{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | An implementation of Lawrence S. Moss' @1\#@ language and Text
-- Register Machine (<http://www.indiana.edu/~iulg/trm/>). 
--
-- This module also includes a slightly higher-level language, @1\#L@,
-- that replaces the forward and backward relative jumps of @1\#@ with
-- labels and goto instructions.
module Language.TRM (
    -- * Basic Text Register Machine
    -- ** Letters and Words
    Letter (..)
  , Word (..)
  , wordToString
    -- ** Registers, Instructions, and Programs
  , Register (..)
  , Instruction (..)
  , instructionToString
  , Program
  , programToString
  , parseProgram
    -- ** Machine Implementation
  , Machine (..)
  , step
  , run
  , phi
    -- * Labels and Gotos
    -- ** Language Definition
  , Label
  , LInstruction (..)
  , LProgram
    -- ** Conversion Between Languages
  , toLabeledProgram
  , fromLabeledProgram
    -- ** Concrete Syntax and Semantics
  , LSymantics (..)
  , LComp (..)
  , freshLabelHere
  , compileL
  , runL
    -- * Examples
    -- * Backwards-Binary Notation
  , encodeBB
  , decodeBB
  , succBB
  , plusBB
) where

import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Writer

import Data.Char (isSpace)
import Data.List hiding ((++))
import Data.Maybe
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vector

import GHC.Exts hiding (Word)

import Prelude hiding ((++))

import Text.Printf

(++) :: Monoid a => a -> a -> a
(++) = mappend

---------------------------------------------------------------------------------
-- Basic 1# parser and machine

-- | Typed representation of the @1#@ letters.
data Letter  = One | Hash deriving (Eq)

-- | A wrapper around a list of 'Letter's with an 'IsString' instance,
-- so that literal strings of @1@s, @#@s, and whitespace can be used
-- instead of lists of 'One's and 'Hash'es. This requires the
-- @-XOverloadedStrings@ flag.
--
-- > loop :: Word
-- > loop = "1### 11####"
newtype Word = W [Letter] deriving (Eq, Monoid)

instance IsString Word where
  fromString []     = W []
  fromString (x:xs) = 
    let (W ls) = fromString xs
    in case x of
         '1'           -> W (One:ls)
         '#'           -> W (Hash:ls)
         c | isSpace c -> W ls 
         _             -> error $ "invalid 1# string: " ++ (x:xs)

-- | Convert a 'Word' back into a 'String'.
wordToString :: Word -> String
wordToString (W [])        = ""
wordToString (W (One :ls)) = '1':wordToString (W ls)
wordToString (W (Hash:ls)) = '#':wordToString (W ls)

instance Show Word where
  show = show . wordToString

-- | Register identifiers.
newtype Register = R Int deriving (Eq, Ord, Show)

-- | Abstract syntax for the primitive @1#@ instructions.
data Instruction = SnocOne  Register
                 | SnocHash Register
                 | Forward  Int
                 | Backward Int
                 | Case     Register
                   deriving (Eq, Show)

-- | Convert an 'Instruction' to concrete syntax.
instructionToString :: Instruction -> String
instructionToString (SnocOne  (R r)) = replicate r '1' ++ "#"
instructionToString (SnocHash (R r)) = replicate r '1' ++ "##"
instructionToString (Forward  i)     = replicate i '1' ++ "###"
instructionToString (Backward i)     = replicate i '1' ++ "####"
instructionToString (Case     (R r)) = replicate r '1' ++ "#####"

-- | A @1#@ program is a 'Vector' of 'Instruction's.
type Program = Vector Instruction

-- | Convert a 'Program' to concrete syntax.
programToString :: Program -> String
programToString = (intercalate " ") . (map instructionToString) . Vector.toList

parseInstruction :: StateT Word Maybe Instruction
parseInstruction = do
  (W ls) <- get
  guard $ not (null ls)
  let (ones  , ls' ) = span (One  ==) ls
      (hashes, ls'') = span (Hash ==) ls'
  put (W ls'')
  case (length ones, length hashes) of
    (r, 1) -> return $ SnocOne  (R r)
    (r, 2) -> return $ SnocHash (R r)
    (i, 3) -> return $ Forward  i
    (i, 4) -> return $ Backward i
    (r, 5) -> return $ Case     (R r)
    _      -> mzero

-- | Parse a 'Word' into a 'Program'; returns 'Nothing' if an invalid
-- instruction is found.
parseProgram :: Word -> Maybe Program
parseProgram w = Vector.fromList <$> evalStateT loop w
  where loop = do (W ls) <- get
                  case ls of
                    [] -> return []
                    _  -> (:) <$> parseInstruction <*> loop

-- | A 'Machine' consists of a 'Program', a program counter, and a
-- 'Map' from registers to the words they contain.
data Machine = M { program :: Program
                 , pc      :: Int 
                 , regs    :: Map Register Word
                 } deriving (Eq, Show)

snocReg :: Register -> Letter -> Map Register Word -> Map Register Word
snocReg r l regs = Map.insertWith (flip (++)) r (W [l]) regs

unsnocReg :: Register -> Map Register Word -> Maybe (Letter, Map Register Word)
unsnocReg r regs = 
  case Map.lookup r regs of
    Nothing            -> mzero
    Just (W [])        -> mzero
    Just (W (One :ls)) -> Just (One , Map.insert r (W ls) regs)
    Just (W (Hash:ls)) -> Just (Hash, Map.insert r (W ls) regs)

-- | Performs the single 'Instruction' indicated by the program
-- counter, if available. Returns 'Left mach' if a step cannot be
-- performed, and 'Right mach' with an updated 'Machine' otherwise.
step :: Machine -> Either Machine Machine
step mach@M { program, pc } 
  | pc < 0 || pc >= Vector.length program = Left mach
step mach@M { program, pc, regs } =
  case program Vector.! pc of
    SnocOne  r -> return $ mach { pc = pc+1, regs = snocReg r One  regs }
    SnocHash r -> return $ mach { pc = pc+1, regs = snocReg r Hash regs }
    Forward  i -> return $ mach { pc = pc+i }
    Backward i -> return $ mach { pc = pc-i }
    Case     r -> 
      case unsnocReg r regs of
        Nothing            -> return $ mach { pc = pc+1 }
        Just (One , regs') -> return $ mach { pc = pc+2, regs = regs' }
        Just (Hash, regs') -> return $ mach { pc = pc+3, regs = regs' }
    
-- | Given a 'Program' and the initial state of the registers, return
-- the final state of the registers.
run :: Program -> Map Register Word -> Map Register Word
run p rs = regs $ final
  where Left final = loop M { program = p, pc = 0, regs = rs }
        loop mach = step mach >>= loop

-- | Wrapper around 'run' that parses the given 'Word' into a
-- 'Program', and then runs it in the given register state. Returns
-- the value in register 1 once the program halts.
--
-- Returns 'Nothing' when either the given 'Word' fails to parse, or
-- if the machine halts abnormally with an invalid program counter or
-- values in registers other than register 1.
phi :: Word -> [(Register, Word)] -> Maybe Word
phi p rs = do p' <- parseProgram p
              let final = run p' $ Map.fromList rs
              checkState final
              Map.lookup (R 1) $! final
  where checkState regs = do
          _ <- Map.lookup (R 1) regs
          let regs' = Map.delete (R 1) regs
          guard $ all (W [] ==) (Map.elems regs')

---------------------------------------------------------------------------------
-- 1#L: Labels and Gotos instead of Forward and Backward

-- | Label representation.
type Label = Int

-- | Abstract syntax for a variant of @1\#@, @1\#L@ with labels and
-- gotos instead of forward and backward jumps.
data LInstruction = LSnocOne  Register
                  | LSnocHash Register
                  | LCase     Register
                  | LGoto     Label
                  | LLabel    Label
                    deriving (Eq, Show)

-- | A @1\#L@ program is a 'Vector' of 'LInstruction's.
type LProgram = Vector LInstruction

exposeLabels :: Program -> Map Int Label
exposeLabels p = Vector.ifoldl' exposeLabel Map.empty p
  where end = Vector.length p
        fresh labs = Map.size labs
        exposeLabel :: Map Int Label
                    -> Int
                    -> Instruction 
                    -> Map Int Label
        exposeLabel labs pos (Forward rel)  
          | pos + rel <= end && pos + rel >= 0
          = Map.insertWith (\_ lab -> lab) (pos+rel) (fresh labs) labs
        exposeLabel labs pos (Backward rel) 
          | pos - rel <= end && pos - rel >= 0
          = Map.insertWith (\_ lab -> lab) (pos-rel) (fresh labs) labs
        exposeLabel _ _ (Forward rel)  = error "forward jump out of range"
        exposeLabel _ _ (Backward rel) = error "backward jump out of range"
        exposeLabel labs _ _ = labs

-- | Convert a @1\#@ 'Program' into a semantically-equivalent @1\#L@
-- 'LProgram'. May fail with an error if the original 'Program' is
-- /non-tidy/, that is it contains forward or backward jumps to
-- instructions outside of the program.
toLabeledProgram :: Program -> LProgram
toLabeledProgram p = Vector.concat (insertLabels 0)
  where labels = exposeLabels p
        p' = Vector.imap substLabel p
        substLabel _   (SnocOne   r) = LSnocOne  r
        substLabel _   (SnocHash  r) = LSnocHash r
        substLabel _   (Case      r) = LCase     r
        substLabel pos (Forward rel) =
            case Map.lookup (pos+rel) labels of
              Just label -> LGoto label
              Nothing -> error "couldn't find label for position"
        substLabel pos (Backward rel) =
            case Map.lookup (pos-rel) labels of
              Just label -> LGoto label
              Nothing -> error "couldn't find label for position"
        insertLabels i | i == Vector.length p' = 
          case Map.lookup i labels of
            Nothing -> []
            Just label -> [Vector.singleton $ LLabel label]
        insertLabels i = 
          case Map.lookup i labels of
            Nothing -> (Vector.singleton $ p' Vector.! i) : insertLabels (i+1)
            Just label -> (Vector.fromList $ [LLabel label, p' Vector.! i])
                        : insertLabels (i+1)

exposePositions :: LProgram -> Map Label Int
exposePositions lp = fst $ Vector.ifoldl' exposePosition (Map.empty, 0) lp
  where exposePosition (poss, seen) pos (LLabel label) =
          ( Map.insertWith (error $ "duplicate label " ++ show label) 
                           label (pos-seen) poss
          , seen+1 )
        exposePosition p _ _ = p


-- | Convert a @1\#L@ 'LProgram' into a semantically-equivalent @1\#@
-- 'Program'. May fail with an error if the 'LProgram' contains
-- duplicate labels, jumps to undefined labels. An error will also
-- occur if the 'LProgram' contains a goto that would translate into a
-- jump of 0 instructions, as this is impossible to express in @1\#@.
fromLabeledProgram :: LProgram -> Program
fromLabeledProgram lp = insertJumps . removeLabels $ lp
  where removeLabels = Vector.filter (not . isLabel)
        isLabel (LLabel _) = True
        isLabel _          = False
        poss = exposePositions lp
        insertJumps = Vector.imap insertJump 
        insertJump _   (LSnocOne  r) = SnocOne  r
        insertJump _   (LSnocHash r) = SnocHash r
        insertJump _   (LCase     r) = Case     r
        insertJump pos (LGoto label) = 
          case Map.lookup label poss of
            Nothing -> error $ "unbound label " ++ show label
            Just dest | dest > pos -> Forward  (dest - pos)
                      | dest < pos -> Backward (pos - dest)
                      | otherwise -> error "can't jump to self"
        insertJump _ (LLabel _) = error "labels shouldn't exist here"

-- | Concrete syntax for @1\#L@, indexed by backend representation in
-- the typed tagless style
-- (<http://okmij.org/ftp/tagless-final/index.html>).
class LSymantics repr where
  -- | Append a @1@ to the end of the given 'Register'.
  snocOne    :: Register -> repr ()
  -- | Append a @#@ to the end of the given 'Register'.
  snocHash   :: Register -> repr ()
  -- | Return a fresh 'Label' to be used in a call to 'label' or 'goto'.
  freshLabel :: repr Label
  -- | Place a 'Label' at the given point in the program. Note that a
  -- particular 'Label' may be used only once per program.
  label      :: Label -> repr ()
  -- | Unconditional jump to the given 'Label'.
  goto       :: Label -> repr ()
  -- | Case analysis; pops a 'Letter' from the front of the
  -- scrutinized 'Register', if non-empty. Note that in the default
  -- backend, new labels are automatically created and placed for the
  -- branches of the 'cond'.
  cond       :: Register -- ^ The 'Register' to scrutinize.
             -> repr ()  -- ^ Run if the 'Register' is empty.
             -> repr ()  -- ^ Run if the front of the 'Register' is a @1@.
             -> repr ()  -- ^ Run if the front of the 'Register' is a @#@.
             -> repr ()

-- | The default backend for 'LSymantics'.
newtype LComp a = LC { unLC :: StateT (Int, Set Label) (Writer LProgram) a }
    deriving ( Functor, Applicative, Monad, MonadFix
             , MonadState (Int, Set Label), MonadWriter LProgram)

instance LSymantics LComp where
  snocOne    = tell . Vector.singleton . LSnocOne
  snocHash   = tell . Vector.singleton . LSnocHash
  freshLabel = do (l, ls) <- get
                  put (l+1, ls)
                  return l
  label l    = do (l', ls) <- get
                  case Set.member l ls of
                    True  -> error $ printf "duplicate label %s" l
                    False -> do put (l', Set.insert l ls)
                                tell . Vector.singleton $ LLabel l
  goto       = tell . Vector.singleton . LGoto
  cond r bEmpty bOne bHash = do 
    [lEmpty, lOne, lHash] <- replicateM 3 freshLabel
    tell . Vector.singleton $ LCase r
    goto  lEmpty >> goto lOne >> goto lHash
    label lEmpty >> bEmpty
    label lOne   >> bOne
    label lHash  >> bHash

-- | Convenience function to create a fresh label and place it at the
-- current position.
freshLabelHere :: (Monad repr, LSymantics repr) => repr Label
freshLabelHere = do l <- freshLabel ; label l ; return l

-- | Compiles an 'LComp' program into an 'LProgram'.
compileL :: LComp () -> LProgram
compileL prog = execWriter (evalStateT (unLC prog) (0, Set.empty))

-- | Given an 'LComp' program and an initial register state, and then
-- runs it in the given register state. May return 'Nothing' if the
-- program does not halt cleanly, as with 'run'.
runL :: LComp () -> [(Register, Word)] -> Maybe Word
runL p rs = 
  Map.lookup (R 1) $ (run . fromLabeledProgram . compileL $ p) (Map.fromList rs)

---------------------------------------------------------------------------------
-- Backwards binary encoding

-- | Encodes an 'Integral' type into a 'Word' of backwards-binary
-- digits using @1@s and @#@s for @1@s and @0@s, respectively. Note
-- that the representation of zero is a single @#@ rather than the
-- empty 'Word'.
encodeBB :: Integral a => a -> Word
encodeBB x | toInteger x == 0 = W [Hash]
           | otherwise        = W (enc (toInteger x))
  where enc 0          = []
        enc n | odd n  = One  : (enc $ n `div` 2)
              | even n = Hash : (enc $ n `div` 2)
        enc _          = error "encodeBB only accepts non-negative integers"

-- | Decodes a 'Word' containing backwards-binary digits into a 'Num'
-- type. Fails with an error if the 'Word' is empty.
decodeBB :: Num a => Word -> a
decodeBB (W []) = error "Backwards-binary words cannot be empty"
decodeBB (W xs) = fromInteger $ dec xs
  where dec []        = 0
        dec (Hash:xs) = 2 * dec xs
        dec (One:xs)  = 1 + (2 * dec xs)

---------------------------------------------------------------------------------
-- Examples

-- | Yields the successor of the backwards-binary number in register 1.
--
-- > *Language.TRM> decodeBB <$> phi succBB [(R 1, encodeBB 0)]
-- > Just 1
-- > *Language.TRM> decodeBB <$> phi succBB [(R 1, encodeBB 119)]
-- > Just 120
succBB :: Word
succBB = "1##### 1111111111 111### 1111111111### 11# 1##### 111111### 111### 11## 1111#### 11# 111111#### 1111### 11## 1111111111 111#### 11# 11##### 111111### 111### 1## 1111#### 1# 111111####"

-- | Yields the sum of two backwards-binary numbers in registers 1 and 2.
--
-- > *Language.TRM> decodeBB <$> phi plusBB [(R 1, encodeBB 2), (R 2, encodeBB 3)]
-- > Just 5
-- > *Language.TRM> decodeBB <$> phi plusBB [(R 1, encodeBB 100), (R 2, encodeBB 20)]
-- > Just 120
plusBB :: Word
plusBB = "1##### 111### 111111### 111111111### 11##### 1111111111 11111111111 11111111111 111### 1111111111 11111111111 11111### 1111111111 11111111111 111111### 11##### 1111111111 11111111111 11### 1111111111 11111111111 1111111### 1111111111 11111111111### 11##### 1111111111 11111111111### 1111111111 11111111### 1111111111 111111111### 1##### 111### 111111### 111111111### 11##### 1111111111 1### 1111111111 111111### 111111111### 11##### 1111111111 111### 1111111111### 1111111111 1### 11##### 111### 11111111### 1### 111# 1111111111 11111111111 11111111111 1#### 111## 1111111111 11111111111 11111111111 111#### 111# 1111111111 11111111111#### 111## 1111111111 11111111111 11#### 1### 111##### 111111### 111### 1## 1111#### 1# 111111####"

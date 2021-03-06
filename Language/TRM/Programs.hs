{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.TRM.Programs (
    -- * 1# Examples
    succBB'
  , plusBB'
  , compare'
    -- * 1#L Programs
  , clear
  , move
  , copy
  , compare
  , succBB
  , addBB
  , multBB
  , exptBB
  , double
  , unaryToBB
  , bbToUnary
) where

import Language.TRM.Base

import Control.Monad

import Prelude hiding (compare)

--------------------------------------------------------------------------------
-- 1# Examples from http://www.indiana.edu/~iulg/trm/arith.shtml

-- | Yields the successor of the backwards-binary number in register 1.
--
-- > *Language.TRM> decodeBB <$> phi succBB [(1, encodeBB 0)]
-- > Just 1
-- > *Language.TRM> decodeBB <$> phi succBB [(1, encodeBB 119)]
-- > Just 120
succBB' :: Word
succBB' = "1##### 1111111111 111### 1111111111### 11# 1##### 111111### 111### 11## 1111#### 11# 111111#### 1111### 11## 1111111111 111#### 11# 11##### 111111### 111### 1## 1111#### 1# 111111####"

-- | Yields the sum of two backwards-binary numbers in registers 1 and 2.
--
-- > *Language.TRM> decodeBB <$> phi plusBB [(1, encodeBB 2), (2, encodeBB 3)]
-- > Just 5
-- > *Language.TRM> decodeBB <$> phi plusBB [(1, encodeBB 100), (2, encodeBB 20)]
-- > Just 120
plusBB' :: Word
plusBB' = "1##### 111### 111111### 111111111### 11##### 1111111111 11111111111 11111111111 111### 1111111111 11111111111 11111### 1111111111 11111111111 111111### 11##### 1111111111 11111111111 11### 1111111111 11111111111 1111111### 1111111111 11111111111### 11##### 1111111111 11111111111### 1111111111 11111111### 1111111111 111111111### 1##### 111### 111111### 111111111### 11##### 1111111111 1### 1111111111 111111### 111111111### 11##### 1111111111 111### 1111111111### 1111111111 1### 11##### 111### 11111111### 1### 111# 1111111111 11111111111 11111111111 1#### 111## 1111111111 11111111111 11111111111 111#### 111# 1111111111 11111111111#### 111## 1111111111 11111111111 11#### 1### 111##### 111111### 111### 1## 1111#### 1# 111111####"

compare' :: Word
compare' = "1##### 111111### 111111111### 11##### 1111111111 1### 1111111111### 111111#### 11##### 1111111111 11111### 111111### 11111### 11##### 111### 1111111111 111#### 1### 1##### 111### 11#### 111#### 11##### 1111### 11#### 111#### 1#"

clear :: Register -- ^ 'Register' to clear.
      -> LComp ()
clear r = 
  do_ $ \continue break -> 
      cond r break continue continue
                   
move :: Register -- ^ Source 'Register'.
     -> Register -- ^ Destination 'Register'.
     -> LComp ()
move src dest = 
  do_ $ \continue break -> 
    cond src 
         break
         (snocOne  dest >> continue)
         (snocHash dest >> continue)

copy :: Register -- ^ Source 'Register'.
     -> Register -- ^ Destination 'Register'.
     -> LComp ()
copy src dest = do
  tmp <- freshReg
  do_ $ \continue break ->
    cond src
         break
         (do snocOne  dest ; snocOne  tmp ; continue)
         (do snocHash dest ; snocHash tmp ; continue)
  move tmp src

-- | Compares the contents of the given registers for equality,
-- leaving a @1@ in the first register if they are, or nothing
-- otherwise. The contents of both registers are destroyed in the
-- process.
compare :: Register -> Register -> LComp ()
compare r1 r2 = do
  [true, false, clear1, clear2] <- replicateM 4 freshLabel

  do_ $ \continue _ ->
    cond r1
         (cond r2 (goto true)   (goto clear2) (goto clear2))
         (cond r2 (goto clear1) continue      (goto clear1))
         (cond r2 (goto clear1) (goto clear1) continue     )
  
  label clear1
  clear r1
 
  label clear2
  clear r2
  goto false

  label true
  snocOne r1
  label false

succBB :: Register -- ^ 'Register' to increment.
       -> LComp ()
succBB r = do
  tmp <- freshReg
  do_ $ \continue break ->
    cond r
         (do snocOne  tmp ; break)
         (do snocHash tmp ; continue)
         (do snocOne  tmp ; move r tmp ; break)
  move tmp r

-- | Add the two argument registers using primitive
-- recursion, leaving the result in the first.
--
-- > *Language.TRM.Programs> decodeBB <$> runL (addBB 1 2) [(1, encodeBB 100), (2, encodeBB 20)]
-- > Just 120
addBB :: Register -> Register -> LComp ()
addBB r1 r2 = do
  [r3, r4, r5, r6] <- replicateM 4 freshReg
  recCase <- freshLabel
  -- initialize
  snocHash r3 >> move r1 r4
  do_ $ \continue break -> do
    -- test
    copy r2 r5
    copy r3 r6
    compare r5 r6
    cond r5 (goto recCase) break (goto recCase)
    -- recursive case
    label recCase
    succBB r4
    succBB r3
    continue
  clear r1 >> clear r2 >> clear r3
  move r4 r1

multBB :: Register -> Register -> LComp ()
multBB r1 r2 = do
  [r3, r4, r5, r6] <- replicateM 4 freshReg
  recCase <- freshLabel
  -- initialize
  snocHash r3 >> snocHash r4
  do_ $ \continue break -> do
    -- test
    copy r2 r5
    copy r3 r6
    compare r5 r6
    cond r5 (goto recCase) break (goto recCase)
    -- recursive case
    label recCase
    copy r1 r5
    move r4 r6
    addBB r5 r6
    move r5 r4
    succBB r3
    continue
  clear r1 >> clear r2 >> clear r3
  move r4 r1    

exptBB :: Register -> Register -> LComp ()
exptBB r1 r2 = do
  [r3, r4, r5, r6] <- replicateM 4 freshReg
  recCase <- freshLabel
  -- initialize
  snocHash r3 >> snocOne r4
  do_ $ \continue break -> do
    -- test
    copy r2 r5 
    copy r3 r6 
    compare r5 r6
    cond r5 (goto recCase) break (goto recCase)
    -- recursive case
    label recCase
    copy r1 r5 
    move r4 r6
    multBB r5 r6
    move r5 r4
    succBB r3
    continue
  clear r1 >> clear r2 >> clear r3
  move r4 r1

unaryToBB :: Register -> Register -> LComp ()
unaryToBB src acc = do
  -- initialize with # in acc
  snocOne acc
  do_ $ \continue break -> do
    -- run succBB on acc as long as there are 1s in src
    cond src
         break
         (do succBB acc ; continue)
         break -- shouldn't be a # in src
  -- finally, move acc to src
  move acc src

double :: Register -> Register -> LComp ()
double r1 r2 = do copy r1 r2 ; move r2 r1

bbToUnary :: Register -> LComp ()
bbToUnary src = do
  [acc, pos, t1] <- replicateM 3 freshReg
  -- initialize with 1 in acc, since unary rep. of 0 is 1
  snocOne acc
  -- initialize position with 1 for least-significant bit
  snocOne pos
  do_ $ \continue break -> do
    cond src
         break
         -- if 1, copy pos to acc, double pos, continue
         (do copy pos acc ; double pos t1 ; continue)
         -- if #, double pos, continue
         (do double pos t1 ; continue)
  clear pos
  move acc src


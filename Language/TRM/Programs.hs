module Language.TRM.Programs (
    -- * 1# Examples
    succBB'
  , plusBB'
    -- * 1#L Programs
  , clear
  , move
  , copy
  , compare
  , succBB
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
     -> Register -- ^ Temporary 'Register'.
     -> LComp ()
copy src dest tmp = do
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

  top <- freshLabelHere

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
       -> Register -- ^ Temporary 'Register', assumed to be empty.
       -> LComp ()
succBB r tmp = do
  do_ $ \continue break ->
    cond r
         (do snocOne  tmp ; break)
         (do snocHash tmp ; continue)
         (do snocOne  tmp ; move r tmp ; break)
  move tmp r

-- | Add the first two registers using primitive recursion
addBB r1 r2 r3 r4 r5 r6 r7 = do
  recCase <- freshLabel
  -- initialize
  snocHash r3 >> move r1 r4
  do_ $ \continue break -> do
    -- test
    copy r2 r5 r6
    copy r3 r6 r7
    compare r5 r6
    cond r5 (goto recCase) break (goto recCase)
    -- recursive case
    label recCase
    succBB r4 r5
    succBB r3 r5
    continue
  clear r1 >> clear r2 >> clear r3
  move r4 r1
    

  

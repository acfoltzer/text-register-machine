{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

import Language.TRM

import Control.Applicative
import Data.Monoid

import Test.QuickCheck hiding (label)
import Test.QuickCheck.All

import Prelude hiding (compare)

instance Arbitrary Letter where
  arbitrary = do
    b <- arbitrary :: Gen Bool
    case b of
      True  -> return One
      False -> return Hash

deriving instance Arbitrary Word

instance Arbitrary Register where
  arbitrary = fromIntegral <$> (arbitrary :: Gen (Positive Integer))

prop_succBB_ :: NonNegative Integer -> Bool
prop_succBB_ x = case phi succBB' [(1, encodeBB x)] of
                   Just x' -> decodeBB x' == x + 1
                   _ -> False

prop_plusBB_ :: NonNegative Integer -> NonNegative Integer -> Bool
prop_plusBB_ x y = case phi plusBB' [(1, encodeBB x), (2, encodeBB y)] of
                     Just z -> decodeBB z == x + y
                     _ -> False

prop_compare_ :: Word -> Word -> Bool
prop_compare_ x y = case phi compare' [(1, x), (2, y)] of
                      Just "1" -> x == y
                      Just ""  -> x /= y
                      _ -> False

prop_clear :: Register -> Word -> Bool
prop_clear r x = case lookup r $ runL' (clear r) [(r, x)] of
                   Just "" -> True
                   _       -> False

prop_move :: Register -> Register -> Word -> Word -> Property
prop_move src dest x y = src /= dest ==>
    case (lookup src rs, lookup dest rs) of
      (Just "", Just z) -> z == y `mappend` x
      _ -> False
  where rs = runL' (move src dest) [(src, x), (dest, y)]

prop_copy :: Register -> Register -> Word -> Word -> Property
prop_copy src dest x y = src /= dest ==>
    case (lookup src rs, lookup dest rs) of
      (Just x', Just z) -> x == x' && z == y `mappend` x
      _ -> False
  where rs = runL' (copy src dest) [(src, x), (dest, y)]

prop_compare :: Register -> Register -> Word -> Word -> Property
prop_compare r1 r2 x y = r1 /= r2 ==>
  case lookup r1 $ runL' (compare r1 r2) [(r1, x), (r2, y)] of
    Just "1" -> x == y
    Just ""  -> x /= y
    _ -> False

prop_succBB :: Register -> NonNegative Integer -> Bool
prop_succBB r x =
  case lookup r $ runL' (succBB r) [(r, encodeBB x)] of
    Just x' -> decodeBB x' == x + 1
    _ -> False

prop_addBB :: Register -> Register 
           -> NonNegative Integer -> NonNegative Integer 
           -> Property
prop_addBB r1 r2 x y = r1 /= r2 ==>
  case lookup r1 $ runL' (addBB r1 r2) [(r1, encodeBB x), (r2, encodeBB y)] of
    Just z -> decodeBB z == x + y
    _ -> False

prop_multBB :: Register -> Register 
            -> NonNegative Integer -> NonNegative Integer 
            -> Property
prop_multBB r1 r2 x y = r1 /= r2 ==>
  case lookup r1 $ runL' (multBB r1 r2) [(r1, encodeBB x), (r2, encodeBB y)] of
    Just z -> decodeBB z == x * y
    _ -> False

prop_exptBB :: Register -> Register 
            -> NonNegative Integer -> NonNegative Integer 
            -> Property
prop_exptBB r1 r2 x y = r1 /= r2 ==>
  case lookup r1 $ runL' (exptBB r1 r2) [(r1, encodeBB x), (r2, encodeBB y)] of
    Just z -> decodeBB z == x ^ y
    _ -> False

runTests = $quickCheckAll
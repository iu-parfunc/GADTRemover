#!/usr/bin/env stack
{- stack 
    --no-system-ghc
    --resolver nightly-2016-06-19
    --install-ghc 
    runghc
 -}

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module GhostBuster where

import GHC.TypeLits
import Unsafe.Coerce

newtype Vec a (n :: Nat) = Vec { unVec :: [a] }
 deriving Show

-- "Almost" Vec GADT, but the inside is a Vec
-- (so only the top-level is unfolded.)
data Vec' a (n :: Nat) where
    VNil'  :: Vec' a 0
    VCons' :: a -> Vec a n -> Vec' a (n + 1)

upVec :: Vec a n -> Vec' a n
upVec (Vec [])     = unsafeCoerce VNil'
upVec (Vec (x:xs)) = unsafeCoerce (VCons' x (Vec xs))

pattern VNil :: () => (n ~ 0) => Vec a n
pattern VNil <- (upVec -> VNil') where
    VNil = Vec []

pattern VCons :: () => ((n + 1) ~ n') => a -> Vec a n -> Vec a n'
pattern VCons x xs <- (upVec -> VCons' x xs) where
    VCons x (Vec xs) = Vec (x : xs)

headVec :: Vec a (n + 1) -> a
headVec (VCons x _) = x

mapVec :: (a -> b) -> Vec a n -> Vec b n
mapVec f VNil = (VNil :: Vec a 0)
mapVec f (VCons x xs) = VCons (f x) (mapVec f xs)

main = do
 let v :: Vec Int 5 -- unsafe/Trusted
     v = Vec [1..5]

     v2 :: Vec Int 2 -- Checked
     v2 = VCons 1 (VCons 2 VNil)

 print v
 print v2
 print $ mapVec (+10) v2

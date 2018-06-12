{-# OPTIONS --type-in-type --without-K #-}

open import Cryptography.agda_lib.Equiv

module Cryptography.agda_lib.List where

  data List (a : Set) : Set where
    []  : List a
    _::_ : a -> List a -> List a 

  {-# COMPILED_DATA List [] [] (:) #-}
  {-# BUILTIN LIST List #-}
  {-# BUILTIN NIL [] #-}
  {-# BUILTIN CONS _::_ #-}

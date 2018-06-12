
{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Cryptography.agda_lib.Utils
open import Cryptography.agda_lib.Nat
open import Cryptography.agda_lib.Equiv

module Cryptography.agda_lib.Char where

 postulate {- Agda Primitive -}
   Char : Set
  
 {-# BUILTIN CHAR Char #-}
 {-# COMPILED_TYPE Char Char #-}
    
 module Char where

  private
   primitive
    primCharToNat    : Char → Nat
    primCharEquality : Char → Char → Bool
  
  toNat : Char → Nat
  toNat = primCharToNat
  
  equal : Char -> Char -> Bool
  equal = primCharEquality

  equals : (c d : Char) → (c ≡ d) ⊎ (c ≡ d → Void)
  equals c d with equal c d
  ... | true = Inl CharEq where
    postulate
      CharEq : c ≡ d 
  ... | false = Inr (\ _ -> CharsNeq) where
    postulate
      CharsNeq : Void

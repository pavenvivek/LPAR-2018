{- Higher inductive type specification for one-time pad using Dan Licata's method -}

{-# OPTIONS --type-in-type --without-K #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import OTP.agda_lib.Bin
open import OTP.agda_lib.Equiv
open import OTP.agda_lib.Vector

module OTP.Crypto.space_otp where

module OneTimePad where
  private
    data OTP* (n : Nat) : Set where
      message* : OTP* n
      cipher* : OTP* n

  OTP : Nat → Set
  OTP n = OTP* n

  message : {n : Nat} → OTP n
  message = message*

  cipher : {n : Nat} → OTP n
  cipher = cipher*

  postulate
    otp-encrypt : {n : Nat} → (key : Vec Bit n) → message {n} ≡ cipher {n}

  otp-recursion : {n : Nat} → (C : Set) → (c-msg : C) → (c-cipher : C) →
                  (c-encrypt : (key : Vec Bit n) → c-msg ≡ c-cipher) →
                  OTP n → C
  otp-recursion C c-msg c-crypto c-encrypt message* = c-msg
  otp-recursion C c-msg c-crypto c-encrypt cipher* = c-crypto

  postulate
    β-otp-recursion : {n : Nat} → (C : Set) → (c-msg : C) → (c-cipher : C) →
                      (c-encrypt : (key : Vec Bit n) → c-msg ≡ c-cipher) →
                      {key : Vec Bit n} → ap (otp-recursion C c-msg c-cipher c-encrypt) (otp-encrypt key) ≡ (c-encrypt key)

  otp-induction : {n : Nat} → (C : OTP n → Set) → (c-msg : C (message)) → (c-cipher : C (cipher)) →
                  (c-encrypt : (key : Vec Bit n) → transport C (otp-encrypt key) c-msg ≡ c-cipher) →
                  (x : OTP n) → C x
  otp-induction C c-data c-crypto c-encrypt message* = c-data
  otp-induction C c-data c-crypto c-encrypt cipher* = c-crypto

  postulate
    β-otp-induction : {n : Nat} → (C : OTP n → Set) → (c-msg : C (message)) → (c-cipher : C (cipher)) →
                      (c-encrypt : (key : Vec Bit n) → transport C (otp-encrypt key) c-msg ≡ c-cipher) →
                      {key : Vec Bit n} → apd (otp-induction C c-msg c-cipher c-encrypt) (otp-encrypt key) ≡ (c-encrypt key)

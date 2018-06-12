{- Interpretation of OTP concrete implementation using its higher inductive type -}

{-# OPTIONS --type-in-type --without-K #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import OTP.agda_lib.Bin
open import OTP.agda_lib.Equiv
open import OTP.agda_lib.Vector
open import OTP.Crypto.space_otp
open import OTP.Crypto.One_Time_Pad


module OTP.Crypto.OTP_interp where

open OneTimePad public

I-OTP : {n : Nat} → OTP n → Set
I-OTP {n} bits = otp-recursion Set (Vec Bit n) (Vec Bit n) (λ key → ua (OTP-equiv key)) bits

I-OTP-path : {n : Nat} → (key : Vec Bit n) → ap I-OTP (otp-encrypt {n} key) ≡ ua (OTP-equiv key)
I-OTP-path {n} key = β-otp-recursion Set (Vec Bit n) (Vec Bit n) (λ k → ua (OTP-equiv k))


interp#1 : {n : Nat} → {a b : OTP n} → (p : a ≡ b) → (I-OTP a) ≃ (I-OTP b)
interp#1 p = coe-biject (ap I-OTP p) 

interp#2 : {n : Nat} → {a b : OTP n} → (p : a ≡ b) → (I-OTP a) → (I-OTP b)
interp#2 {n} {a} {b} p = coe' (ap I-OTP p) 

pf : (interp#2 (otp-encrypt (1b :: (0b :: []))) (1b :: (1b :: []))) ≡ (0b :: (1b :: []))
pf = begin
       interp#2 (otp-encrypt (1b :: (0b :: []))) (1b :: (1b :: [])) ≡⟨ refl ⟩
       coe' (ap I-OTP (otp-encrypt (1b :: (0b :: [])))) (1b :: (1b :: [])) ≡⟨ ap (λ x → coe' x (1b :: (1b :: []))) (I-OTP-path (1b :: (0b :: []))) ⟩
       coe' (ua (OTP-equiv (1b :: (0b :: [])))) (1b :: (1b :: [])) ≡⟨ refl ⟩
       fst (coe-biject (ua (OTP-equiv (1b :: (0b :: []))))) (1b :: (1b :: [])) ≡⟨ ap (λ x → fst x (1b :: (1b :: []))) (ua-cbj (OTP-equiv (1b :: (0b :: [])))) ⟩
       fst (OTP-equiv (1b :: (0b :: []))) (1b :: (1b :: [])) ≡⟨ refl ⟩
       (0b :: (1b :: [])) ∎


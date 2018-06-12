{- Concrete implementation of one-time pad in the universe -}

{-# OPTIONS --type-in-type --without-K #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import OTP.agda_lib.Bin
open import OTP.agda_lib.Equiv
open import OTP.agda_lib.Vector
open import OTP.Crypto.space_otp
open import Function renaming (_∘_ to _○_)


module OTP.Crypto.One_Time_Pad where

open OneTimePad public

_xor_ : Bit → Bit → Bit
0b xor 0b = 0b
0b xor 1b = 1b
1b xor 0b = 1b
1b xor 1b = 0b

_xorBits_ : {n : Nat} → Vec Bit n → Vec Bit n → Vec Bit n
[] xorBits [] = []
(x :: xs) xorBits (y :: ys) = (x xor y) :: (xs xorBits ys)

OTP-encrypt : {n : Nat} → (key : Vec Bit n) → (message : Vec Bit n) → Vec Bit n
OTP-encrypt {n} key message = message xorBits key

0b-vec : (n : Nat) → Vec Bit n
0b-vec 0 = []
0b-vec (suc n) = 0b :: (0b-vec n)

xor-sym : (x : Bit) → x xor x ≡ 0b
xor-sym = indBit (λ x → x xor x ≡ 0b) refl refl

xor-id : (x : Bit) → x xor 0b ≡ x
xor-id = indBit (λ x → x xor 0b ≡ x) refl refl

xor-assoc : (x : Bit) → (y : Bit) → (z : Bit) → (x xor y) xor z ≡ (x xor (y xor z))
xor-assoc = indBit (λ x → (y z : Bit) → (x xor y) xor z ≡ (x xor (y xor z)))
                      (indBit (λ y → (z : Bit) → (0b xor y) xor z ≡ (0b xor (y xor z)))
                              (indBit (λ z → (0b xor 0b) xor z ≡ (0b xor (0b xor z)))
                                      refl refl)
                              (indBit (λ z → (0b xor 1b) xor z ≡ (0b xor (1b xor z)))
                                      refl refl))
                      (indBit (λ y → (z : Bit) → (1b xor y) xor z ≡ (1b xor (y xor z)))
                              (indBit (λ z → (1b xor 0b) xor z ≡ (1b xor (0b xor z)))
                                      refl refl)
                              (indBit (λ z → (1b xor 1b) xor z ≡ (1b xor (1b xor z)))
                                      refl refl))

xor-sym-pf : {n : Nat} → (x : Vec Bit n) → x xorBits x ≡ (0b-vec n)
xor-sym-pf = (indVec (λ {n} x → x xorBits x ≡ (0b-vec n))
                      refl
                      (λ {n} x xs pf → begin
                                          (x :: xs) xorBits (x :: xs) ≡⟨ refl ⟩
                                          (x xor x) :: (xs xorBits xs) ≡⟨ ap (λ pxs → (x xor x) :: pxs) pf ⟩
                                          (x xor x) :: (0b-vec n) ≡⟨ ap (λ px → px :: (0b-vec n)) (xor-sym x) ⟩
                                          0b :: (0b-vec n) ≡⟨ refl ⟩
                                          0b-vec (suc n) ∎))

xor-id-pf : {n : Nat} → (x : Vec Bit n) → x xorBits (0b-vec n) ≡ x
xor-id-pf = indVec (λ {n} x → x xorBits (0b-vec n) ≡ x)
                    refl
                    λ {n} x xs pf → begin
                                       (x :: xs) xorBits 0b-vec (suc n) ≡⟨ refl ⟩
                                       (x :: xs) xorBits (0b :: (0b-vec n)) ≡⟨ refl ⟩
                                       (x xor 0b) :: (xs xorBits (0b-vec n)) ≡⟨ ap (λ pxs → (x xor 0b) :: pxs) pf ⟩
                                       (x xor 0b) :: xs ≡⟨ ap (λ px → px :: xs) (xor-id x) ⟩
                                       (x :: xs) ∎ 

xor-assoc-pf : {n : Nat} → (x : Vec Bit n) → (y : Vec Bit n) → (z : Vec Bit n) → (x xorBits y) xorBits z ≡ (x xorBits (y xorBits z))
xor-assoc-pf {n} [] [] [] = refl
xor-assoc-pf {n} (x :: xs) (y :: ys) (z :: zs) = begin
                                                     ((x :: xs) xorBits (y :: ys)) xorBits (z :: zs) ≡⟨ refl ⟩
                                                     ((x xor y) :: (xs xorBits ys)) xorBits (z :: zs) ≡⟨ refl ⟩
                                                     ((x xor y) xor z) :: ((xs xorBits ys) xorBits zs) ≡⟨ ap (λ p → p :: ((xs xorBits ys) xorBits zs)) (xor-assoc x y z) ⟩
                                                     (x xor (y xor z)) :: ((xs xorBits ys) xorBits zs) ≡⟨ ap (λ p → (x xor (y xor z)) :: p) (xor-assoc-pf xs ys zs) ⟩
                                                     (x xor (y xor z)) :: (xs xorBits (ys xorBits zs)) ≡⟨ refl ⟩
                                                     (x :: xs) xorBits ((y xor z) :: (ys xorBits zs)) ≡⟨ refl ⟩
                                                     (x :: xs) xorBits ((y :: ys) xorBits (z :: zs)) ∎

α-OTP : {n : Nat} → (key : Vec Bit n) → (message : Vec Bit n) → (OTP-encrypt {n} key (OTP-encrypt {n} key message)) ≡ message
α-OTP {n} key message = begin
                        (OTP-encrypt key (OTP-encrypt key message)) ≡⟨ refl ⟩
                        (OTP-encrypt key (message xorBits key)) ≡⟨ refl ⟩
                        ((message xorBits key) xorBits key) ≡⟨ xor-assoc-pf message key key ⟩
                        (message xorBits (key xorBits key)) ≡⟨ ap (λ x → message xorBits x) (xor-sym-pf {n} key)  ⟩
                        (message xorBits (0b-vec n)) ≡⟨ xor-id-pf {n} message ⟩
                        message ∎

f∘g : {n : Nat} → (key : Vec Bit n) → Vec Bit n → Vec Bit n
f∘g {n} key = (OTP-encrypt key) ○ (OTP-encrypt key)

α : {n : Nat} → (key : Vec Bit n) → (f∘g key) ∼ id
α {n} key = α-OTP key 

OTP-equiv : {n : Nat} → (key : Vec Bit n) → Vec Bit n ≃ Vec Bit n
OTP-equiv key = ((OTP-encrypt key) , equiv₁ (mkqinv (OTP-encrypt key) (α key) (α key)))

OTP-path : {n : Nat} → (key : Vec Bit n) → Vec Bit n ≡ Vec Bit n
OTP-path {n} key with univalence 
... | (_ , eq) = isequiv.g eq (OTP-equiv {n} key)


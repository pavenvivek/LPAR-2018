
module OTP.agda_lib.Bin where

data Bit : Set where
  1b : Bit
  0b : Bit

recBit : (C : Set) → (c0 c1 : C) → Bit → C
recBit C c0 c1 0b = c0
recBit C c0 c1 1b = c1

indBit : (C : Bit → Set) → (c0 : C(0b)) → (c1 : C(1b)) → (x : Bit) → C(x)
indBit C c0 c1 0b = c0
indBit C c0 c1 1b = c1

Add LoadPath "/home/paven/Type_Theory/Coq/HoTT/Crypto".

Require Import PathUtils.
Require Import Vector.

Module Export OTP.

Inductive Bit : Type :=
  | oneb : Bit
  | zerob : Bit.

Private Inductive OTP (n : nat) : Type :=
  | msg : OTP n
  | cph : OTP n.
  Arguments msg [n].
  Arguments cph [n].

Axiom otpEncrypt : forall {n : nat}, vec Bit n -> @msg n ≡ @cph n.

Definition OTP_rec {n : nat} 
  (C : Type)
  (cmsg : C) 
  (ccph : C) 
  (cEncrypt : vec Bit n -> cmsg ≡ ccph)
  : forall x : OTP n, C
  := fun x => (match x return (_ -> C) with
                | msg => fun _ => cmsg
                | cph  => fun _ => ccph
              end) cEncrypt.

Axiom OTP_rec_otpEncrypt : forall {n : nat} 
  (C : Type)
  (cmsg : C) 
  (ccph : C) 
  (cEncrypt : vec Bit n -> cmsg ≡ ccph)
  (key : vec Bit n), 
  ap (OTP_rec C cmsg ccph cEncrypt) (@otpEncrypt n key) ≡ (cEncrypt key).


Definition OTP_ind {n : nat} 
  (C : OTP n -> Type)
  (cmsg : C (msg)) 
  (ccph : C (cph)) 
  (cEncrypt : forall (key : vec Bit n), (@otpEncrypt n key) # cmsg ≡ ccph)
  : forall x : OTP n, C x
  := fun x => (match x return (_ -> C x) with
                | msg => fun _ => cmsg
                | cph  => fun _ => ccph
              end) cEncrypt.


Axiom OTP_ind_otpEncrypt : forall {n : nat} 
  (C : OTP n -> Type)
  (cmsg : C (msg)) 
  (ccph : C (cph)) 
  (cEncrypt : forall (key : vec Bit n), (@otpEncrypt n key) # cmsg ≡ ccph)
  (key : vec Bit n),
  apD (OTP_ind C cmsg ccph cEncrypt) (@otpEncrypt n key) ≡ (cEncrypt key).

End OTP.
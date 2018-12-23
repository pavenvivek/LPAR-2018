Add LoadPath "/home/paven/Type_Theory/Coq/HoTT/Crypto".

Require Import PathUtils.
Require Import Vector.
Require Import OTPSpace.
Require Import OTPImpl.

Definition IOTP {n} (bits : OTP n) : Type
  := OTP_rec Type (vec Bit n) (vec Bit n) (fun key => ua (@OTPequiv n key)) bits.

Definition IOTPPath {n} (key : vec Bit n) : (ap IOTP (@otpEncrypt n key)) ≡ (ua (@OTPequiv n key))
  := (OTP_rec_otpEncrypt Type (vec Bit n) (vec Bit n) (fun k => ua (@OTPequiv n k))) key.

Definition interp1 {n} {a b : OTP n} (p : a ≡ b) : (equiv (IOTP a) (IOTP b))
  := coe_biject (ap IOTP p).

Definition interp2 {n} {a b : OTP n} (p : a ≡ b) : IOTP a -> IOTP b
  := coe (ap IOTP p).

Theorem pf : (interp2 (otpEncrypt (cons oneb (cons zerob nil))) (cons oneb (cons oneb nil))) ≡ (cons zerob (cons oneb nil)).
Proof.
  assert (H1: (interp2 (otpEncrypt (cons oneb (cons zerob nil))) (cons oneb (cons oneb nil)))
              ≡ (coe (ap IOTP (otpEncrypt (cons oneb (cons zerob nil)))) (cons oneb (cons oneb nil)))).
  { exact idpath. }
  assert (H2: (coe (ap IOTP (otpEncrypt (cons oneb (cons zerob nil)))) (cons oneb (cons oneb nil)))
              ≡ (coe (ua (OTPequiv (cons oneb (cons zerob nil)))) (cons oneb (cons oneb nil)))).
  { exact (ap (fun x => (coe x (cons oneb (cons oneb nil)))) (IOTPPath (cons oneb (cons zerob nil)))). }
  assert (H3: (coe (ua (OTPequiv (cons oneb (cons zerob nil)))) (cons oneb (cons oneb nil)))
              ≡ (Σe_fst (coe_biject (ua (OTPequiv (cons oneb (cons zerob nil))))) (cons oneb (cons oneb nil)))).
  { exact idpath. }
  assert (H4: (Σe_fst (coe_biject (ua (OTPequiv (cons oneb (cons zerob nil))))) (cons oneb (cons oneb nil)))
              ≡ (Σe_fst (OTPequiv (cons oneb (cons zerob nil))) (cons oneb (cons oneb nil)))).
  { exact (ap (fun x => Σe_fst x (cons oneb (cons oneb nil))) (ua_cbj (OTPequiv (cons oneb (cons zerob nil))))). }
  assert (H5: (Σe_fst (OTPequiv (cons oneb (cons zerob nil))) (cons oneb (cons oneb nil)))
              ≡ (cons zerob (cons oneb nil))).
  { exact idpath. }
  rewrite -> H1.
  rewrite -> H2.
  rewrite -> H3; rewrite -> H4; rewrite -> H5.
  exact idpath.
Qed.


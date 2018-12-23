Add LoadPath "/home/paven/Type_Theory/Coq/HoTT/Crypto".

Require Import PathUtils.
Require Import Vector.
Require Import OTPSpace.

Set Universe Polymorphism.

Fixpoint xor (n m : Bit) : Bit :=
  match n, m with
    | zerob, x => x
    | oneb, zerob => oneb
    | oneb, oneb => zerob
  end.

Fixpoint xorBits {n : nat} (v1 v2 : vec Bit n) : vec Bit n :=
  match v1 in vec _ n return vec Bit n -> vec Bit n with
  | nil =>           fun _  => nil
  | cons x1 v1' => fun v2 => cons (xor x1 (hd v2)) (xorBits v1' (tl v2))
  end v2.


Definition OTPencrypt {n : nat}
  (key : vec Bit n)
  (message : vec Bit n)
  : vec Bit n
  := xorBits message key.


Fixpoint zerobvec (n : nat) : vec Bit n := 
  match n as n0 return vec Bit n0 with
  | 0 => nil
  | S n0 => cons zerob (zerobvec n0)
  end.

(* Check Bit_ind. *)

Definition xorsym : forall (x : Bit), xor x x ≡ zerob :=
  Bit_ind (fun x => xor x x ≡ zerob) idpath idpath.

Definition xorid : forall (x : Bit), xor x zerob ≡ x :=
  Bit_ind (fun x => xor x zerob ≡ x) idpath idpath.

Definition xorassoc : forall (x y z : Bit), (xor (xor x y) z) ≡ (xor x (xor y z)) :=
  Bit_ind (fun x => forall (y z : Bit), (xor (xor x y) z) ≡ (xor x (xor y z)))
    (Bit_ind (fun y => forall (z : Bit), (xor (xor oneb y) z) ≡ (xor oneb (xor y z)))
      (Bit_ind (fun z => (xor (xor oneb oneb) z) ≡ (xor oneb (xor oneb z))) idpath idpath)
      (Bit_ind (fun z => (xor (xor oneb zerob) z) ≡ (xor oneb (xor zerob z))) idpath idpath))
    (Bit_ind (fun y => forall (z : Bit), (xor (xor zerob y) z) ≡ (xor zerob (xor y z)))
      (Bit_ind (fun z => (xor (xor zerob oneb) z) ≡ (xor zerob (xor oneb z))) idpath idpath)
      (Bit_ind (fun z => (xor (xor zerob zerob) z) ≡ (xor zerob (xor zerob z))) idpath idpath)).

Theorem xorSymPrf : forall (n : nat) (x : vec Bit n), xorBits x x ≡ (zerobvec n).
Proof.
  intros n x.
  elim x.
    exact idpath.

    intros n0 a v.
    intros ind_H.
    assert (H1: (xorBits (cons a v) (cons a v)) ≡ (cons (xor a a) (xorBits v v))).
    { exact idpath. }
    assert (H2: (cons (xor a a) (xorBits v v)) ≡ (cons (xor a a) (zerobvec n0))).
    { exact (ap (fun pxs => (cons (xor a a) pxs)) ind_H). }
    assert (H3: (cons (xor a a) (zerobvec n0)) ≡ (cons zerob (zerobvec n0))).
    { exact (ap (fun px => cons px (zerobvec n0)) (xorsym a)). }
    assert (H4: (cons zerob (zerobvec n0)) ≡ zerobvec (S n0)).
    { exact idpath. }
    rewrite -> H1.
    rewrite -> H2.
    rewrite -> H3.
    rewrite -> H4.
    exact idpath.
Qed.

Theorem xorIdPrf : forall (n : nat) (x : vec Bit n), (xorBits x (zerobvec n)) ≡ x.
Proof.
  intros n x.
  elim x.
    exact idpath.

    intros n0 a v.
    intros ind_H.
    assert (H1: xorBits (cons a v) (zerobvec (S n0)) ≡ xorBits (cons a v) (cons zerob (zerobvec n0))).
    { exact idpath. }
    assert (H2: xorBits (cons a v) (cons zerob (zerobvec n0)) ≡ (cons (xor a zerob) (xorBits v (zerobvec n0)))).
    { exact idpath. }
    assert (H3: (cons (xor a zerob) (xorBits v (zerobvec n0))) ≡ (cons (xor a zerob) v)).
    { exact (ap (fun pxs => (cons (xor a zerob) pxs)) ind_H). }
    assert (H4: (cons (xor a zerob) v) ≡ (cons a v)).
    { exact (ap (fun px => cons px v) (xorid a)). }
    rewrite -> H1.
    rewrite -> H2.
    rewrite -> H3.
    rewrite -> H4.
    exact idpath.
Qed.

Fixpoint pfVec {n : nat} (x : vec Bit (S n)) : (cons (hd x) (tl x)) ≡ x.
Proof.
  refine (
    match x with
    | cons a v => _
    end).
  assert (H1: (cons (hd (cons a v)) (tl (cons a v))) ≡ 
               cons a v).
  { exact idpath. }
  rewrite -> H1.
  exact idpath.
Qed.

Fixpoint xorAssocPf (n : nat) (x1 y1 z1 : vec Bit n) {struct x1} : (xorBits (xorBits x1 y1) z1) ≡ (xorBits x1 (xorBits y1 z1)).
  refine (
    match x1 in vec _ n0 return forall (y z : vec Bit n0), (xorBits (xorBits x1 y) z) ≡ (xorBits x1 (xorBits y z)) with
    | nil => fun _ _ => idpath
    | cons x xs => fun y z => _
    end y1 z1).
  assert (H1: (xorBits (xorBits (cons x xs) (cons (hd y) (tl y))) (cons (hd z) (tl z))) ≡ 
              (xorBits (cons (xor x (hd y)) (xorBits xs (tl y))) (cons (hd z) (tl z)))).
  { exact idpath. }
  assert (H2: (xorBits (cons (xor x (hd y)) (xorBits xs (tl y))) (cons (hd z) (tl z))) ≡ 
              (cons (xor (xor x (hd y)) (hd z)) (xorBits (xorBits xs (tl y)) (tl z)))).
  { exact idpath. }
  assert (H3: (cons (xor (xor x (hd y)) (hd z)) (xorBits (xorBits xs (tl y)) (tl z))) ≡ 
              (cons (xor x (xor (hd y) (hd z))) (xorBits (xorBits xs (tl y)) (tl z)))).
  { exact (ap (fun p => (cons p (xorBits (xorBits xs (tl y)) (tl z)))) (xorassoc x (hd y) (hd z))). }
  assert (H4: (cons (xor x (xor (hd y) (hd z))) (xorBits (xorBits xs (tl y)) (tl z))) ≡ 
              (cons (xor x (xor (hd y) (hd z))) (xorBits xs (xorBits (tl y) (tl z))))).
  { exact (ap (fun p => (cons (xor x (xor (hd y) (hd z))) p)) (xorAssocPf n0 xs (tl y) (tl z))). } 
  assert (H5: (cons (xor x (xor (hd y) (hd z))) (xorBits xs (xorBits (tl y) (tl z)))) ≡ 
              (xorBits (cons x xs) (cons (xor (hd y) (hd z)) (xorBits (tl y) (tl z))))).
  { exact idpath. }
  assert (H6: (xorBits (cons x xs) (cons (xor (hd y) (hd z)) (xorBits (tl y) (tl z)))) ≡ 
              (xorBits (cons x xs) (xorBits (cons (hd y) (tl y)) (cons (hd z) (tl z))))).
  { exact idpath. }
  assert (H7: (cons (hd y) (tl y)) ≡ y).
  { exact (pfVec y). }
  assert (H8: (cons (hd z) (tl z)) ≡ z).
  { exact (pfVec z). }
  rewrite <- H7; rewrite <- H8; rewrite -> H1; rewrite -> H2; rewrite -> H3; rewrite -> H4; rewrite -> H5; rewrite -> H6.
  exact idpath.
Qed.


Theorem alphaOTP : forall {n : nat} (key : vec Bit n) (message : vec Bit n), (OTPencrypt key (OTPencrypt key message)) ≡ message.
Proof.
intros n key msg.
assert (H1: (OTPencrypt key (OTPencrypt key msg)) ≡ 
            (OTPencrypt key (xorBits msg key))).
{ exact idpath. }
assert (H2: (OTPencrypt key (xorBits msg key)) ≡ 
            (xorBits (xorBits msg key) key)).
{ exact idpath. }
assert (H3: (xorBits (xorBits msg key) key) ≡ 
            (xorBits msg (xorBits key key))).
{ exact (xorAssocPf n msg key key). }  
assert (H4: (xorBits msg (xorBits key key)) ≡ 
            (xorBits msg (zerobvec n))).
{ exact (ap (fun x => xorBits msg x) (xorSymPrf n key)). }
assert (H5: (xorBits msg (zerobvec n)) ≡ 
            msg).
{ exact (xorIdPrf n msg). }
rewrite -> H1; rewrite -> H2; rewrite -> H3; rewrite -> H4; rewrite -> H5.
exact idpath.
Qed.

Definition fcompg {n : nat} (key : vec Bit n) : vec Bit n -> vec Bit n :=
(OTPencrypt key) ∘ (OTPencrypt key).

Definition alpha {n} (key : vec Bit n) : fnext (fcompg key) id
  := alphaOTP key.

Definition OTPequiv {n} (key : vec Bit n) : equiv (vec Bit n) (vec Bit n)
  := BuildΣe (OTPencrypt key) (equiv1 (BuildQinv (OTPencrypt key) (alpha key) (alpha key))).

Definition OTPpath {n} (key : vec Bit n) : (vec Bit n ≡ vec Bit n)
  :=
  match univalence with
  | (BuildΣe _ eq) => IsEquiv_g eq (OTPequiv key)
  end.


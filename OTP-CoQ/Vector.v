Set Implicit Arguments.

Inductive vec (A : Type) : nat -> Type :=
  | nil : vec A 0
  | cons : forall n : nat, A -> vec A n -> vec A (S n).
   Arguments nil [A].

Definition hd (A : Type) (n : nat) (v : vec A (S n)) : A :=
  match v in (vec _ (S n)) return A with
  | cons h _ => h
  end.

Definition tl (A : Type) n (v : vec A (S n)) : vec A n :=
  match v with
  | cons _ tl => tl
  end.

Fixpoint vpadd {n : nat} (v1 v2 : vec nat n) : vec nat n :=
  match v1 in vec _ n return vec nat n -> vec nat n with
  | nil =>           fun _  => nil
  | cons x1 v1' => fun v2 => cons (x1 + hd v2) (vpadd v1' (tl v2))
  end v2.


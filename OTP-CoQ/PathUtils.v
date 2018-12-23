Global Unset Strict Universe Declaration.
Global Unset Universe Minimization ToSet.
Global Set Keyed Unification.
Global Unset Bracketing Last Introduction Pattern.
Global Unset Refine Instance Mode.

Local Set Typeclasses Strict Resolution.
Local Unset Elimination Schemes.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.


Reserved Notation "x ≡ y :> A" (at level 70, y at next level, no associativity).
Reserved Notation "x ≡ y" (at level 70, no associativity).
Notation "x ≡ y :> A" := (@paths A x y) : type_scope.
Notation "x ≡ y" := (x ≡ y :>_) : type_scope.

Definition paths_ind {A : Type} (P : forall (a b : A), (a ≡ b) -> Type)
  : (forall (a : A), P a a idpath) -> forall (a b : A) (p : a ≡ b), P a b p.
Proof.
  intros H. 
  intros ? ? [].
  apply H.
Defined.

Bind Scope path_scope with paths.
Local Open Scope path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x ≡ y) (u : P x) : P y :=
  match p with idpath => u end.

Arguments transport {A}%type_scope P%function_scope {x y} p%path_scope u : simpl nomatch.

Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p # x" (right associativity, at level 65, only parsing).
Notation "p # x" := (transport _ p x) (only parsing) : type_scope.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x ≡ y) : f x ≡ f y
  := match p with idpath => idpath end.

Global Arguments ap {A B}%type_scope f%function_scope {x y} p%path_scope.

Arguments ap {A B} f {x y} p : simpl nomatch.

Definition apD {A : Type} {B : A -> Type} (f : forall (a : A), B a) {x y : A} (p : x ≡ y) : p # (f x) ≡ f y
  :=
  match p with idpath => idpath end.

Arguments apD {A%type_scope B} f%function_scope {x y} p%path_scope : simpl nomatch.

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f) (at level 40, left associativity) : type_scope.

(* Local Open Scope program_scope. *)

Definition id {A : Type} (x : A) : A
  := x.

Definition fnext {A : Type} {P : A -> Type} (f g : forall (x : A), P x) : Type 
  := forall (x : A), f x ≡ g x.

Record Qinv {A} {B} (f : A -> B) := BuildQinv {
  g : B -> A ;
  α : fnext (f ∘ g) id ;
  β : fnext (g ∘ f) id
}.

Arguments BuildQinv {A B} {f} _ _ _.
Set Universe Polymorphism.
 
Record IsEquiv {A} {B} (f : A -> B) := BuildIsEquiv {
  IsEquiv_g : B -> A ;
  IsEquiv_α : fnext (f ∘ IsEquiv_g) id ;
  IsEquiv_h : B -> A ;
  IsEquiv_β : fnext (IsEquiv_h ∘ f) id
}.

Arguments BuildIsEquiv {A B} {f} _ _ _ _.
Arguments IsEquiv_g {A B} {f}.

Definition equiv1 {A} {B} {f : A -> B} (x : Qinv f) : IsEquiv f
  := 
  match x with
  | (BuildQinv qg qa qb) => BuildIsEquiv qg qa qg qb
  end.

Record Σe (A : Type) (B : A -> Type) := BuildΣe {
  Σe_fst : A ;
  Σe_snd : B Σe_fst
}.

Arguments BuildΣe {A B} _ _.
Arguments Σe_fst {A B}.
Arguments Σe_snd {A B}.

Definition equiv (A B : Type) : Type
  := Σe (A -> B) IsEquiv.

Axiom univalence : forall {A B : Type}, (equiv (A ≡ B) (equiv A B)).
Axiom ua : forall {A B : Type}, (equiv A B) -> (A ≡ B).

Definition coe_biject {A B : Type} (path : A ≡ B) : (equiv A B)
  := 
  match univalence with
  | (BuildΣe f eq) => f path
  end.
  
Definition coe {A B : Type} (path : A ≡ B) : A -> B
  := Σe_fst (coe_biject path).

Axiom ua_cbj : forall {A B : Type} (eq : equiv A B), (coe_biject (ua eq)) ≡ eq.


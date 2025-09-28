Set Primitive Projections.
Set Universe Polymorphism.
Set Definitional UIP.

(* Utilities *)

Record andS (A : SProp) (B : SProp) : SProp :=
  mkAndS {
      fstS : A ;
      sndS : B ;
    }.
Arguments mkAndS {_} {_}.
Arguments fstS {_} {_}.
Arguments sndS {_} {_}.
Notation "A ∧ B" := (andS A B) (at level 80, right associativity).

Record andD (A : SProp) (B : A -> SProp) : SProp :=
  mkAndD {
      fstD : A ;
      sndD : B fstD ;
    }.
Arguments mkAndD {_} {_}.
Arguments fstD {_} {_}.
Arguments sndD {_} {_}.

Inductive orS (A B : SProp) : SProp :=
| orS_introl : A -> orS A B
| orS_intror : B -> orS A B.
Notation "A ∨ B" := (orS A B) (at level 85, right associativity).

Inductive FalseS : SProp :=.

Inductive TrueS : SProp := ttS.

Definition notS (A : SProp) : SProp := A -> FalseS.
Notation "¬ A" := (notS A) (at level 75, right associativity).

Definition bi_impl (A B : SProp) : SProp := (A -> B) ∧ (B -> A).
Notation "A ↔ B" := (bi_impl A B) (at level 95, no associativity).

Inductive eqS (A : Type) (a : A) : A -> SProp :=
| eqS_refl : eqS A a a.
Arguments eqS {_}.
Arguments eqS_refl {_}.
Notation "x ≡ y" := (eqS x y) (at level 70, no associativity).

Definition transp {A : Type} (P : A -> Type) {a b : A} (e : a ≡ b) : P a -> P b.
Proof.
  intro p. exact (eqS_rect A a (fun b _ => P b) p b e).
Defined.

Definition transpS {A : Type} (P : A -> SProp) {a b : A} (e : a ≡ b) : P a -> P b.
Proof.
  intro p. exact (eqS_sind A a (fun b _ => P b) p b e).
Qed.

Lemma sym {A : Type} {a b : A} : a ≡ b -> b ≡ a.
Proof.
  intro e. exact (eqS_sind A a (fun b _ => b ≡ a) (eqS_refl a) b e).
Qed.

Lemma trans {A : Type} {a b c : A} : a ≡ b -> b ≡ c -> a ≡ c.
Proof.
  intros e1 e2. apply (transpS (fun c => a ≡ c) e2). exact e1.
Qed.

Record Sigma (A : Type) (B : A -> SProp) : Type :=
  mkSigma {
      fst : A ;
      snd : B fst ;
    }.
Arguments mkSigma {_} {_}.
Arguments fst {_} {_}.
Arguments snd {_} {_}.

Record SigmaT (A : Type) (B : A -> Type) : Type :=
  mkSigmaT {
      fstT : A ;
      sndT : B fstT ;
    }.
Arguments mkSigmaT {_} {_}.
Arguments fstT {_} {_}.
Arguments sndT {_} {_}.

Inductive exS (A : Type) (B : A -> SProp) : SProp :=
| exS_intro : forall x : A, B x -> exS A B.

Definition uniqueS {A : Type} (P : A -> SProp) (x : A) :=
  P x ∧ forall (x':A), P x' -> x ≡ x'.

Definition exU (A : Type) (B : A -> SProp) : SProp := exS A (uniqueS B).

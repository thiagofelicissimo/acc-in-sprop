Set Primitive Projections.
Set Universe Polymorphism.

(* Our model construction is supposed to take place in ZF set theory, which is a set of axioms that
   can be put on top of first order logic (FOL). However, we certainly do not want to do a deep
   embedding of FOL in the logic of Rocq!
   Instead, we will use a shallow embedding of HOL into Rocq's logic (by carefully avoiding the use
   of dependent types and universes) and then postulate the skolemised axioms of ZF in HOL. This
   file does the shallow embedding of HOL into Rocq.

   - We use [SProp] as our type of truth values (we postulate classical logic, so it might as well
     be [bool]).
   - Dependent function types are not allowed, only universal quantifiers are allowed
     (i.e., we can write [forall] only when writing an inhabitant of [SProp]).
   - We allow prenex polymorphism over [Type], but we do not use universes otherwise.
   - Inductive types are used to simulate the logical connectives [∧] [∨] [⊤] [⊥] [∃] [=].
   - Large elimination is disallowed thanks to them living in [SProp].
 *)

(* Conjunction of truth values *)
Record andS (A : SProp) (B : SProp) : SProp :=
  mkAndS {
      fstS : A ;
      sndS : B ;
    }.
Arguments mkAndS {_} {_}.
Arguments fstS {_} {_}.
Arguments sndS {_} {_}.
Notation "A ∧ B" := (andS A B) (at level 80, right associativity).

(* Disjunction of truth values *)
Inductive orS (A B : SProp) : SProp :=
| orS_introl : A -> orS A B
| orS_intror : B -> orS A B.
Notation "A ∨ B" := (orS A B) (at level 85, right associativity).

Inductive FalseS : SProp :=.

Inductive TrueS : SProp := ttS.

Definition notS : SProp -> SProp := fun A => A -> FalseS.
Notation "¬ A" := (notS A) (at level 75, right associativity).

Definition bi_impl : SProp -> SProp -> SProp := fun A B => (A -> B) ∧ (B -> A).
Notation "A ↔ B" := (bi_impl A B) (at level 95, no associativity).

Inductive eqS (A : Type) (a : A) : A -> SProp :=
| eqS_refl : eqS A a a.
Arguments eqS {_}.
Arguments eqS_refl {_}.
Notation "x ≡ y" := (eqS x y) (at level 70, no associativity).

Definition transpS {A : Type} (P : A -> SProp) {a b : A} : a ≡ b -> P a -> P b.
Proof.
  intros e p. exact (eqS_sind A a (fun b _ => P b) p b e).
Qed.

Lemma sym {A : Type} {a b : A} : a ≡ b -> b ≡ a.
Proof.
  intro e. exact (eqS_sind A a (fun b _ => b ≡ a) (eqS_refl a) b e).
Qed.

Lemma trans {A : Type} {a b c : A} : a ≡ b -> b ≡ c -> a ≡ c.
Proof.
  intros e1 e2. apply (transpS (fun c => a ≡ c) e2). exact e1.
Qed.

(* Record Sigma (A : Type) (B : A -> SProp) : Type := *)
(*   mkSigma { *)
(*       fst : A ; *)
(*       snd : B fst ; *)
(*     }. *)
(* Arguments mkSigma {_} {_}. *)
(* Arguments fst {_} {_}. *)
(* Arguments snd {_} {_}. *)

Inductive exS (A : Type) (B : A -> SProp) : SProp :=
| exS_intro : forall x : A, B x -> exS A B.

Definition uniqueS {A : Type} (P : A -> SProp) (x : A) :=
  P x ∧ forall (x':A), P x' -> x ≡ x'.

Definition exU (A : Type) (B : A -> SProp) : SProp := exS A (uniqueS B).

(* Classical logic *)
Axiom LEM : forall (P : SProp), P ∨ (¬ P).


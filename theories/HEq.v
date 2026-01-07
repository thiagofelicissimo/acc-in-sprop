Set Universe Polymorphism.


(* In this file, we work internally in the system of TypingP. 
   However, we only postulate the conversions associated with cast
   propositionally, in order to avoid rewrite rules. *)


(* --- START OF THE DEF OF OBS EQ --- *)

Inductive obseq@{u} (A : Type@{u}) (a : A) : forall (b : A), SProp :=
| obseq_refl : obseq A a a.
Notation "a ~ b" := (obseq _ a b) (at level 50).
Arguments obseq {A} a _.
Arguments obseq_refl {A a} , [A] a.

Definition obseq_trans {A : Type} {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
  obseq_sind _ b (fun X _ => a ~ X) e c e'.
Notation "e @@@ f" := (obseq_trans e f) (at level 40, left associativity, only parsing).

Definition obseq_sym {A : Type} {a b : A} (e : a ~ b) : b ~ a :=
  obseq_sind _ a (fun X _ => X ~ a) obseq_refl b e.

(* Type casting *)

Axiom cast@{u v} : forall (A B : Type@{u}), @obseq@{v} Type@{u} A B -> A -> B.
Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

(* SProp casting *)
(* We do not want to use sort polymorphism for cast, to avoid useless (and potentially looping)
   computations in SProp *)

Definition cast_prop (A B : SProp) (e : @obseq SProp A B) (a : A) := obseq_sind SProp A (fun X _ => X) a B e.
Notation "e #% a" := (cast_prop _ _ e a) (at level 40, only parsing).

Axiom cast_refl : forall A e t, cast A A e t ~ t.

(* We can use cast to derive large elimination principles for obseq *)

Definition ap {A B} (f : A -> B) {x y} (e : x ~ y) : f x ~ f y :=
  obseq_sind _ x (fun y _ => f x ~ f y) obseq_refl _ e.

Definition apd {A} {a} (P : forall b : A, a ~ b -> Type) (b : A) (e : a ~ b) : (P a obseq_refl) ~ (P b e) :=
  obseq_sind _ a (fun b e => (P a obseq_refl) ~ (P b e)) obseq_refl b e.

Definition obseq_rect : forall (A : Type) (a : A) (P : forall b : A, obseq a b -> Type),
    P a obseq_refl -> forall (b : A) (e : obseq a b), P b e :=
  fun A a P t b e => cast (P a obseq_refl) (P b e) (apd P b e) t.

Definition obseq_rec : forall (A : Type) (a : A) (P : forall b : A, obseq a b -> Set),
    P a obseq_refl -> forall (b : A) (e : obseq a b), P b e :=
  fun A a P t b e => cast (P a obseq_refl) (P b e) (apd P b e) t.

(** Definition of the observational equality on pi's *)

Axiom obseq_forall_1@{u v +} : 
    forall 
        {A A' : Type@{u}} 
        {B : A -> Type@{v}} {B' : A' -> Type@{v}}, 
        (forall (x : A), B x) ~ (forall (x : A'), B' x) -> 
        A' ~ A.

Parameter obseq_forall_2@{u v+} : 
    forall 
        {A A' : Type@{u}} {B : A -> Type@{v}} {B' : A' -> Type@{v}}
        (e : (forall (x : A), B x) ~ (forall (x : A'), B' x))
        (x : A'), 
        (B (obseq_forall_1 e # x)) ~ (B' x).

Parameter funext : forall {A B} (f g : forall (x : A), B x), (forall (x : A), f x ~ g x) -> f ~ g.

Axiom cast_pi : forall A B A' B' e f, 
    cast (forall (x : A), B x) (forall (x : A'), B' x) e f 
    = fun (x : A') => cast (B (cast A' A (obseq_forall_1 e) x))
                            (B' x)
                            (obseq_forall_2 e x)
                            (f (cast A' A (obseq_forall_1 e) x)).

Parameter propext : forall {A B : SProp}, (A -> B) -> (B -> A) -> A ~ B.

(* --- END OF THE DEF OF OBS EQ --- *)

(* Constructing Sigmas *)
Definition Σ (A : SProp) (B : A -> SProp) : SProp := 
    forall P, (forall a:A, B a -> P) -> P.

Definition fst {A B}: Σ A B -> A := 
    fun f => f A (fun a b => a).

Definition snd {A B}: forall (x : Σ A B), B (fst x) := 
    fun f => f (B (fst f)) (fun a b => b).

Definition mkΣ {A B} (a : A) (b : B a) : Σ A B := 
    fun P f => f a b.

(* the heterogeneous equality *)
Definition heq (A B : Type) (a : A) (b : B) := 
    Σ (A ~ B) (fun eq_ty => (eq_ty # a) ~ b).

Notation "a == b" := (heq _ _ a b) (at level 90).

Lemma heq_refl {A : Type} (a : A) : a == a. 
Proof.
    unfold heq. unshelve eapply mkΣ.
    - eapply obseq_refl.
    - eapply cast_refl.
Qed.

Lemma heq_sym {A B : Type} {a : A} {b : B} (e : a == b) : b == a. 
Proof.
    unshelve eapply mkΣ.
    - eapply obseq_sym. eapply fst in e. assumption.
    - unfold heq in e. eapply fst in e as e1. 
      pose proof (e2 := snd e). simpl in e2.
      destruct e1. destruct e2. eapply obseq_trans.
      eapply cast_refl.
      eapply cast_refl.
Qed.

Lemma heq_trans {A B C} {a : A} {b : B} {c : C} (p : a == b) (q : b == c) : a == c.
Proof.
    eapply fst in p as p1. pose proof (p2 := snd p).
    eapply fst in q as q1. pose proof (q2 := snd q). simpl in p2,q2.
    destruct p1. destruct q1. destruct q2. destruct p2.
    unshelve eapply mkΣ. eapply obseq_refl.
    eapply obseq_sym. eapply cast_refl.
Qed.

Lemma homo_to_hetero {A : Type} {a b : A} (e : a ~ b) : a == b.
Proof.
    unshelve eapply mkΣ. eapply obseq_refl. 
    eapply obseq_trans. eapply cast_refl. eapply e.
Qed.

Lemma hetero_to_homo {A : Type} {a b : A} (e : a == b) : a ~ b.
Proof.
    eapply fst in e as e1. pose proof (e2 := snd e).
    destruct e1. destruct e2. eapply obseq_sym. eapply cast_refl.
Qed.

Definition cast_heq {A B : Type} (e : A == B) (a : A) : B := hetero_to_homo e # a.

Lemma heq_ap : forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} {t : A1} {u : A2} (p : f == g) (q : t == u), (f t) == (g u).
Proof.  
    intros.
    eapply fst in p as p1. pose proof (p2 := snd p).
    eapply fst in q as q1. pose proof (q2 := snd q). simpl in p2,q2.
    destruct q1. destruct q2. 
Admitted.


Definition heq_cast_left {A B C : Type} {t : A} {u : C} (e : A ~ B) (p : t == u) : e # t == u. 
Admitted.

Definition heq_cast_right {A B C : Type} {t : A} {u : B} (e : B ~ C) (p : t == u) : t == e # u.
Admitted.

Definition heq_cast_left' {A B C : Type} {t : A} {u : C} (e : A ~ B) (p : e # t == u) : t == u.
Admitted.

Definition heq_cast_right' {A B C : Type} {t : A} {u : B} (e : B ~ C) (p : t == e # u) : t == u.
Admitted.

Definition heq_funext : forall {A : Type} {B1 B2 : A -> Type} {f : forall x : A, B1 x} {g : forall x : A, B2 x} (p : forall x, f x == g x), f == g.
Admitted.

Definition heq_funext' {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} (e : A1 ~ A2) (p : forall x, f x == g (e # x)) : f == g.   
Proof.
Admitted.
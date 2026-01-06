From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Contexts Typing TypingP BasicMetaTheory BasicMetaTheoryP.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.

(* Σ types using an impredicative encoding

  Σ A B := Π (P : Prop). (Π (x : A). B x → P) → P

  TODO FIX, at least the levels are wrong

*)

Definition Sig i A B :=
  Pi (ty 0) prop (Sort prop) (
    Pi prop prop (Pi (Ax i) prop (S ⋅ S ⋅ A) (Pi prop prop (app (Ax i) (ty 0) (S ⋅ S ⋅ S ⋅ A) (Sort prop) (S ⋅ S ⋅ S ⋅ B) (var 0)) (var 2))) (var 1)
  ).

Definition sig_ex (i : level) (A B a b : term) : term.
Admitted.

Lemma type_Sig Γ i A B :
  Γ ⊢< Ax i > A : Sort i →
  Γ ⊢< ty 0 > B : Pi (Ax i) (ty 0) A (Sort prop) →
  Γ ⊢< ty 0 > Sig i A B : Sort prop.
Proof.
Admitted.

Lemma type_sig_ex Γ i A B a b :
  Γ ⊢< Ax i > A : Sort i →
  Γ ⊢< ty 0 > B : Pi (Ax i) (ty 0) A (Sort prop) →
  Γ ⊢< i > a : A →
  Γ ⊢< prop > b : app (Ax i) (ty 0) A (Sort prop) B a →
  Γ ⊢< ty 0 > sig_ex i A B a b : Sig i A B.
Proof.
Admitted.

(* Heterogenous equality

  heq A B a b := Σ (A = B) (λ p. cast p a = b)

*)

Definition heq i A B a b :=
  Sig prop (obseq (ty (S i)) (Sort (ty i)) A B) (
    lam prop (ty 0) (obseq (ty (S i)) (Sort (ty i)) A B) (Sort prop) (
      obseq (ty i) (S ⋅ B) (cast (ty i) (S ⋅ A) (S ⋅ B) (var 0) (S ⋅ a)) (S ⋅ b)
    )
  ).

Lemma type_heq Γ i A B a b :
  Γ ⊢< ty (S i) > A : Sort (ty i) →
  Γ ⊢< ty (S i) > B : Sort (ty i) →
  Γ ⊢< ty i > a : A →
  Γ ⊢< ty i > b : B →
  Γ ⊢< ty 0 > heq i A B a b : Sort prop.
Proof.
Admitted.

Lemma conv_heq Γ i A A' B B' a a' b b' :
  Γ ⊢< ty (S i) > A ≡ A' : Sort (ty i) →
  Γ ⊢< ty (S i) > B ≡ B' : Sort (ty i) →
  Γ ⊢< ty i > a ≡ a' : A →
  Γ ⊢< ty i > b ≡ b' : B →
  Γ ⊢< ty 0 > heq i A B a b ≡ heq i A' B' a' b' : Sort prop.
Proof.
Admitted.

Definition heq_refl (i : nat) (A a : term) : term.
Admitted.

Lemma type_heq_refl Γ i A a :
  Γ ⊢< ty (S i) > A : Sort (ty i) →
  Γ ⊢< ty i > a : A →
  Γ ⊢< prop > heq_refl i A a : heq i A A a a.
Proof.
Admitted.

Definition heq_cast (i : nat) (A B e a : term) : term.
Admitted.

Lemma type_heq_cast Γ i A B e a :
  Γ ⊢< ty (S i) > A : Sort (ty i) →
  Γ ⊢< ty (S i) > B : Sort (ty i) →
  Γ ⊢< prop > e : obseq (ty (S i)) (Sort (ty i)) A B →
  Γ ⊢< ty i > a : A →
  Γ ⊢< prop > heq_cast i A B e a : heq i A B a (cast (ty i) A B e a).
Proof.
Admitted.

(* Uniqueness of type *)

Lemma unique_type Γ i u A B :
  Γ ⊢< i > u : A →
  Γ ⊢< i > u : B →
  Γ ⊢< Ax i > A ≡ B : Sort i.
Proof.
Admitted.

(* Potential translations

  u ⊏ v means that v is u decorated with casts.

*)

Reserved Notation " t ⊏ t' " (at level 19).

Inductive decoration : term → term → Prop :=
| add_cast i A B e a :
    a ⊏ cast i A B e a

| dec_Pi i j A A' B B' :
    A ⊏ A' →
    B ⊏ B' →
    Pi i j A B ⊏ Pi i j A' B'

| dec_lam i j A A' B B' t t' :
    A ⊏ A' →
    B ⊏ B' →
    t ⊏ t' →
    lam i j A B t ⊏ lam i j A' B' t'

| dec_app i j A A' B B' t t' u u' :
    A ⊏ A' →
    B ⊏ B' →
    t ⊏ t' →
    u ⊏ u' →
    app i j A B t u ⊏ app i j A' B' t' u'

| dec_succ t t' :
    t ⊏ t' →
    succ t ⊏ succ t'

| dec_rec l P P' pz pz' ps ps' t t' :
    P ⊏ P' →
    pz ⊏ pz' →
    ps ⊏ ps' →
    t ⊏ t' →
    rec l P pz ps t ⊏ rec l P' pz' ps' t'

| dec_acc i A A' R R' a a' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    acc i A R a ⊏ acc i A' R' a'

| dec_accin i A A' R R' a a' p p' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    p ⊏ p' →
    accin i A R a p ⊏ accin i A' R' a' p'

| dec_accinv i A A' R R' a a' p p' b b' r r' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    p ⊏ p' →
    b ⊏ b' →
    r ⊏ r' →
    accinv i A R a p b r ⊏ accinv i A' R' a' p' b' r'

| dec_accel i l A A' R R' P P' p p' a a' q q' :
    A ⊏ A' →
    R ⊏ R' →
    P ⊏ P' →
    a ⊏ a' →
    q ⊏ q' →
    accel i l A R P p a q ⊏ accel i l A' R' P' p' a' q'

| dec_obseq i A A' a a' b b' :
    A ⊏ A' →
    a ⊏ a' →
    b ⊏ b' →
    obseq i A a b ⊏ obseq i A' a' b'

| dec_obsrefl i A A' a a' :
    A ⊏ A' →
    a ⊏ a' →
    obsrefl i A a ⊏ obsrefl i A' a'

| dec_J i A A' a a' P P' p p' b b' e e' :
    A ⊏ A' →
    a ⊏ a' →
    P ⊏ P' →
    p ⊏ p' →
    b ⊏ b' →
    e ⊏ e' →
    J i A a P p b e ⊏ J i A' a' P' p' b' e'

| dec_cast i A A' B B' e e' a a' :
    A ⊏ A' →
    B ⊏ B' →
    e ⊏ e' →
    a ⊏ a' →
    cast i A B e a ⊏ cast i A' B' e' a'

| dec_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ⊏ A1' →
    A2 ⊏ A2' →
    B1 ⊏ B1' →
    B2 ⊏ B2' →
    e ⊏ e' →
    injpi1 i j A1 A2 B1 B2 e ⊏ injpi1 i j A1' A2' B1' B2' e'

| dec_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ⊏ A1' →
    A2 ⊏ A2' →
    B1 ⊏ B1' →
    B2 ⊏ B2' →
    e ⊏ e' →
    a2 ⊏ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ⊏ injpi2 i j A1' A2' B1' B2' e' a2'

| dec_refl u :
    u ⊏ u

| dec_trans u v w :
    u ⊏ v →
    v ⊏ w →
    u ⊏ w

where "u ⊏ v" := (decoration u v).

Reserved Notation " t ~ t' " (at level 19).

Inductive simdec : term → term → Prop :=
| sim_cast i A B e a :
    a ~ cast i A B e a

| dec_sim_Pi i j A A' B B' :
    A ~ A' →
    B ~ B' →
    Pi i j A B ~ Pi i j A' B'

| dec_sim_lam i j A A' B B' t t' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    lam i j A B t ~ lam i j A' B' t'

| dec_sim_app i j A A' B B' t t' u u' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    u ~ u' →
    app i j A B t u ~ app i j A' B' t' u'

| dec_sim_succ t t' :
    t ~ t' →
    succ t ~ succ t'

| dec_sim_rec l P P' pz pz' ps ps' t t' :
    P ~ P' →
    pz ~ pz' →
    ps ~ ps' →
    t ~ t' →
    rec l P pz ps t ~ rec l P' pz' ps' t'

| dec_sim_acc i A A' R R' a a' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    acc i A R a ~ acc i A' R' a'

| dec_sim_accin i A A' R R' a a' p p' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    accin i A R a p ~ accin i A' R' a' p'

| dec_sim_accinv i A A' R R' a a' p p' b b' r r' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    b ~ b' →
    r ~ r' →
    accinv i A R a p b r ~ accinv i A' R' a' p' b' r'

| dec_sim_accel i l A A' R R' P P' p p' a a' q q' :
    A ~ A' →
    R ~ R' →
    P ~ P' →
    a ~ a' →
    q ~ q' →
    accel i l A R P p a q ~ accel i l A' R' P' p' a' q'

| dec_sim_obseq i A A' a a' b b' :
    A ~ A' →
    a ~ a' →
    b ~ b' →
    obseq i A a b ~ obseq i A' a' b'

| dec_sim_obsrefl i A A' a a' :
    A ~ A' →
    a ~ a' →
    obsrefl i A a ~ obsrefl i A' a'

| dec_sim_J i A A' a a' P P' p p' b b' e e' :
    A ~ A' →
    a ~ a' →
    P ~ P' →
    p ~ p' →
    b ~ b' →
    e ~ e' →
    J i A a P p b e ~ J i A' a' P' p' b' e'

| dec_sim_cast i A A' B B' e e' a a' :
    A ~ A' →
    B ~ B' →
    e ~ e' →
    a ~ a' →
    cast i A B e a ~ cast i A' B' e' a'

| dec_sim_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    injpi1 i j A1 A2 B1 B2 e ~ injpi1 i j A1' A2' B1' B2' e'

| dec_sim_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    a2 ~ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ~ injpi2 i j A1' A2' B1' B2' e' a2'

| dec_sim_refl u :
    u ~ u

| dec_sim_trans u v w :
    u ~ v →
    v ~ w →
    u ~ w

where "u ~ v" := (simdec u v).

Lemma dec_to_sim u v :
  u ⊏ v →
  u ~ v.
Proof.
  induction 1.
  all: solve [ econstructor ; eauto ].
Qed.

(* Fundamental lemma

  We're going to prove a more general statement with cast substitutions, but
  for now, we'll admit this version.
  In ETT to ITT/WTT, we used the more general version too in the final
  translation so we'll have to check whether it's needed.

*)

Lemma sim_heq i Γ u v A B :
  u ~ v →
  Γ ⊢< ty i > u : A →
  Γ ⊢< ty i > v : B →
  ∃ e, Γ ⊢< prop > e : heq i A B u v.
Proof.
  intros hsim hu hv.
  induction hsim in Γ, A, B, hu, hv |- *.
  - eapply type_inv_cast in hv as hv'.
    destruct hv' as (hA & hB & he & ha & -> & hBB).
    eexists. eapply type_conv.
    + eapply type_heq_cast. 3: exact he. all: eassumption.
    + apply conv_sym. eapply conv_heq. all: try (apply conv_refl ; assumption).
      2: assumption.
      eapply meta_lvl_conv.
      { eapply unique_type. all: eassumption. }
      reflexivity.
Admitted.

(* Potential translations *)

Definition ctx_dec (Γ Δ : ctx) :=
  Forall2 (λ u v, snd u ⊏ snd v) Γ Δ.

Notation " Γ ⊂ Δ " := (ctx_dec Γ Δ) (at level 19).

Definition tr_ctx Γ Δ :=
  ⊢ Δ ∧ Γ ⊂ Δ.

Definition tr_ty l t A Γ' t' A' :=
  Γ' ⊢< l > t' : A' ∧ t ⊏ t' ∧ A ⊏ A'.

Notation "D ⊨⟨ l ⟩ t : A ∈ ⟦ u : B ⟧" :=
  (tr_ty l u B D t A)
  (at level 8, t, A, u, B at next level).

Definition eqtrans l A u v Γ' A' A'' u' v' e :=
  match l with
  | prop => True
  | ty i =>
    A ⊏ A' ∧
    A ⊏ A'' ∧
    u ⊏ u' ∧
    v ⊏ v' ∧
    Γ' ⊢< prop > e : heq i A' A'' u' v'
  end.

(* New notations for source derivations *)

Notation "Γ ∋< l >× x : T" :=
  (Typing.varty Γ x l T) (at level 50, l, x, T at next level).

Notation "Γ ⊢< l >× t : A" :=
  (Typing.typing Γ l t A) (at level 50, l, t, A at next level).

Notation "Γ ⊢< l >× t ≡ u : T" :=
 (Typing.conversion Γ l t u T) (at level 50, l, t, u, T at next level).

Notation "⊢× Γ" :=
  (Typing.ctx_typing Γ) (at level 50).

(* Translation of derivations *)

(* TODO MOVE *)
Lemma Forall2_inv_l A B (R : A → B → Prop) a la lb :
  Forall2 R (a :: la) lb →
  ∃ b lb', Forall2 R la lb' ∧ R a b ∧ lb = b :: lb'.
Proof.
  inversion 1. subst.
  firstorder eauto.
Qed.

Lemma tr_ctx_inv Γ l A Δ :
  tr_ctx (Γ ,, (l, A)) Δ →
  ∃ Γ' A', tr_ctx Γ Γ' ∧ A ⊏ A' ∧ Δ = Γ',, (l, A').
Proof.
  intros [h1 h2].
  eapply Forall2_inv_l in h2 as ((l' & A') & Γ' & ? & ? & ->).
  inversion h1. subst.
  cbn in *.
  unfold tr_ctx. firstorder eauto.
Abort.

(* Lemma varty_trans Γ Γ' x l A :
  Γ ∋< l >× x : A →
  tr_ctx Γ Γ' →
  ∃ A', Γ' ∋< l > x : A'.
Proof.
  intros hx [hc hs].
  induction hx in Γ', hc, hs |- *.
  - inversion hs. subst. cbn in *.
    eexists. econstructor.
  -



  induction hs as [| σ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed. *)

Lemma typing_conversion_trans :
  (∀ Γ l t A,
    Γ ⊢< l >× t : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      ∃ t' A', Γ' ⊨⟨ l ⟩ t' : A' ∈ ⟦ t : A ⟧
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l >× u ≡ v : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      ∃ A' A'' u' v' e, eqtrans l A u v Γ' A' A'' u' v' e
  ).
Proof.
  apply Typing.typing_mutind.
  - intros * ? hx ? hc.
Abort.

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

Reserved Notation " t ⊏ t' " (at level 21).

Inductive decoration : term → term → Prop :=
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

| add_cast i A B e a :
    a ⊏ cast i A B e a

where "u ⊏ v" := (decoration u v).

Reserved Notation " t ~ t' " (at level 19).

Inductive simdec : term → term → Prop :=
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

| sim_cast i A B e a :
    a ~ cast i A B e a

where "u ~ v" := (simdec u v).

Lemma dec_to_sim u v :
  u ⊏ v →
  u ~ v.
Proof.
  induction 1.
  all: solve [ econstructor ; eauto ].
Qed.

Lemma rename_dec ρ u v :
  u ⊏ v →
  ρ ⋅ u ⊏ ρ ⋅ v.
Proof.
  induction 1 in ρ |- *.
  all: solve [ cbn ; econstructor ; eauto ].
Qed.

Lemma subst_dec σ u v :
  u ⊏ v →
  u <[ σ ] ⊏ v <[ σ ].
Proof.
  induction 1 in σ |- *.
  all: solve [ cbn ; econstructor ; eauto ].
Qed.

Definition dec_subst (σ θ : nat → term) :=
  ∀ x, σ x ⊏ θ x.

Lemma dec_subst_up σ θ :
  dec_subst σ θ →
  dec_subst (up_term σ) (up_term θ).
Proof.
  intros h [].
  - cbn. constructor.
  - cbn. unfold ">>". apply rename_dec. apply h.
Qed.

Lemma dec_subst_one u v :
  u ⊏ v →
  dec_subst (u..) (v..).
Proof.
  intros h [].
  - cbn. assumption.
  - cbn. constructor.
Qed.

Lemma dec_subst_scons u v σ σ' :
  u ⊏ v →
  dec_subst σ σ' →
  dec_subst (u .: σ) (v .: σ').
Proof.
  intros hu hs [].
  - cbn. assumption.
  - cbn. apply hs.
Qed.

Lemma dec_subst_refl σ :
  dec_subst σ σ.
Proof.
  intro. apply dec_refl.
Qed.

Lemma substs_dec σ θ u :
  dec_subst σ θ →
  u <[ σ ] ⊏ u <[ θ ].
Proof.
  intros h.
  induction u in σ, θ, h |- *.
  all: try solve [ cbn ; econstructor ; eauto using dec_subst_up ].
  - cbn. eauto.
  - cbn.
Admitted.

Lemma substs_decs σ θ u v :
  dec_subst σ θ →
  u ⊏ v →
  u <[ σ ] ⊏ v <[ θ ].
Proof.
  intros hs hd.
  eapply dec_trans.
  - eapply subst_dec. eassumption.
  - apply substs_dec. assumption.
Qed.

Lemma substs_decs_one u v a b :
  u ⊏ v →
  a ⊏ b →
  u <[ a .. ] ⊏ v <[ b .. ].
Proof.
  intros h1 h2.
  apply substs_decs. 2: auto.
  apply dec_subst_one. assumption.
Qed.

(* Fundamental lemma

  We're going to prove a more general statement with cast substitutions, but
  for now, we'll admit this version.
  I already have a plan in mind so it might not be necessary to have a look at
  it yet.
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
  1-17: admit.
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
  Forall2 (λ u v, fst u = fst v ∧ snd u ⊏ snd v) Γ Δ.

Notation " Γ ⊂ Δ " := (ctx_dec Γ Δ) (at level 19).

Definition tr_ctx Γ Δ :=
  ⊢ Δ ∧ Γ ⊂ Δ.

Definition tr_ty_data l t A Γ' t' A' :=
  Γ' ⊢< l > t' : A' ∧ t ⊏ t' ∧ A ⊏ A'.

Notation "D ⊨⟨ l ⟩ t : A ↦ u : B" :=
  (tr_ty_data l t A D u B)
  (at level 50, t, A, u, B at next level).

Definition tr_ty_abs l t A Γ' A' :=
  ∃ t', tr_ty_data l t A Γ' t' A'.

Notation "D ⊨⟨ l ⟩ t : A ⇒ B" :=
  (tr_ty_abs l t A D B)
  (at level 50, t, A, B at next level).

Definition tr_ty l t A Γ' :=
  ∃ A', Γ' ⊨⟨ l ⟩ t : A ⇒ A'.

Notation "D ⊨⟨ l ⟩ t : A" :=
  (tr_ty l t A D)
  (at level 50, t, A at next level).

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

Definition tr_eq Γ' l A u v :=
  ∃ A' A'' u' v' e, eqtrans l A u v Γ' A' A'' u' v' e.

Notation "D ⊨⟨ l ⟩ u ≡ v : A" :=
  (tr_eq D l A u v)
  (at level 50, u, v, A at next level).

(* Type heads *)

Inductive type_head := hSort (l : level) | hPi | hNat | hacc | hobseq.

Inductive has_type_head : term → type_head → Prop :=
| isSort l : has_type_head (Sort l) (hSort l)
| isPi i j A B : has_type_head (Pi i j A B) hPi
| isNat : has_type_head Nat hNat
| isacc i A R x : has_type_head (acc i A R x) hacc
| isobseq i A u v : has_type_head (obseq i A u v) hobseq.

Lemma keep_head Γ' l t A h :
  Γ' ⊨⟨ l ⟩ t : A →
  has_type_head A h →
  ∃ A',
    has_type_head A' h ∧
    Γ' ⊨⟨ l ⟩ t : A ⇒ A'.
Proof.
  intros ht hh.
Admitted.

Corollary keep_sort Γ' i j A :
  Γ' ⊨⟨ i ⟩ A : Sort j →
  Γ' ⊨⟨ i ⟩ A : Sort j ⇒ Sort j.
Proof.
  intros h.
  eapply keep_head in h. 2: econstructor.
  destruct h as (A' & h & hA).
  inversion h. subst.
  assumption.
Qed.

Lemma change_type Γ' i t A A' :
  Γ' ⊨⟨ i ⟩ t : A →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ' ⊨⟨ i ⟩ t : A ⇒ A'.
Proof.
Admitted.

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

Lemma tr_ctx_inv Γ l A Δ :
  tr_ctx (Γ ,, (l, A)) Δ →
  ∃ Γ' A', tr_ctx Γ Γ' ∧ A ⊏ A' ∧ Δ = Γ',, (l, A').
Proof.
  intros [h1 h2].
  eapply Forall2_inv_l in h2 as ((l' & A') & Γ' & ? & (e & ?) & ->).
  cbn in e. subst.
  inversion h1. subst.
  firstorder eauto.
Qed.

Lemma varty_trans Γ Γ' x l A :
  Γ ∋< l >× x : A →
  tr_ctx Γ Γ' →
  ∃ A', Γ' ∋< l > x : A' ∧ A ⊏ A'.
Proof.
  intros hx hc.
  induction hx as [| Γ i j A B x hx ih] in Γ', hc |- *.
  - eapply tr_ctx_inv in hc as (Δ & A' & hc & hA & ->).
    eexists. split.
    + constructor.
    + apply rename_dec. assumption.
  - eapply tr_ctx_inv in hc as (Δ & B' & hc & hB & ->).
    eapply ih in hc. destruct hc as (A' & h & hA).
    eexists. split.
    + econstructor. eassumption.
    + apply rename_dec. assumption.
Qed.

Lemma tr_var Γ Γ' x A l :
  Γ ∋< l >× x : A →
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ l ⟩ var x : A.
Proof.
  intros hx hc.
  eapply varty_trans in hx as hx'. 2: eassumption.
  destruct hx' as (A' & hx' & hA).
  eexists _,_. split.
  { econstructor. 2: eauto. apply hc. }
  intuition constructor.
Qed.

(* Not ideal, but given circumstances there is not much else we can do. *)

Axiom tr_assm_sig :
  ∀ c A,
    nth_error Typing.assm_sig c = Some A →
    ∃ A',
      nth_error assm_sig c = Some A' ∧ A ⊏ A' ∧ ∙ ⊢< Ax prop > A' : Sort prop.

Lemma tr_ctx_cons Γ Γ' A A' i :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  tr_ctx (Γ ,, (i, A)) (Γ' ,, (i, A')).
Proof.
  intros [hc1 hc2] (? & ? & hs).
  split.
  - econstructor. all: eauto.
  - econstructor. 2: eassumption.
    cbn. intuition auto.
Qed.

Lemma tr_Sort Γ Γ' l :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax (Ax l) ⟩ Sort l : Sort (Ax l).
Proof.
  intros hc.
  eexists _,_. split. 2: intuition constructor.
  econstructor. apply hc.
Qed.

Lemma tr_Pi i j Γ' A A' B :
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ',, (i, A') ⊨⟨ Ax j ⟩ B : Sort j →
  Γ' ⊨⟨ Ax (Ru i j) ⟩ Pi i j A B : Sort (Ru i j).
Proof.
  intros ihA ihB.
  eapply keep_sort in ihB.
  destruct ihA as (? & ? & ?), ihB as (?& ? & ?).
  eexists _,_. split. 2: intuition (constructor ; eauto).
  econstructor. all: eauto.
Qed.

Lemma tr_Nat Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 1 ⟩ Nat : Sort (ty 0) ↦ Nat : Sort (ty 0).
Proof.
  intro hc.
  split. 2: intuition constructor.
  constructor.
  apply hc.
Qed.

Lemma tr_zero Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat.
Proof.
  intros hc.
  eexists _,_. split. 2: intuition constructor.
  constructor. apply hc.
Qed.

Lemma tr_succ Γ' t :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat.
Proof.
  intros iht.
  eapply keep_head in iht. 2: econstructor.
  destruct iht as (? & hh & iht). inversion hh. subst.
  destruct iht as (? & ? & ?).
  eexists _,_. split. 2: intuition (constructor ; eauto).
  constructor. assumption.
Qed.

Definition tr_subst_data Γ' σ σ' Δ' :=
  Γ' ⊢s σ' : Δ' ∧ dec_subst σ σ'.

Notation "Γ ⊨s σ : Δ ⇒ σ'" :=
  (tr_subst_data Γ σ σ' Δ)
  (at level 50, σ, Δ at next level).

Definition tr_subst Γ' σ Δ' :=
  ∃ σ', tr_subst_data Γ' σ σ' Δ'.

Notation "Γ ⊨s σ : Δ" :=
  (tr_subst Γ σ Δ)
  (at level 50, σ, Δ at next level).

#[export] Instance dec_subst_morphism :
  Proper ((`=1`) ==> (`=1`) ==> iff) dec_subst.
Proof.
  intros σ σ' e θ θ' e'.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  intros x. rewrite <- e, <- e'. apply h.
Qed.

#[export] Instance tr_subst_data_morphism :
  Proper (eq ==> (`=1`) ==> (`=1`) ==> eq ==> iff) tr_subst_data.
Proof.
  intros Γ ? <- σ σ' e θ θ' e' Δ ? <-.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  destruct h. split.
  - rewrite <- e'. assumption.
  - rewrite <- e, <- e'. assumption.
Qed.

#[export] Instance tr_subst_morphism :
  Proper (eq ==> (`=1`) ==> eq ==> iff) tr_subst.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  destruct h as [s h]. exists s.
  rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_tr_subst_data :
  ∀ Γ Δ s1 s2 s3 s4,
    SubstSimplification s1 s2 →
    SubstSimplification s3 s4 →
    tr_subst_data Γ s1 s3 Δ ↔ tr_subst_data Γ s2 s4 Δ.
Proof.
  intros * h1 h2.
  apply tr_subst_data_morphism. 1,4: eauto.
  - apply h1.
  - apply h2.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_tr_subst_data : rasimpl_outermost.

Lemma autosubst_simpl_tr_subst :
  ∀ Γ Δ s1 s2,
    SubstSimplification s1 s2 →
    tr_subst Γ s1 Δ ↔ tr_subst Γ s2 Δ.
Proof.
  intros * h.
  apply tr_subst_morphism. 1,3: eauto.
  apply h.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_tr_subst : rasimpl_outermost.

Lemma tr_subst_scons l Γ' Δ' σ σ' A A' u :
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ l ⟩ u : A <[ σ ] ⇒ A' <[ σ' ] →
  Γ' ⊨s (u .: σ) : Δ' ,, (l, A').
Proof.
  intros [hs1 hs2] [? [hu1 hu2]].
  eexists. split.
  - apply well_scons_alt. all: eauto.
  - apply dec_subst_scons. all: intuition eauto.
Qed.

Lemma tr_subst_ren Γ Γ' Δ' ρ :
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨s (ρ >> var) : Δ' ⇒ (ρ >> var).
Proof.
  intros hc hr.
  split. 2: apply dec_subst_refl.
  apply WellSubst_ren.
  - assumption.
  - apply hc.
Qed.

Lemma tr_substitution i Γ Γ' t A Δ' σ :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ t : A →
  Γ' ⊨s σ : Δ' →
  Γ' ⊨⟨ i ⟩ t <[ σ ] : A <[ σ ].
Proof.
  intros hc ht hs.
  destruct ht as (? & ? & ? & ?), hs as (? & ? & ?).
  eexists _,_. split. 2: intuition eauto using substs_decs.
  eapply typing_conversion_subst.
  - eassumption.
  - apply hc.
  - assumption.
Qed.

Corollary tr_substitution_sort i Γ Γ' A l Δ' σ :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ A : Sort l →
  Γ' ⊨s σ : Δ' →
  Γ' ⊨⟨ i ⟩ A <[ σ ] : Sort l.
Proof.
  intros hc ht hs.
  eapply tr_substitution in hs. 2,3: eassumption.
  assumption.
Qed.

Corollary tr_substitution_one i j Γ Γ' t u A B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ t : A →
  Γ' ⊨⟨ j ⟩ u : B ⇒ B' →
  Γ' ⊨⟨ i ⟩ t <[ u .. ] : A <[ u .. ].
Proof.
  intros hc ht hu.
  eapply tr_substitution. 1,2: eassumption.
  destruct hu as (? & hu).
  eexists. split.
  - apply subst_one. apply hu.
  - apply dec_subst_one. apply hu.
Qed.

Corollary tr_substitution_one_sort i j Γ Γ' t u l B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ t : Sort l →
  Γ' ⊨⟨ j ⟩ u : B ⇒ B' →
  Γ' ⊨⟨ i ⟩ t <[ u .. ] : Sort l.
Proof.
  intros hc ht hu.
  eapply tr_substitution_one in hu. 2,3: eassumption.
  assumption.
Qed.

Lemma typing_conversion_trans :
  (∀ Γ l t A,
    Γ ⊢< l >× t : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      Γ' ⊨⟨ l ⟩ t : A
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l >× u ≡ v : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      Γ ⊨⟨ l ⟩ u ≡ v : A
  ).
Proof.
  apply Typing.typing_mutind.

  (* Typing rules *)

  - intros * ? hx ? hc.
    eapply tr_var. all: eassumption.
  - intros * ?? hc.
    eapply tr_Sort. eassumption.
  - intros * ? e ? ih ? hc.
    eapply tr_assm_sig in e as e'. destruct e' as (A' & e' & ? & ?).
    eexists _, (assm _). split.
    { econstructor. 2,3: eassumption. apply hc. }
    intuition constructor.
  - intros * ? ihA ? ihB ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_Pi. 1: eassumption.
    eapply ihB.
    eapply tr_ctx_cons. all: eassumption.
  - intros * ? ihA ? ihB ? iht ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    specialize iht with (1 := hca).
    eapply change_type in iht. 2: eassumption.
    destruct iht as (t' & iht).
    destruct ihA as (? & ? & _), ihB as (? & ? & _), iht as (? & ? & _).
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihB ? iht ? ihu ? hc.
    specialize ihA with (1 := hc).
    eapply keep_sort in ihA. destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca).
    eapply keep_sort in ihB. destruct ihB as (B' & ihB).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ fail. (* We need the explicit version! *)


    eapply tr_Pi. all: eassumption. }
    destruct iht as (t'' & iht).
    specialize ihu with (1 := hc). destruct ihu as (u' & Au & ihu).
    eapply change_type in ihu. 2: eassumption.
    destruct ihu as (u'' & ihu).
    destruct
      ihA as (? & ? & _),
      ihB as (? & ? & _),
      iht as (? & ? & _),
      ihu as (? & ? & _).
    eexists _,_. split. 2: split. 2: constructor ; eauto.
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: assumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_Nat. eassumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_zero. eassumption.
  - intros * ? iht ? hc.
    specialize iht with (1 := hc). destruct iht as (t' & N & iht).
    eapply change_type in iht. 2:{ eapply tr_Nat. all: eassumption. }
    destruct iht as (t'' & iht).
    eexists _,_. eapply tr_succ. eassumption.
  - intros * ? ihP ? ihz ? ihs ? iht ? hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn). destruct ihP as (P' & ?s & ihP).
    eapply keep_sort in ihP. destruct ihP as (P'' & ihP).
    specialize ihz with (1 := hc). destruct ihz as (?z' & ?T & ihz).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns). destruct ihs as (?s' & ?T' & ihs).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ.
        (* Need tr_var or something, but can we actually do it?
          I guess it works if we're ok with the translated term not being a
          variable.

          Or we have a version that works when translation is identity?

          Perhaps I should try to have a judgment Γ' ⊨⟨ l ⟩ t : A
          defined as ∃ t', A', …
          so that they compose better.
          Need to think how change_type and so on become with it.
          Maybe a judgment that also specifies the type like
          Γ' ⊨⟨ l ⟩ t : A ⇒ A'
        *)
        admit.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    specialize iht with (1 := hc). destruct iht as (?t' & ?T & iht).
    eapply change_type in iht. 2:{ eapply tr_Nat. eassumption. }
    destruct iht as (?t' & iht).
    (* TODO LATER *)
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros * ? iht ? ihAB ? hc.
    admit.

  (* Conversion rules *)

  - intros * ??? hc. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

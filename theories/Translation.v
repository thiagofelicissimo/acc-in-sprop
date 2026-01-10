From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Contexts Typing TypingP BasicMetaTheory BasicMetaTheoryP TypeUniquenessP.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.


(* the following axioms are justified in the file HEq.v *)

Axiom heq : level -> term -> term -> term -> term -> term.

Axiom heq_ren : forall ρ l A B a e,
  ρ ⋅ (heq l A B a e) = heq l (ρ ⋅ A) (ρ ⋅ B) (ρ ⋅ a) (ρ ⋅ e).

Axiom type_heq : forall Γ n A B a b,
  Γ ⊢< Ax (ty n) > A : Sort (ty n) →
  Γ ⊢< Ax (ty n) > B : Sort (ty n) →
  Γ ⊢< ty n > a : A →
  Γ ⊢< ty n > b : B →
  Γ ⊢< ty 0 > heq (ty n) A B a b : Sort prop.

Axiom conv_heq : forall Γ n A B a b A' B' a' b',
  Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
  Γ ⊢< Ax (ty n) > B ≡ B' : Sort (ty n) →
  Γ ⊢< ty n > a ≡ a' : A →
  Γ ⊢< ty n > b ≡ b' : B →
  Γ ⊢< ty 0 > heq (ty n) A B a b ≡ heq (ty n) A' B' a' b' : Sort prop.



Axiom heq_refl : level -> term -> term -> term.

Axiom type_heq_refl : forall Γ n A a,
  Γ ⊢< Ax (ty n) > A : Sort (ty n) →
  Γ ⊢< ty n > a : A →
  Γ ⊢< prop > heq_refl (ty n) A a : heq (ty n) A A a a.

Axiom conv_heq_refl : forall Γ n A A' a a',
  Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
  Γ ⊢< ty n > a ≡ a' : A →
  Γ ⊢< prop > heq_refl (ty n) A a ≡ heq_refl (ty n) A' a' : heq (ty n) A A a a.  



Axiom heq_sym : level -> term -> term -> term -> term -> term -> term.

Axiom type_heq_sym : forall Γ n A B b a e,
  Γ ⊢< ty n > a : A ->
  Γ ⊢< ty n > b : B ->
  Γ ⊢< prop > e : heq (ty n) A B a b →
  Γ ⊢< prop > heq_sym (ty n) A B a b e : heq (ty n) B A b a.

Axiom conv_heq_sym : forall Γ n A B b a e A' B' b' a' e',
  Γ ⊢< ty n > a ≡ a' : A ->
  Γ ⊢< ty n > b ≡ b' : B ->
  Γ ⊢< prop > e ≡ e' : heq (ty n) A B a b →
  Γ ⊢< prop > heq_sym (ty n) A B a b e ≡ heq_sym (ty n) A' B' a' b' e' : heq (ty n) B A b a.



Axiom heq_trans : level -> term -> term -> term -> term -> term -> term -> term -> term -> term.

Axiom type_heq_trans : forall Γ n A B C c b a e1 e2,
  Γ ⊢< ty n > a : A ->
  Γ ⊢< ty n > b : B ->
  Γ ⊢< ty n > c : C ->
  Γ ⊢< prop > e1 : heq (ty n) A B a b →
  Γ ⊢< prop > e2 : heq (ty n) B C b c → 
  Γ ⊢< prop > heq_trans (ty n) A B C a b c e1 e2 : heq (ty n) A C a c.

Axiom conv_heq_trans : forall Γ n A B C c b a e1 e2 A' B' C' c' b' a' e1' e2',
  Γ ⊢< ty n > a ≡ a' : A ->
  Γ ⊢< ty n > b ≡ b' : B ->
  Γ ⊢< ty n > c ≡ c' : C ->
  Γ ⊢< prop > e1 ≡ e1' : heq (ty n) A B a b →
  Γ ⊢< prop > e2 ≡ e2' : heq (ty n) B C b c → 
  Γ ⊢< prop > heq_trans (ty n) A B C a b c e1 e2 ≡ heq_trans (ty n) A' B' C' a' b' c' e1' e2' : heq (ty n) A C a c.



Axiom heq_cast : forall (i : level) (A B e a : term), term.

Axiom type_heq_cast : forall Γ i A B e a,
  Γ ⊢< Ax (ty i) > A : Sort (ty i) →
  Γ ⊢< Ax (ty i) > B : Sort (ty i) →
  Γ ⊢< prop > e : obseq (Ax (ty i)) (Sort (ty i)) A B →
  Γ ⊢< ty i > a : A →
  Γ ⊢< prop > heq_cast (ty i) A B e a : heq (ty i) A B a (cast (ty i) A B e a).

Axiom conv_heq_cast : forall Γ i A A' B B' e e' a a',
  Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
  Γ ⊢< Ax (ty i) > B ≡ B' : Sort (ty i) →
  Γ ⊢< prop > e ≡ e' : obseq (Ax (ty i)) (Sort (ty i)) A B →
  Γ ⊢< ty i > a ≡ a' : A →
  Γ ⊢< prop > heq_cast (ty i) A B e a : heq (ty i) A B a (cast (ty i) A B e a).



Axiom heq_app : level -> level -> term -> term -> term -> term -> term -> term -> term -> term -> term -> term -> term.

Axiom type_heq_app : forall Γ n m A1 A2 B1 B2 f1 f2 a1 a2 p q,
  Γ ,, (ty n, A1) ⊢< ty m > f1 : B1 ->
  Γ ,, (ty n, A2) ⊢< ty m > f2 : B2 ->
  Γ ⊢< ty n > a1 : A1 ->
  Γ ⊢< ty n > a2 : A2 ->
  Γ ⊢< prop > p : heq (Ru (ty n) (ty m)) (Pi (ty n) (ty m) A1 B1) (Pi (ty n) (ty m) A2 B2) f1 f2 -> 
  Γ ⊢< prop > q : heq (ty n) A1 A2 a1 a2 ->
  Γ ⊢< prop > heq_app (ty n) (ty m) A1 A2 B1 B2 f1 f2 a1 a2 p q 
    : heq (ty m) (B1 <[a1..]) (B2 <[a2..]) (app (ty n) (ty m) A1 B1 f1 a1) (app (ty n) (ty m) A2 B2 f2 a2).




Axiom heq_pi : level -> level -> term -> term -> term -> term -> term -> term -> term.

(* I think we will need another heq_pi which replaces (ty n) by prop, but this cannot be the same symbol *)
Axiom type_heq_pi : forall Γ n m A1 A2 B1 B2 p q,
  Γ ⊢< Ax (ty n) > A1 : Sort (ty n) ->
  Γ ⊢< Ax (ty n) > A2 : Sort (ty n) ->
  Γ ,, (ty n, A1) ⊢< Ax (ty m) > B1 : Sort (ty m) ->
  Γ ,, (ty n, A2) ⊢< Ax (ty m) > B2 : Sort (ty m) ->
  Γ ⊢< prop > p : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) A1 A2 ->
  let Aeq := heq (ty n) ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (ty n, A1) ,, (ty n, S ⋅ A2) ,, (prop, Aeq)
    ⊢< prop > q : heq (Ax (ty m)) (Sort (ty m)) (Sort (ty m)) (((S >> S >> S) ⋅ B1) <[(var 2)..]) (((S >> S >> S) ⋅ B2) <[(var 1)..]) -> 
  Γ ⊢< prop > heq_pi (ty n) (ty m) A1 A2 B1 B2 p q 
    : heq (Ax (Ru (ty n) (ty m))) (Sort (Ru (ty n) (ty m))) (Sort (Ru (ty n) (ty m))) (Pi (ty n) (ty m) A1 B1) (Pi (ty n) (ty m) A2 B2).


(* Uniqueness of type *)

(* The following can now be found in UnicityP.v *)
(* Lemma unique_type Γ i u A B :
  Γ ⊢< i > u : A →
  Γ ⊢< i > u : B →
  Γ ⊢< Ax i > A ≡ B : Sort i.
Proof.
Admitted. *)

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
| sim_var x :
    var x ~ var x 

| sim_sort l :
    Sort l ~ Sort l 

| sim_assm c :
    assm c ~ assm c 

| sim_Pi i j A A' B B' :
    A ~ A' →
    B ~ B' →
    Pi i j A B ~ Pi i j A' B'

| sim_lam i j A A' B B' t t' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    lam i j A B t ~ lam i j A' B' t'

| sim_app i j A A' B B' t t' u u' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    u ~ u' →
    app i j A B t u ~ app i j A' B' t' u'

| sim_nat : 
    Nat ~ Nat 

| sim_zero :
    zero ~ zero

| sim_succ t t' :
    t ~ t' →
    succ t ~ succ t'

| sim_rec l P P' pz pz' ps ps' t t' :
    P ~ P' →
    pz ~ pz' →
    ps ~ ps' →
    t ~ t' →
    rec l P pz ps t ~ rec l P' pz' ps' t'

| sim_acc i A A' R R' a a' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    acc i A R a ~ acc i A' R' a'

| sim_accin i A A' R R' a a' p p' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    accin i A R a p ~ accin i A' R' a' p'

| sim_accinv i A A' R R' a a' p p' b b' r r' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    b ~ b' →
    r ~ r' →
    accinv i A R a p b r ~ accinv i A' R' a' p' b' r'

| sim_accel i l A A' R R' P P' p p' a a' q q' :
    A ~ A' →
    R ~ R' →
    P ~ P' →
    a ~ a' →
    q ~ q' →
    accel i l A R P p a q ~ accel i l A' R' P' p' a' q'

| sim_obseq i A A' a a' b b' :
    A ~ A' →
    a ~ a' →
    b ~ b' →
    obseq i A a b ~ obseq i A' a' b'

| sim_obsrefl i A A' a a' :
    A ~ A' →
    a ~ a' →
    obsrefl i A a ~ obsrefl i A' a'

| sim_J i A A' a a' P P' p p' b b' e e' :
    A ~ A' →
    a ~ a' →
    P ~ P' →
    p ~ p' →
    b ~ b' →
    e ~ e' →
    J i A a P p b e ~ J i A' a' P' p' b' e'

(* admissible *)
(* | sim_cast i A A' B B' e e' a a' :
    A ~ A' →
    B ~ B' →
    e ~ e' →
    a ~ a' →
    cast i A B e a ~ cast i A' B' e' a' *)

| sim_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    injpi1 i j A1 A2 B1 B2 e ~ injpi1 i j A1' A2' B1' B2' e'

| sim_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    a2 ~ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ~ injpi2 i j A1' A2' B1' B2' e' a2'

| sim_castR i A B e a b :
    b ~ a →
    b ~ cast i A B e a

| sim_castL i A B e a b :
    a ~ b →
    cast i A B e a ~ b

where "u ~ v" := (simdec u v).

Lemma sim_cast i A A' B B' e e' a a' :
    a ~ a' →
    cast i A B e a ~ cast i A' B' e' a'.
Proof.
  intros. eauto using simdec.
Qed.

Lemma sim_refl t :
  t ~ t.
Proof.
  induction t. 
  all: eauto using simdec.
  admit.
Admitted.


Lemma sim_sym u v :
  u ~ v -> v ~ u.
Proof.
  intros. induction H; eauto using simdec.
Qed.

Derive Signature for simdec.
Lemma sim_trans t u v :
  t ~ u -> u ~ v -> t ~ v.
Proof.
  intros. rename H0 into h. generalize v h. clear v h. induction H; intros.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto 7 using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto 7 using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto 7 using simdec.
  - admit.
  - admit.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - admit.
  - admit.
  (* - dependent induction h; eauto using simdec. *)
  - admit.
  - apply IHsimdec. dependent induction h; eauto using simdec.
  - eapply IHsimdec in h. eauto using simdec.
Admitted.


(* Lemma dec_to_sim u v :
  u ⊏ v →
  u ~ v.
Proof.
  induction 1.
  all: solve [ econstructor ; eauto ].
Qed. *)

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

(* Fundamental lemma

  We're going to prove a more general statement with cast substitutions, but
  for now, we'll admit this version.
  I already have a plan in mind so it might not be necessary to have a look at
  it yet.
  In ETT to ITT/WTT, we used the more general version too in the final
  translation so we'll have to check whether it's needed.

*)

Definition renX m := 3 * m.
Definition renR m := 1 + (3 * m).
Definition renL m := 2 + (3 * m).

Fixpoint pack (Γ : ctx) := 
  match Γ with 
  | nil => ∙
  | cons (l, A) Γ => 
    let A1 := renL ⋅ A in
    let A2 := renR ⋅ A in
    let Aeq := heq l ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
    pack Γ ,, (l, A1) ,, (l, S ⋅ A2) ,, (prop, Aeq)
  end.


Lemma WellRen_packL Γ :
  pack Γ ⊢r renL : Γ.
Proof.
  induction Γ.
  - econstructor.
  - destruct a. unfold renL. econstructor.
    * simpl. eapply WellRen_weak,WellRen_weak,WellRen_weak. fold plus.
      eapply autosubst_simpl_WellRen. 2:eauto.
      econstructor. unfold pointwise_relation. intros.
      induction a; eauto.
      unfold renL in *.  simpl in *. rewrite IHa. lia.
    * eapply varty_meta. 1:cbn. 1:econstructor. 1:econstructor. 1:econstructor.
      unfold renL; ssimpl. eapply ren_term_morphism. 2:reflexivity.
      unfold pointwise_relation. intros. induction a.
      all:unfold ">>" in *; simpl in *; lia.
Qed.


Lemma WellRen_packR Γ :
  pack Γ ⊢r renR : Γ.
Proof.
  induction Γ.
  - econstructor.
  - destruct a. unfold renR. econstructor. 
    * simpl. eapply WellRen_weak,WellRen_weak. fold plus. 
      eapply autosubst_simpl_WellRen.
      2:eapply WellRen_weak. 2:eapply IHΓ. unfold renR. simpl.
      econstructor. unfold pointwise_relation. intros.
      unfold ">>". lia. 
    * eapply varty_meta. 1:cbn. 1:econstructor. 1:econstructor.
      unfold renR; ssimpl. eapply ren_term_morphism. 2:reflexivity.
      unfold pointwise_relation. intros. induction a.
      all:unfold ">>" in *; simpl in *; lia.
Qed.


Lemma sim_heq i Γ u v A B :
  u ~ v →
  Γ ⊢< ty i > u : A →
  Γ ⊢< ty i > v : B →
  ∃ e, pack Γ ⊢< prop > e : heq (ty i) (renL ⋅ A) (renR ⋅ B) (renL ⋅ u) (renR ⋅ v).
Proof.
  intros hsim hu hv.
  induction hsim in i, Γ, A, B, hu, hv |- *.
  all:try solve 
   [ eapply type_inv in hu; dependent destruction hu ; dependent destruction lvl_eq ].
  - admit.
  - eapply type_inv in hu, hv. dependent destruction hu. dependent destruction hv.  
    assert (⊢ pack Γ) by admit.
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty. 3:eapply WellRen_packL. all:eauto.
    eapply conv_ren in conv_ty0. 3:eapply WellRen_packR. all:eauto.
    simpl in *.
    eexists. eapply type_conv.
    2:eapply conv_heq.
    1:eapply type_heq_refl.
    all:simpl.
    5,6:eapply conv_refl; econstructor; eauto.
    1,2:eapply meta_lvl. 1:eapply meta_conv.
    1,4:eauto using typing.
    1-3:reflexivity.
    all:eauto using conv_sym.
  - eapply type_inv in hu, hv. dependent destruction hu. dependent destruction hv.
    
    edestruct IHhsim1. 1,2:unfold Ax in *; eauto.
    edestruct IHhsim2. 1,2:unfold Ax in *; eauto.
    all:admit.
    
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - eapply type_inv in hv as hv'; dependent destruction hv'. subst.
    destruct (IHhsim _ _ _ _ hu a_Wt).
    eexists. 
    eapply type_heq_trans.
    4:eapply H.
    all: try solve [ eapply type_ren; 
      eauto using WellRen_packL, WellRen_packR, validity_ty_ctx ].
    eapply type_ren.
    3:eapply WellRen_packR.
    2:eauto using validity_ty_ctx.
    1:eapply type_conv. 2:eapply conv_heq.
    6:rewrite heq_ren; reflexivity.
    1:eapply type_heq_cast. 3:exact e_Wt.
    all:eauto using conv_sym, conv_refl, conversion.
  - eapply type_inv in hu as hu'; dependent destruction hu'. subst.
    destruct (IHhsim _ _ _ _ a_Wt hv).
    eexists. 
    eapply type_heq_trans.
    5:eapply H.
    all: try solve [ eapply type_ren; 
      eauto using WellRen_packL, WellRen_packR, validity_ty_ctx ].
    eapply type_ren.
    3:eapply WellRen_packL.
    2:eauto using validity_ty_ctx.
    1:eapply type_conv. 2:eapply conv_heq.
    6:rewrite heq_ren; reflexivity.
    1:eapply type_heq_sym, type_heq_cast.
    5:eapply e_Wt.
    all:eauto using conv_sym, conv_refl, typing.
Admitted.

(* Potential translations *)

Definition ctx_dec (Γ Δ : ctx) :=
  Forall2 (λ u v, fst u = fst v ∧ snd u ⊏ snd v) Γ Δ.

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
    Γ' ⊢< prop > e : heq (ty i) A' A'' u' v'
  end.

(* Type heads *)

Inductive type_head := hSort (l : level) | hPi | hNat | hacc | hobseq.

Inductive has_type_head : term → type_head → Prop :=
| isSort l : has_type_head (Sort l) (hSort l)
| isPi i j A B : has_type_head (Pi i j A B) hPi
| isNat : has_type_head Nat hNat
| isacc i A R x : has_type_head (acc i A R x) hacc
| isobseq i A u v : has_type_head (obseq i A u v) hobseq.

Lemma keep_head Γ' l t t' A A' h :
  Γ' ⊨⟨ l ⟩ t' : A' ∈ ⟦ t : A ⟧ →
  has_type_head A h →
  ∃ A'' t'',
    has_type_head A'' h ∧
    Γ' ⊨⟨ l ⟩ t'' : A'' ∈ ⟦ t : A ⟧.
Proof.
  intros ht hh.
Admitted.

Corollary keep_sort Γ' i j A A' s :
  Γ' ⊨⟨ i ⟩ A' : s ∈ ⟦ A : Sort j ⟧ →
  ∃ A'', Γ' ⊨⟨ i ⟩ A'' : Sort j ∈ ⟦ A : Sort j ⟧.
Proof.
  intros h.
  eapply keep_head in h. 2: econstructor.
  destruct h as (A'' & s' & h & hA).
  inversion h. subst.
  firstorder.
Qed.

Lemma change_type Γ' i t t' A A1 A2 :
  Γ' ⊨⟨ i ⟩ t' : A1 ∈ ⟦ t : A ⟧ →
  Γ' ⊨⟨ Ax i ⟩ A2 : Sort i ∈ ⟦ A : Sort i ⟧ →
  ∃ t'', Γ' ⊨⟨ i ⟩ t'' : A2 ∈ ⟦ t : A ⟧.
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

(* Not ideal, but given circumstances there is not much else we can do. *)

Axiom tr_assm_sig :
  ∀ c A,
    nth_error Typing.assm_sig c = Some A →
    ∃ A',
      nth_error assm_sig c = Some A' ∧ A ⊏ A' ∧ ∙ ⊢< Ax prop > A' : Sort prop.

Lemma tr_ctx_cons Γ Γ' A A' i :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax i ⟩ A' : Sort i ∈ ⟦ A : Sort i ⟧ →
  tr_ctx (Γ ,, (i, A)) (Γ' ,, (i, A')).
Proof.
  intros [hc1 hc2] (? & ? & hs).
  split.
  - econstructor. all: eauto.
  - econstructor. 2: eassumption.
    cbn. intuition auto.
Qed.

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
    eapply varty_trans in hx as hx'. 2: eassumption.
    destruct hx' as (A' & hx' & hA).
    eexists _,_. split.
    { econstructor. 2: eauto. apply hc. }
    intuition constructor.
  - intros * ?? hc.
    eexists _,_. split. 2: intuition constructor.
    econstructor. apply hc.
  - intros * ? e ? ih ? hc.
    eapply tr_assm_sig in e as e'. destruct e' as (A' & e' & ? & ?).
    eexists (assm _), _. split.
    { econstructor. 2,3: eassumption. apply hc. }
    intuition constructor.
  - intros * ? ihA ? ihB ? hc.
    specialize ihA with (1 := hc). destruct ihA as (A' & s & ihA).
    eapply keep_sort in ihA. destruct ihA as (A'' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). destruct ihB as (B' & s' & ihB).
    eapply keep_sort in ihB. destruct ihB as (B'' & ihB).
    destruct ihA as (? & ? & _), ihB as (? & ? & _).
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihB ? iht ? hc.
    specialize ihA with (1 := hc). destruct ihA as (A' & s & ihA).
    eapply keep_sort in ihA. destruct ihA as (A'' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). destruct ihB as (B' & s' & ihB).
    eapply keep_sort in ihB. destruct ihB as (B'' & ihB).
    specialize iht with (1 := hca). destruct iht as (t' & B2 & iht).
    eapply change_type in iht. 2: eassumption.
    destruct iht as (t'' & iht).
    destruct ihA as (? & ? & _), ihB as (? & ? & _), iht as (? & ? & _).
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
Abort.

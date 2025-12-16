
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.

Derive Signature for varty.
Derive Signature for ctx_typing.
Derive Signature for typing.

Lemma Ax_inj l l' : Ax l = Ax l' → l = l'.
Proof.
  intro H. destruct l; destruct l'; inversion H; auto.
Qed.

(** Typing implies scoping *)

Lemma varty_scoped Γ l x A :
  Γ ∋< l > x : A →
  scoped (length Γ) (var x) = true.
Proof.
  induction 1.
  - reflexivity.
  - cbn - ["<?"] in *. rewrite Nat.ltb_lt in *. lia.
Qed.

Lemma typing_scoped Γ l t A :
  Γ ⊢< l > t : A →
  scoped (length Γ) t = true.
Proof.
  induction 1.
  all: try solve [ intros ; cbn - ["<?"] in * ; eauto using varty_scoped ].
  all: solve [
    intros ;
    cbn in * ;
    rewrite ?Bool.andb_true_iff in * ;
    intuition eauto
  ].
Qed.

Lemma typing_closed l t A :
  ∙ ⊢< l > t : A →
  closed t = true.
Proof.
  intros h.
  eapply typing_scoped with (Γ := ∙).
  eassumption.
Qed.

Lemma scoped_ren ρ k t :
  scoped k t = true →
  (Nat.iter k up_ren ρ) ⋅ t = t.
Proof.
  intros h.
  induction t in k, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ;
    rewrite ?Bool.andb_true_iff in * ;
    repeat change (upRen_term_term (Nat.iter ?k up_ren ?ρ)) with (Nat.iter (S k) up_ren ρ) ;
    intuition (f_equal ; eauto)
  ].
  cbn - ["<?"] in *. f_equal.
  apply Nat.ltb_lt in h.
  induction n as [| n ih] in k, h |- *.
  - destruct k. 1: lia.
    reflexivity.
  - destruct k. 1: lia.
    cbn. unfold ">>". f_equal.
    apply ih. lia.
Qed.

Corollary closed_ren ρ t :
  closed t = true →
  ρ ⋅ t = t.
Proof.
  intros h.
  eapply scoped_ren in h. eauto.
Qed.

Lemma conv_refl Γ t l A :
  Γ ⊢< l > t : A →
  Γ ⊢< l > t ≡ t : A.
Proof.
  induction 1.
  all: solve [ econstructor ; eauto ].
Qed.

Lemma conv_refl_conv Γ u v l A :
  Γ ⊢< l > u ≡ v : A →
  Γ ⊢< l > u ≡ u : A.
Proof.
  intros h.
  eapply conv_trans. 1: eassumption.
  apply conv_sym. assumption.
Qed.

Theorem refl_subst Γ σ Δ :
  Γ ⊢s σ : Δ →
  Γ ⊢s σ ≡ σ : Δ.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + eauto.
    + apply conv_refl. assumption.
Qed.

Lemma varty_meta Γ l x A B :
  Γ ∋< l > x : A →
  A = B →
  Γ ∋< l > x : B.
Proof.
  intros h ->. exact h.
Qed.

Lemma WellRen_meta Γ Γ' Δ Δ' ρ :
  Γ ⊢r ρ : Δ →
  Γ = Γ' →
  Δ = Δ' →
  Γ' ⊢r ρ : Δ'.
Proof.
  intros ? -> ->. auto.
Qed.

#[export] Instance WellRen_morphism :
  Proper (eq ==> (`=1`) ==> eq ==> iff) WellRen.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  induction h as [| ρ Δ l A h ih ho] in ρ', e |- *.
  - constructor.
  - constructor.
    + eapply ih. intros x. unfold ">>". apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_WellRen :
  ∀ Γ Δ r s,
    RenSimplification r s →
    Γ ⊢r r : Δ ↔ Γ ⊢r s : Δ.
Proof.
  intros Γ Δ r s H.
  apply WellRen_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_WellRen : rasimpl_outermost.

Lemma WellRen_weak Γ Δ ρ l A :
  Γ ⊢r ρ : Δ →
  Γ ,, (l, A) ⊢r (ρ >> S) : Δ.
Proof.
  induction 1 as [| ρ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply varty_meta.
      * unfold ">>". constructor. eassumption.
      * rasimpl. reflexivity.
Qed.

Lemma WellRen_up Γ Δ l A A' ρ :
  Γ ⊢r ρ : Δ →
  A' = ρ ⋅ A →
  Γ ,, (l, A') ⊢r up_ren ρ : Δ ,, (l, A).
Proof.
  intros h p. subst.
  constructor.
  - rasimpl. apply WellRen_weak. assumption.
  - rasimpl. cbn. eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.

Lemma varty_ren Γ Δ ρ x l A :
  Γ ∋< l > x : A →
  Δ ⊢r ρ : Γ →
  Δ ∋< l > ρ x : ρ ⋅ A.
Proof.
  intros hx hr.
  induction hr as [| ρ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma WellRen_comp Γ Δ Θ ρ ρ' :
  Δ ⊢r ρ : Θ →
  Γ ⊢r ρ' : Δ →
  Γ ⊢r (ρ >> ρ') : Θ.
Proof.
  intros hρ hρ'.
  induction hρ as [| ρ Θ i B h ih ho] in ρ', Γ, hρ' |- *.
  - constructor.
  - constructor.
    + eauto.
    + unfold ">>". eapply varty_meta.
      1: eauto using varty_ren.
      rasimpl. reflexivity.
Qed.

Lemma WellRen_id Γ :
  Γ ⊢r id : Γ.
Proof.
  induction Γ as [| [l A] Γ ih].
  - constructor.
  - constructor.
    + change (S >> id) with (id >> S).
      eauto using WellRen_weak.
    + constructor.
Qed.

Lemma WellRen_S Γ l A :
  Γ ,, (l, A) ⊢r S : Γ.
Proof.
  change S with (id >> S).
  apply WellRen_weak.
  apply WellRen_id.
Qed.

Lemma meta_conv Γ t l A B :
  Γ ⊢< l > t : A →
  A = B →
  Γ ⊢< l > t : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_lvl Γ t A i j :
  Γ ⊢< i > t : A →
  i = j →
  Γ ⊢< j > t : A.
Proof.
  intros ? ->. assumption.
Qed.

Lemma meta_conv_conv Γ u v l A B :
  Γ ⊢< l > u ≡ v : A →
  A = B →
  Γ ⊢< l > u ≡ v : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_lvl_conv Γ u v l l' A :
  Γ ⊢< l > u ≡ v : A →
  l = l' →
  Γ ⊢< l' > u ≡ v : A.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_rhs_conv Γ u v w l A :
  Γ ⊢< l > u ≡ v : A →
  v = w →
  Γ ⊢< l > u ≡ w : A.
Proof.
  intros ? ->. auto.
Qed.

Lemma validity_ctx :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ⊢ Γ
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ⊢ Γ).
Proof.
  apply typing_mutind. all: eauto.
Qed.

Corollary validity_ty_ctx Γ l t A :
  Γ ⊢< l > t : A →
  ⊢ Γ.
Proof.
  intros. eapply validity_ctx in H; eauto.
Qed.

Corollary validity_conv_ctx Γ l t u A :
  Γ ⊢< l > t ≡ u : A →
  ⊢ Γ.
Proof.
  intros. eapply validity_ctx in H; eauto.
Qed.

Lemma thread_pi Γ i j A B :
  Γ ⊢< Ax i > A : Sort i →
  (⊢ Γ ,, (i, A) → Γ ,, (i, A) ⊢< Ax j > B : Sort j) →
  Γ ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j).
Proof.
  intros.
  firstorder eauto using type_pi, ctx_cons, validity_ty_ctx.
Qed.

Lemma conv_cast_refl' Γ i A B e a :
  Γ ⊢< Ax i > A ≡ B : Sort i ->
  Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
  Γ ⊢< i > a : A ->
  Γ ⊢< i > cast i A B e a ≡ a : B.
Proof.
  intros hAB he ha.
  eapply conv_trans.
  - econstructor.
    + eapply conv_refl_conv. eassumption.
    + apply conv_sym. eassumption.
    + apply conv_refl. assumption.
    + apply conv_refl. assumption.
  - econstructor. 2: eassumption.
    econstructor. 2: auto.
    econstructor. 1: eassumption.
    constructor.
    + constructor. eapply validity_ty_ctx. eassumption.
    + eapply conv_refl_conv. eassumption.
    + apply conv_sym. assumption.
Qed.

Lemma well_rcons_alt Γ Δ x ρ l A :
  Γ ⊢r ρ : Δ →
  Γ ∋< l > x : ρ ⋅ A →
  Γ ⊢r (x .: ρ) : Δ ,, (l , A).
Proof.
  intros hr hx.
  constructor.
  - erewrite autosubst_simpl_WellRen. 2: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma varty0_eq Γ l A B :
  S ⋅ A = B →
  Γ ,, (l , A) ∋< l > 0 : B.
Proof.
  intros <-.
  constructor.
Qed.

Lemma vartyS_eq Γ i j A B C x :
  Γ ∋< i > x : A →
  S ⋅ A = C →
  Γ ,, (j, B) ∋< i > S x : C.
Proof.
  intros h <-.
  constructor. assumption.
Qed.

Ltac meta_conv :=
  lazymatch goal with
  | |- _ ⊢< _ > _ : _ => eapply meta_conv
  | |- _ ⊢< _ > _ ≡ _ : _ => eapply meta_conv_conv
  end.

Ltac subst_def :=
  lazymatch goal with
  | u := _ |- _ => subst u
  end.

Create HintDb sidecond.

Hint Resolve
  WellRen_up WellRen_comp WellRen_S well_rcons_alt varty0_eq vartyS_eq
  ctx_nil ctx_cons
  : sidecond.

Hint Extern 100 (_ = _) =>
  rasimpl ; reflexivity : sidecond.

Hint Extern 1000 (_ = _) =>
  repeat subst_def ; rasimpl ; reflexivity : sidecond.

Ltac ren_ih :=
  lazymatch goal with
  | |- _ ⊢< _ > _ ⋅ _ ⋅ _ : _ => rasimpl ; ren_ih
  | ih : ∀ (Δ : ctx) (ρ : nat → nat), ⊢ Δ → Δ ⊢r ρ : ?Γ → Δ ⊢< _ > ρ ⋅ ?t : _ |- _ ⊢< _ > ?r ⋅ ?t : _ =>
    eapply meta_conv ; [
      eapply ih with (ρ := r) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        ren_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | ih : ∀ (Δ : ctx) (ρ : nat → nat), ⊢ Δ → Δ ⊢r ρ : _ → Δ ⊢< _ > ρ ⋅ ?u ≡ ρ ⋅ ?v : _ |- _ ⊢< _ > ?r ⋅ ?u ≡ _ ⋅ ?v : _ =>
    eapply meta_conv_conv ; [
      eapply ih with (ρ := r) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        ren_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | |- _ => eauto with sidecond
  end.

Ltac typing_ren_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    econstructor ;
    ren_ih
  | eauto with sidecond
  ].

Ltac comp_rule :=
  first [
    eapply conv_cast_refl
  | eapply conv_cast_pi
  | eapply conv_beta
  | eapply conv_rec_zero
  | eapply conv_rec_succ
  | eapply conv_accel_accin
  ].

Ltac typing_ren_comp_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    eapply meta_rhs_conv ; [
      comp_rule ;
      ren_ih
    | eauto with sidecond
    ]
  | eauto with sidecond
  ].

Lemma typing_conversion_ren :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ∀ Δ ρ,
      ⊢ Δ →
      Δ ⊢r ρ : Γ →
      Δ ⊢< l > ρ ⋅ t : ρ ⋅ A
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ∀ Δ ρ,
      ⊢ Δ →
      Δ ⊢r ρ : Γ →
      Δ ⊢< l > ρ ⋅ u ≡ ρ ⋅ v : ρ ⋅ A).
Proof.
  apply typing_mutind.
  1, 22: solve [ intro ; cbn ; econstructor ; eauto using varty_ren ].
  all: try solve [
    intros ; try econstructor ; eauto with sidecond
  ].
  all: try solve [ typing_ren_tac ].
  all: try solve [ typing_ren_comp_tac ].
  - intros. cbn in *. rewrite closed_ren.
    2:{ eapply typing_closed. eassumption. }
    econstructor. all: eassumption.
  - typing_ren_tac.
    econstructor. 1: ren_ih.
    meta_conv. 1: eapply meta_lvl.
    { rasimpl. econstructor.
      all: ren_ih.
      - eauto 6 with sidecond.
      - eauto 6 with sidecond.
      - eauto 7 with sidecond.
    }
    all: destruct l. all: reflexivity.
  - intros. cbn in *. rewrite closed_ren.
    2:{ eapply typing_closed. eassumption. }
    econstructor. all: eassumption.
  - typing_ren_tac.
    econstructor. 1: ren_ih.
    meta_conv. 1: eapply meta_lvl.
    { econstructor. all: ren_ih.
      - eauto 6 with sidecond.
      - eauto 6 with sidecond.
      - eauto 7 with sidecond.
    }
    all: destruct l ; reflexivity.
  - typing_ren_comp_tac.
    repeat subst_def. rasimpl. f_equal. f_equal. f_equal. f_equal. f_equal.
    all: rasimpl. 1,2: reflexivity.
    f_equal.
    all: substify.
    all: apply ext_term.
    all: intros []. all: reflexivity.
  - (* eta *)
    intros ?????????????????? ih ? ρ **. cbn in *.
    eapply conv_eta. 3,4: ren_ih. 1,2: ren_ih. rasimpl. rasimpl in ih.
    eapply (ih _ (0 .: (ρ >> S))).
    1: econstructor; eauto.
    eauto with sidecond.
  - typing_ren_comp_tac.
    + rasimpl. f_equal. f_equal. f_equal.
      all: rasimpl. all: try reflexivity.
      all: substify. all: apply ext_term. all: intros [| []]. all: reflexivity.
    + rasimpl. apply ext_term. intros [].
    all: cbn. all: rasimpl. all: reflexivity.
  - typing_ren_comp_tac.
    + econstructor. 1: ren_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor. all: ren_ih.
        - eauto 6 with sidecond.
        - eauto 6 with sidecond.
        - eauto 7 with sidecond.
      }
      all: destruct l ; reflexivity.
    + repeat subst_def. rasimpl. f_equal. f_equal. f_equal.
      all: rasimpl. all: try reflexivity.
      all: f_equal.
      1,2: substify. 1,2: apply ext_term. 1,2: intros [] ; reflexivity.
      f_equal. 1-3: substify. 1-3: apply ext_term.
      1-3: intros [| []] ; reflexivity.
      f_equal. substify. apply ext_term. intros [| []] ; reflexivity.
Qed.

Lemma type_ren Γ l t A Δ ρ A' :
  Γ ⊢< l > t : A →
  ⊢ Δ →
  Δ ⊢r ρ : Γ →
  A' = ρ ⋅ A →
  Δ ⊢< l > ρ ⋅ t : A'.
Proof.
  intros h **. subst. eapply typing_conversion_ren in h. all: eauto.
Qed.

Lemma conv_ren Γ l t u A Δ ρ A' :
  Γ ⊢< l > t ≡ u : A →
  ⊢ Δ →
  Δ ⊢r ρ : Γ →
  A' = ρ ⋅ A →
  Δ ⊢< l > ρ ⋅ t ≡ ρ ⋅ u : A'.
Proof.
  intros h **. subst. eapply typing_conversion_ren in h ; eauto.
Qed.

Lemma ups_below k σ n :
  n < k →
  Nat.iter k up_term σ n = var n.
Proof.
  intro h.
  induction k as [| k ih] in n, σ, h |- *. 1: lia.
  cbn. destruct n as [| ].
  - reflexivity.
  - cbn. unfold ">>". unfold Nat.iter in ih. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma scoped_subst σ k t :
  scoped k t = true →
  t <[ Nat.iter k up_term σ ] = t.
Proof.
  intros h.
  induction t in k, σ, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ;
    rewrite ?Bool.andb_true_iff in * ;
    repeat change (up_term_term (Nat.iter ?k up_term ?σ)) with (Nat.iter (S k) up_term σ) ;
    intuition (f_equal ; eauto)
  ].
  cbn - ["<?"] in *.
  apply ups_below.
  apply Nat.ltb_lt. assumption.
Qed.

Corollary closed_subst σ t :
  closed t = true →
  t <[ σ ] = t.
Proof.
  intros h.
  eapply scoped_subst in h. eauto.
Qed.

#[export] Instance WellSubst_morphism :
  Proper (eq ==> eq ==> (`=1`) ==> iff) WellSubst.
Proof.
  intros Γ ? <- Δ ? <- σ σ' e.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| σ Δ l A h ih ho] in σ', e |- *.
  - constructor.
  - constructor.
    + eapply ih. intros x. unfold ">>". apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_WellSubst :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    Γ ⊢s r : Δ ↔ Γ ⊢s s : Δ.
Proof.
  intros Γ Δ r s H.
  apply WellSubst_morphism. 1,2: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_WellSubst : rasimpl_outermost.

Lemma well_scons_alt Γ Δ σ u l A :
  Γ ⊢s σ : Δ →
  Γ ⊢< l > u : A <[ σ ] →
  Γ ⊢s (u .: σ) : Δ ,, (l, A).
Proof.
  intros hs hu.
  constructor.
  - erewrite autosubst_simpl_WellSubst. 2: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma WellSubst_weak Γ Δ σ l A :
  Γ ⊢s σ : Δ →
  Γ ⊢< Ax l > A : Sort l →
  Γ ,, (l, A) ⊢s (σ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply meta_conv.
      * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
        1:econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.

Lemma WellSubst_weak_two Γ Δ σ l A l' B :
  Γ ⊢s σ : Δ →
  ⊢ Γ ,, (l, A) ,, (l', B) →
  Γ ,, (l, A) ,, (l', B) ⊢s (σ >> ren_term (S >> S)) : Δ.
Proof.
  intros.
  intros.  induction H.
  - econstructor.
  - econstructor. 1:ssimpl.  1: asimpl in IHWellSubst; eauto.
    ssimpl. eapply typing_conversion_ren in H1.
    1:eapply meta_conv. 1:eassumption.
    1:rasimpl; reflexivity.
    1:eauto.
    1: eapply WellRen_weak. eapply WellRen_S.
Qed.


Lemma WellSubst_weak_three Γ Δ σ l A l' B l'' C :
  Γ ⊢s σ : Δ →
  ⊢ Γ ,, (l, A) ,, (l', B) ,, (l'', C) →
  Γ ,, (l, A) ,, (l', B) ,, (l'', C) ⊢s (σ >> ren_term (S >> S >> S)) : Δ.
Proof.
  intros.  induction H.
  - econstructor.
  - econstructor. 1:ssimpl.  1: asimpl in IHWellSubst; eauto.
    ssimpl. eapply typing_conversion_ren in H1.
    1:eapply meta_conv. 1:eassumption.
    1:rasimpl; reflexivity.
    1:eauto.
    1: eapply WellRen_weak. 1:eapply WellRen_weak. eapply WellRen_S.
Qed.

Lemma WellSubst_up Γ Δ l A A' σ :
  Γ ⊢s σ : Δ →
  A' = A <[ σ ] →
  Γ ⊢< Ax l > A <[ σ ] : Sort l →
  Γ ,, (l, A') ⊢s up_term σ : Δ ,, (l, A).
Proof.
  intros. subst.
  constructor.
  - rasimpl. apply WellSubst_weak; assumption.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
   eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.


Lemma WellSubst_up_two Γ Δ σ l l' B A A' B' :
  Γ ⊢s σ : Δ →
  ⊢ Γ ,, (l, A <[ σ ]) ,, (l', B <[ up_term σ ]) ->
  A' = A <[ σ ] -> B' = B <[ up_term σ ] ->
  Γ ,, (l, A') ,, (l', B') ⊢s up_term (up_term σ) : Δ ,, (l, A) ,, (l', B).
Proof.
  intros. subst. dependent destruction H0.
  dependent destruction H0.
  econstructor. 1:econstructor.
  - rasimpl. eapply WellSubst_weak. 1:eapply WellSubst_weak.
    all:eauto.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
     eapply varty_meta.
    + constructor. constructor.
    + rasimpl. reflexivity.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
     eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.
(* 
Lemma WellSubst_up_two Γ Δ σ l l' B A :
  Γ ⊢s σ : Δ →
  Γ ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ⊢< Ax l'> B <[ σ ] : Sort l' ->
  Γ ,, (l, A <[ σ ]) ,, (l', S ⋅ (B <[ σ ])) ⊢s up_term (up_term σ) : Δ ,, (l, A) ,, (l', S ⋅ B).
Proof.
  intros.
  assert (Γ,, (l, A <[ σ]) ⊢< Ax l' > B <[ σ >> ren_term S] : Sort l').
  { eapply (type_ren _ _ _ _ _ S) in H1.
    1:rasimpl in H1; eassumption. 
    1:econstructor; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    rasimpl;reflexivity. }
  constructor.
  1:constructor.
  - rasimpl. eapply WellSubst_weak. 1:eapply WellSubst_weak.
    all:eauto.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
     eapply varty_meta.
    + constructor. constructor.
    + rasimpl. reflexivity.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
     eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity. *)
(* Qed. *)

Lemma varty_subst Γ Δ σ x l A :
  Γ ∋< l > x : A →
  Δ ⊢s σ : Γ →
  Δ ⊢< l > σ x : A <[ σ ].
Proof.
  intros hx hs.
  induction hs as [| σ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma WellSubst_meta Γ Γ' Δ Δ' σ :
  Γ ⊢s σ : Δ →
  Γ = Γ' →
  Δ = Δ' →
  Γ' ⊢s σ : Δ'.
Proof.
  intros ? -> ->. auto.
Qed.

Lemma WellSubst_ren Γ Δ ρ :
  Δ ⊢r ρ : Γ →
  ⊢ Δ →
  Δ ⊢s (ρ >> var) : Γ.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + eauto.
    + rasimpl. unfold ">>".
      econstructor. all: eassumption.
Qed.

Lemma WellSubst_compr Γ Δ Θ σ ρ :
  Δ ⊢s σ : Θ →
  Γ ⊢r ρ : Δ →
  ⊢ Γ →
  Γ ⊢s (σ >> ren_term ρ) : Θ.
Proof.
  intros hσ hρ hΓ.
  induction hσ as [| σ Θ i B h ih ho] in ρ, Γ, hΓ, hρ |- *.
  - constructor.
  - constructor.
    + eauto.
    + unfold ">>". meta_conv.
      { eapply type_ren. all: eauto. }
      rasimpl. reflexivity.
Qed.

Hint Resolve
  WellSubst_up WellSubst_weak well_scons_alt WellSubst_ren WellSubst_compr
  : sidecond.

Ltac subst_ih :=
  lazymatch goal with
  | |- _ ⊢< _ > _ ⋅ _ ⋅ _ : _ => rasimpl ; subst_ih
  | ih : ∀ (Δ : ctx) (σ : nat → term), ⊢ Δ → Δ ⊢s σ : _ → Δ ⊢< _ > ?t <[ σ ] : _ |- _ ⊢< _ > ?t <[ ?s ] : _ =>
    eapply meta_conv ; [
      eapply ih with (σ := s) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        subst_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | ih : ∀ (Δ : ctx) (σ : nat → term), ⊢ Δ → Δ ⊢s σ : _ → Δ ⊢< _ > ?u <[ σ ] ≡ ?v <[ σ ] : _ |- _ ⊢< _ > ?u <[ ?s ] ≡ ?v <[ _ ] : _ =>
    eapply meta_conv_conv ; [
      eapply ih with (σ := s) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        subst_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | |- _ => eauto with sidecond
  end.

(* Would have been cool, but too slow *)
(* Hint Extern 2000 (⊢ _ ,, _) => econstructor ; [| subst_ih] : sidecond. *)

Ltac typing_subst_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    econstructor ;
    subst_ih
  | eauto with sidecond
  ].

Ltac typing_subst_comp_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    eapply meta_rhs_conv ; [
      comp_rule ;
      subst_ih
    | eauto with sidecond
    ]
  | eauto with sidecond
  ].

(* A bit weird but well *)
Hint Resolve type_nat : sidecond.

Lemma typing_conversion_subst :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ∀ Δ σ,
      ⊢ Δ →
      Δ ⊢s σ : Γ →
      Δ ⊢< l > t <[ σ ] : A <[ σ ]
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ∀ Δ σ,
      ⊢ Δ →
      Δ ⊢s σ : Γ →
      Δ ⊢< l > u <[ σ ] ≡ v <[ σ ] : A <[ σ ]).
Proof.
  apply typing_mutind.
  22:{ intros. cbn. apply conv_refl. eauto using varty_subst. }
  all: try solve [ intros ; try econstructor ; eauto with sidecond ].
  all: try solve [ typing_subst_tac ].
  all: try solve [ typing_subst_comp_tac ].
  - intros. cbn. eauto using varty_subst.
  - intros. cbn in *. rewrite closed_subst.
    2:{ eapply typing_closed. eassumption. }
    econstructor. all: eassumption.
  - typing_subst_tac.
    eapply WellSubst_up. 1,2: eauto with sidecond.
    subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + rasimpl. eapply well_scons_alt.
      * eapply autosubst_simpl_WellSubst. 1: exact _.
        eapply well_scons_alt.
        -- eapply WellSubst_weak. 1: eauto with sidecond. subst_ih.
        -- econstructor. 2: eauto with sidecond.
          constructor. 1: auto with sidecond.
          subst_ih.
      * econstructor. 2: eauto with sidecond.
        econstructor. 1: eauto with sidecond.
        subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn. rasimpl.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply autosubst_simpl_WellSubst. 1: exact _.
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. rasimpl.
      econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih. eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
  - typing_subst_tac.
    symmetry. apply closed_subst.
    eapply typing_closed. eassumption.
  - typing_subst_tac.
    eapply WellSubst_up. all: eauto with sidecond.
    subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + econstructor. 1:{ rasimpl. subst_ih. }
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - rasimpl. subst_ih.
          unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - rasimpl. subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. cbn. rasimpl.
      econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - rasimpl. subst_ih.
          unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - rasimpl. subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
  - typing_subst_comp_tac.
    repeat subst_def. cbn. rasimpl. f_equal. f_equal.
    f_equal. f_equal. f_equal. all: rasimpl. all: reflexivity.
  - (* eta *)
    intros ?????????????????? ih ? σ **. cbn in *.
    eapply conv_eta. 3,4: subst_ih. 1,2: subst_ih.
    rasimpl. rasimpl in ih.
    specialize ih with (σ := up_term_term σ).
    cbn in ih. rasimpl in ih.
    eapply ih.
    1: econstructor; eauto.
    eauto with sidecond.
  - typing_subst_comp_tac.
    eapply WellSubst_up. all: eauto with sidecond.
    subst_ih.
  - typing_subst_comp_tac.
    eapply WellSubst_up. all: eauto with sidecond.
    subst_ih.
  - typing_subst_comp_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. cbn. rasimpl.
      econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
    + repeat subst_def. rasimpl. f_equal. f_equal. f_equal.
      all: rasimpl. all: reflexivity.
Qed.

Theorem subst_ty Γ l t A Δ σ A' :
  ⊢ Δ ->
  Δ ⊢s σ : Γ ->
  Γ ⊢< l > t : A ->
  A' = A <[ σ ] ->
  Δ ⊢< l > t <[ σ ] : A'.
Proof.
  intros. subst. eapply typing_conversion_subst in H1; eauto.
Qed.


Theorem subst_id Γ :
  ⊢ Γ ->
  Γ ⊢s var : Γ.
Proof.
  induction Γ as [| (l, A) Γ ih].
  - constructor.
  - constructor.
    + eapply WellSubst_weak with (A := A) in ih; eauto.
      all:inversion H; eauto.
    + constructor; eauto. rasimpl. constructor.
Qed.

Lemma subst_one Γ l A u :
  Γ ⊢< l > u : A →
  Γ ⊢s u .. : Γ ,, (l, A).
Proof.
  intros h.
  apply well_scons_alt.
  - apply subst_id; eauto using validity_ty_ctx.
  - rasimpl. assumption.
Qed.

Lemma WellSubst_conv Γ Δ Ξ σ :
  Γ ⊢s σ : Δ →
  ⊢ Δ ≡ Ξ →
  Γ ⊢s σ : Ξ.
Proof.
  intros hs hc.
  induction hs as [| σ Δ l A hs ih h ] in Ξ, hc |- *.
  - inversion hc. constructor.
  - inversion hc. subst.
    constructor.
    + eapply ih. assumption.
    + eapply type_conv.
      * eassumption.
      * eapply meta_conv_conv.
        { eapply typing_conversion_subst. all: eauto using validity_ty_ctx. }
        reflexivity.
Qed.


(* We show weaker versions of conv_in_ctx in which we require the assumption ⊢ Δ.
  Once we have validity, we then prove the real conv_in_ctx which drop this assumption. *)
Lemma pre_conv_in_ctx_ty Γ Δ t l A :
  Γ ⊢< l > t : A →
  ⊢ Δ ->
  ⊢ Δ ≡ Γ →
  Δ ⊢< l > t : A.
Proof.
  intros h h' hc.
  eapply typing_conversion_subst with (σ := var) in h.
  - rasimpl in h. eassumption.
  - assumption.
  - eapply WellSubst_conv. 2: eassumption.
    apply subst_id. assumption.
Qed.

Lemma pre_conv_in_ctx_conv Γ Δ u v l A :
  Γ ⊢< l > u ≡ v : A →
  ⊢ Δ ->
  ⊢ Δ ≡ Γ →
  Δ ⊢< l > u ≡ v : A.
Proof.
  intros h h' hc.
  eapply typing_conversion_subst with (σ := var) in h.
  - rasimpl in h. eassumption.
  - assumption.
  - eapply WellSubst_conv. 2: eassumption.
    apply subst_id. assumption.
Qed.

Lemma valid_varty Γ x A l :
  ⊢ Γ →
  Γ ∋< l > x : A →
  Γ ⊢< Ax l > A : Sort l.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ i B hΓ ih hB] in x, l, A, h |- *.
  1: inversion h.
  inversion h.
  - subst.
    eapply meta_conv.
    + eapply typing_conversion_ren. 3: eapply WellRen_S.
      1:eassumption. econstructor; eauto.
    + reflexivity.
  - subst.
    eapply meta_conv.
    + eapply typing_conversion_ren.
      2:econstructor; eauto.
    2: eapply WellRen_S.
      eapply ih. eassumption.
    + reflexivity.
Qed.

Lemma ctx_conv_refl Γ :
  ⊢ Γ →
  ⊢ Γ ≡ Γ.
Proof.
  induction 1 as [| Γ l A h ih hA].
  - constructor.
  - constructor. 1: assumption.
    apply conv_refl. assumption.
Qed.

#[export] Instance ConvSubst_morphism :
  Proper (eq ==> eq ==> (`=1`) ==> (`=1`) ==> iff) ConvSubst.
Proof.
  intros Γ ? <- Δ ? <- σ σ' e θ θ' e'.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  induction h as [| σ θ Δ l A h ih ho] in σ', e, θ', e' |- *.
  - constructor.
  - constructor.
    + eapply ih; unfold ">>". all: intro ; eauto.
    + rewrite <- e, <- e'. assumption.
Qed.

Lemma autosubst_simpl_ConvSubst :
  ∀ Γ Δ s1 s2 s3 s4,
    SubstSimplification s1 s2 →
    SubstSimplification s3 s4 →
    Γ ⊢s s1 ≡ s3 : Δ ↔ Γ ⊢s s2 ≡ s4 : Δ.
Proof.
  intros ?????? h1 h2.
  apply ConvSubst_morphism. 1,2: eauto.
  - apply h1.
  - apply h2.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_ConvSubst : rasimpl_outermost.

Lemma conv_scons_alt Γ Δ σ θ u v l A :
  Γ ⊢s σ ≡ θ : Δ →
  Γ ⊢< l > u ≡ v : A <[ σ ] →
  Γ ⊢s (u .: σ) ≡ (v .: θ) : Δ ,, (l, A).
Proof.
  intros hs hu.
  constructor.
  - erewrite autosubst_simpl_ConvSubst. 2,3: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma ConvSubst_weak Γ Δ σ θ l A :
  Γ ⊢s σ ≡ θ : Δ →
  Γ ⊢< Ax l > A : Sort l ->
  Γ ,, (l, A) ⊢s (σ >> ren_term S) ≡ (θ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ θ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply meta_conv_conv.
      * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
        1: econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.

Lemma conv_substs_up Γ Δ σ σ' l A :
  Γ ⊢s σ ≡ σ' : Δ →
  Γ ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ,, (l, A <[ σ ]) ⊢s up_term σ ≡ up_term σ' : Δ ,, (l, A).
Proof.
  intros h h'.
  apply conv_scons_alt.
  - apply ConvSubst_weak; assumption.
  - constructor. 
    1:eapply varty_meta.
    1:econstructor; eauto using validity_ty_ctx.
    1:rasimpl; reflexivity.
    constructor; eauto using validity_ty_ctx.
Qed.




Lemma conv_substs_up_two Γ Δ σ σ' l l' B A A' B' :
  Γ ⊢s σ ≡ σ' : Δ →
  ⊢ Γ ,, (l, A <[ σ ]) ,, (l', B <[ up_term σ ]) ->
  A' = A <[ σ ] -> B' = B <[ up_term σ ] ->
  Γ ,, (l, A') ,, (l', B') ⊢s up_term (up_term σ) ≡ up_term (up_term σ') : Δ ,, (l, A) ,, (l', B).
Proof.
  intros. subst. dependent destruction H0. dependent destruction H0.
  apply conv_scons_alt.
  - apply ConvSubst_weak. 1:eapply conv_substs_up; eauto. eauto.
  - constructor.
    1:eapply varty_meta.
    1:econstructor; eauto using validity_ty_ctx.
    1:rasimpl; reflexivity.
    constructor. 1:constructor; eauto using validity_ty_ctx. eauto.
Qed.

Theorem substs_id Γ :
  ⊢ Γ ->
  Γ ⊢s var ≡ var : Γ.
Proof.
  intros.
  induction Γ as [| (l, A) Γ ih].
  - constructor.
  - constructor.
    + inversion H. eapply ConvSubst_weak with (A := A) in ih.
      all:eassumption.
    + constructor. 
      1:eapply varty_meta. 1:econstructor.
      1:rasimpl;reflexivity.
      assumption.
Qed.

Lemma substs_one Γ l A u v :
  Γ ⊢< l > u ≡ v : A →
  Γ ⊢s u .. ≡ v .. : Γ ,, (l, A).
Proof.
  intros h.
  apply conv_scons_alt.
  - apply substs_id. eauto using validity_conv_ctx.
  - rasimpl. assumption.
Qed.

Lemma varty_conv_substs Γ Δ σ θ x l A :
  Γ ∋< l > x : A →
  Δ ⊢s σ ≡ θ : Γ →
  Δ ⊢< l > σ x ≡ θ x : A <[ σ ].
Proof.
  intros hx hs.
  induction hs as [| σ θ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma subst_conv_meta_conv_ctx Γ Δ σ τ Γ' :
  Γ ⊢s σ ≡ τ : Δ ->
  Γ = Γ' ->
  Γ' ⊢s σ ≡ τ : Δ.
Proof.
  intros. subst. assumption.
Qed.

Lemma subst_meta_conv_ctx Γ Δ σ Γ' :
  Γ ⊢s σ : Δ ->
  Γ = Γ' ->
  Γ' ⊢s σ : Δ.
Proof.
  intros. subst. assumption.
Qed.


Lemma conv_substs Γ Δ σ σ' t l A :
  ⊢ Δ ->
  Δ ⊢s σ ≡ σ' : Γ →
  Δ ⊢s σ : Γ →
  Γ ⊢< l > t : A →
  Δ ⊢< l > t <[ σ ] ≡ t <[ σ' ] : A <[ σ ].
Proof.
  intros h hs hst ht.
  induction ht in Δ, σ, σ', h, hs, hst |- *; cbn.
  all : try solve [ econstructor ; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty ].
  - eauto using varty_conv_substs.
  - eapply meta_conv_conv.
    + econstructor. all: eauto 9 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    + rewrite closed_subst; eauto using typing_closed.
  - eapply meta_conv_conv.
    1:try solve [ econstructor ; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty ].
    rasimpl; reflexivity.
  - assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
      by (eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up).
    eapply meta_conv_conv.
    + econstructor.
          all : try solve [ (eapply meta_conv_conv + eapply meta_conv) ; [
        eauto 12 using ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
  - assert (Δ ⊢< Ax i > A <[σ] : Sort i).
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (⊢ (Δ,, (i, A <[ σ])),, (i, (S ⋅ A) <[ up_term σ])).
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in H. 
      3:eapply WellRen_S. 1:rasimpl in H; eassumption. econstructor; eauto. } rasimpl in H0.
    eapply meta_conv_conv.
    1:econstructor; eauto.
    2:reflexivity.
    eapply IHht2; eauto.
    (* 1:rasimpl; eauto. *)
    2:eapply conv_substs_up_two; eauto.
    4:eapply WellSubst_up_two; eauto.
    all:rasimpl; eauto.
  - assert (Δ ⊢< Ax i > A <[σ] : Sort i).
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (⊢ (Δ,, (i, A <[ σ])),, (i, (S ⋅ A) <[ up_term σ])).
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in H. 
      3:eapply WellRen_S. 1:rasimpl in H; eassumption. econstructor; eauto. } rasimpl in H0.
    econstructor; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    2:eapply meta_conv_conv. 2:eapply IHht4; eauto.
    2:unfold R', acc_wk, R_wk, A_wk; rasimpl; reflexivity.
    eapply IHht2.
    2:eapply conv_substs_up_two; eauto.
    4:eapply WellSubst_up_two; eauto.
    all:rasimpl; eauto.
  - assert (Δ ⊢< Ax i > A <[σ] : Sort i).
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (⊢ (Δ,, (i, A <[ σ])),, (i, (S ⋅ A) <[ up_term σ])).
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in H. 
      3:eapply WellRen_S. 1:rasimpl in H; eassumption. econstructor; eauto. } rasimpl in H0.
    econstructor; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    1:eapply IHht2; eauto.
    2:eapply conv_substs_up_two; eauto.
    4:eapply WellSubst_up_two; eauto.
    6:eapply meta_conv_conv.
    6:eapply IHht6;eauto.
    all:rasimpl; eauto.
  - assert (Δ ⊢< Ax i > A <[σ] : Sort i).
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (⊢ (Δ,, (i, A <[ σ])),, (i, (S ⋅ A) <[ up_term σ])).
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in H. 
      3:eapply WellRen_S. 1:rasimpl in H; eassumption. econstructor; eauto. } rasimpl in H0.
    assert ((Δ,, (i, A <[ σ])),, (i, A <[ σ >> ren_term S]) ⊢< Ax prop > R <[ var 1 .: (var 0 .: σ >> ren_term (S >> S))] : Sort prop).
    { eapply typing_conversion_subst in ht2; simpl in ht2; rasimpl; eauto.
      1:econstructor. 1:econstructor.
      1:eapply WellSubst_weak_two; eauto.
      1:ssimpl. 1:eapply meta_conv. 1:econstructor.
      2:econstructor. 1:eauto. 1:rasimpl; reflexivity.
      1:eapply meta_conv. 1:econstructor.
      1:eauto. 1:econstructor. 1:econstructor. 1:rasimpl; reflexivity. }
    assert (⊢ (Δ,, (i, A <[ σ])),, (Ru i l, B <[ up_term σ])).
    { econstructor. 1:econstructor; eauto. unfold B. unfold R', P'.
      simpl. econstructor. 1:inversion H0; eauto.
      1:rasimpl;eauto.
      eapply meta_conv. 1:eapply meta_lvl. 1:eapply type_pi.
      3,4:destruct l;reflexivity.
      1:rasimpl; eauto.
      eapply typing_conversion_subst in ht3. 1:rasimpl. 1:simpl in ht3; eauto.
      1:econstructor; eauto. econstructor.
      2:ssimpl. 2:eapply meta_conv. 2:econstructor. 3:econstructor. 3:econstructor. 
      3:rasimpl; reflexivity. 2:econstructor; eauto.
      assert (↑ >> (var 1 .: σ >> ren_term (S >> (S >> S))) = σ >> ren_term (S >> (S >> S))). 1:ssimpl; reflexivity.
      1:eapply WellSubst_weak_three; eauto.
      1:econstructor; eauto. } 
    eapply meta_conv_conv.
    1:econstructor; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    2:eapply IHht2.
    3:eapply conv_substs_up_two; eauto.
    5:eapply WellSubst_up_two; eauto.
    1:eapply typing_conversion_subst in ht2; eauto. 
    2:eapply WellSubst_up_two; eauto.
    1-8,10:rasimpl; eauto.
    eapply meta_conv_conv.
    1:eapply IHht4.
    2:eapply conv_substs_up_two; eauto.
    3:eapply WellSubst_up_two; eauto.
    2-4: unfold B, P'', R', P'; rasimpl;reflexivity.
    unfold P'', B, R', P' in H2; rasimpl in H2; rasimpl.
    eauto.
  - eapply meta_conv_conv.
    + econstructor.
          all : try solve [ (eapply meta_conv_conv + eapply meta_conv) ; [
        eauto 8 using subst_ty, ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
  - eapply meta_conv_conv.
    1:try solve [ econstructor ; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty ].
    rasimpl; reflexivity.
  - eapply conv_conv. 1: eauto.
    eapply meta_conv_conv.
    + eapply typing_conversion_subst; eauto. all: eauto.
    + reflexivity.
Qed.


Theorem pre_subst_conv Γ l t u A Δ σ τ A' :
  ⊢ Δ →
  Δ ⊢s σ : Γ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Γ ⊢< l > t : A ->
  Γ ⊢< l > u : A ->
  Γ ⊢< l > t ≡ u : A ->
  A' = A <[ σ ] ->
  Δ ⊢< l > t <[ σ ] ≡ u <[ τ ] : A'.
Proof.
  intros hΔ hσ hστ ht hu htu ->.
  eapply conv_trans.
  - eapply typing_conversion_subst in htu. all: eauto.
  - eapply conv_substs; eauto.
Qed.


Lemma subst_id_reduce1 : pointwise_relation _ eq (var 0 .: (S >> var)) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a; reflexivity.
Qed.

Lemma subst_id_reduce2 : pointwise_relation _ eq (var 0 .: (var 1 .: (S >> (S >> var)))) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a. 1:reflexivity. destruct a. 1:reflexivity. reflexivity.
Qed.

Section AccCompValidity.

  Context (Γ : ctx) (i : level) (A R : term) 
    (AWt : Γ ⊢< Ax i > A : Sort i)
    (RWt : Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop).
  Let R0 := (1 .: (0 .: (S >> S))) ⋅ R.

  Lemma R0Wt : Γ,, (i, A),, (i, S ⋅ A) ⊢< Ax prop > R0 : Sort prop.
  Proof.
    unfold R0.
    eapply type_ren; eauto using validity_ty_ctx.
    econstructor. 1:econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. rasimpl; reflexivity.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl;reflexivity.
  Qed.

  Context (l : level) (P : term) (PWt : Γ ,, (i, A) ⊢< Ax l > P : Sort l).  
  Let P0 := (1 .: (S >> S >> S)) ⋅ P.
  Let B := Pi i l (S ⋅ A) (Pi prop l R0 P0).
  Let P00 := (1.: (S >> S)) ⋅ P.

  Lemma P0Wt : Γ,, (i, A),, (i, S ⋅ A),, (prop, R0) ⊢< Ax l > P0 : Sort l.
  Proof.
    unfold P0.
    eapply type_ren;eauto.
    1:econstructor; eauto using validity_ty_ctx, R0Wt.
    1:econstructor. 
    - ssimpl. eapply WellRen_weak, WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Lemma BWt : Γ,, (i, A)⊢< Ax (Ru i l) > B : Sort (Ru i l).
  Proof.
    unfold B.
    econstructor.
    1:eapply type_ren; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    1:eapply meta_lvl. 1:eapply meta_conv.
    1:econstructor; eauto using R0Wt, P0Wt.
    all: destruct l; reflexivity.
  Qed.

  Lemma P00Wt : Γ ,, (i, A) ,, (Ru i l, B) ⊢< Ax l > P00 : Sort l.
  Proof.
    unfold P00.
    eapply type_ren; eauto.
    1:econstructor; eauto using validity_ty_ctx, BWt.
    econstructor. 
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl. reflexivity.
  Qed.

  Context (p a q : term)
    (pWt : Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P00)
    (aWt : Γ ⊢< i > a : A)
    (qWt : Γ ⊢< prop > q : acc i A R a).
  Let Awk := (S >> S) ⋅ A.
  Let Rwk := (up_ren (up_ren (S >> S))) ⋅ R.
  Let Pwk := (up_ren (S >> S)) ⋅ P.
  Let pwk := (up_ren (up_ren (S >> S))) ⋅ p.
  Let t0 := accinv i Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0).
  Let t1 := accel i l Awk Rwk Pwk pwk (var 1) t0.
  Let t2 := R<[S ⋅ a .: (var 0 .: S >> var)].
  Let t3 := lam prop l t2 P00 t1.
  Let t4 := Pi prop l t2 P00.
  Let t5 := lam i l A t4 t3.

  Lemma t2Wt : Γ ,, (i, A) ⊢< Ax prop > t2 : Sort prop.
  Proof.
    unfold t2.
    eapply subst_ty; eauto using validity_ty_ctx.
    econstructor. 
    1:econstructor.
    - ssimpl. change (S >> var) with (var >> ren_term S). eapply WellSubst_weak; eauto using subst_id, validity_ty_ctx.
    - ssimpl. eapply meta_conv. 1:econstructor. 2:econstructor. 1:eauto using validity_ty_ctx. rasimpl. reflexivity.
    - ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx. 1:eapply WellRen_S. rasimpl. reflexivity.
  Qed.


  Lemma AwkWt : Γ ,, (i, A) ,, (prop, t2) ⊢< Ax i > Awk : Sort i.
  Proof.
    unfold Awk.
    eapply type_ren; eauto using validity_ty_ctx.
    1:econstructor; eauto using validity_ty_ctx, t2Wt.
    eapply WellRen_weak, WellRen_S.
  Qed.

  Lemma RwkWt : Γ ,, (i, A) ,, (prop, t2),, (i, Awk) ,, (i, S ⋅ Awk) ⊢< Ax prop > Rwk : Sort prop.
  Proof.
    unfold Rwk, Awk.
    eapply type_ren; eauto.
    1:econstructor. 1:econstructor. 2:fold Awk. 1,2:eauto using validity_ty_ctx, AwkWt.
    1:ssimpl. 1:eapply type_ren; eauto. 1:econstructor. 2:fold Awk. 1,2:eauto using validity_ty_ctx, AwkWt.
    1:eapply WellRen_weak, WellRen_weak, WellRen_S.
    eapply WellRen_up. 1:eapply WellRen_up. 1:eapply WellRen_weak, WellRen_S. all:rasimpl; reflexivity.
  Qed.

  Lemma PwkWt : Γ ,, (i, A) ,, (prop, t2),, (i, Awk) ⊢< Ax l > Pwk : Sort l.
  Proof.
    unfold Pwk, Awk.
    eapply type_ren; eauto.
    1:econstructor. 2:fold Awk. 1,2:eauto using validity_ty_ctx, AwkWt.
    eapply WellRen_up. 1:eapply WellRen_weak, WellRen_S. reflexivity.
  Qed.

  Lemma pwkWt : Γ ,, (i, A) ,, (prop, t2) ,, (i, Awk) ,, (Ru i l, (up_ren (S >> S)) ⋅ B) ⊢< l > pwk : (up_ren (up_ren (S >> S))) ⋅ P00.
  Proof.
    unfold pwk, Awk. eapply type_ren; eauto.
    1:econstructor; eauto using PwkWt, validity_ty_ctx.
    1:eapply type_ren; eauto using BWt, validity_ty_ctx, PwkWt.
    1:eapply WellRen_up.
    1:eapply WellRen_weak, WellRen_S.
    1:reflexivity.
    1:eapply WellRen_up. 1:eapply WellRen_up.
    1:eapply WellRen_weak, WellRen_S.
    all: ssimpl; reflexivity.
  Qed.

  Lemma t0Wt : Γ ,, (i, A) ,, (prop, t2) ⊢< prop > t0 : acc i Awk Rwk (var 1).
  Proof.
    unfold t0.
    econstructor; eauto using AwkWt, RwkWt, PwkWt.
    - eapply type_ren; eauto using WellRen_weak, WellRen_S, AwkWt, validity_ty_ctx.
    - eapply type_ren; eauto using WellRen_weak, WellRen_S, AwkWt, validity_ty_ctx.
    - econstructor; eauto using AwkWt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:econstructor. 1:unfold Awk; rasimpl; reflexivity.
    - econstructor; eauto using AwkWt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:unfold Rwk, t2; rasimpl; simpl; reflexivity.
  Qed.

  Lemma t1Wt : Γ ,, (i, A) ,, (prop, t2) ⊢< l > t1 : Pwk <[ (var 1) .. ].
  Proof.
    unfold t1.
    econstructor; eauto using AwkWt, RwkWt, PwkWt, t0Wt.
    - assert (Pi i l (S ⋅ Awk) (Pi prop l ((1 .: (0 .: S >> S)) ⋅ Rwk) ((1 .: (S >> S) >> S) ⋅ Pwk)) = (up_ren (S >> S)) ⋅ B).
      1: {unfold B, Awk, Rwk, Pwk, R0, P0. rasimpl. reflexivity. }
      rewrite H; eapply meta_conv.
      1: eapply pwkWt. unfold P00, Pwk; rasimpl; reflexivity.
    - econstructor; eauto using t0Wt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:econstructor. unfold Awk; rasimpl; reflexivity.
  Qed.

  Lemma P00Wt2 : (Γ,, (i, A)),, (prop, t2) ⊢< Ax l > P00 : Sort l.
  Proof.
    unfold P00. eapply type_ren; eauto using t1Wt, validity_ty_ctx.
    econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Lemma t3Wt : Γ ,, (i, A) ⊢< l > t3 : Pi prop l t2 P00.
  Proof. 
    unfold t3. eapply meta_lvl.
    1:econstructor; eauto using t2Wt, P00Wt2.
    1:eapply meta_conv. 1:eapply t1Wt.
    1:unfold Pwk, P00; substify; ssimpl; reflexivity.
    destruct l; eauto.
  Qed.

  Lemma t4Wt : Γ ,, (i, A) ⊢< Ax l > t4 : Sort l.
  Proof.
    unfold t4. eapply meta_conv. 1:eapply meta_lvl.
    1:econstructor; eauto using t2Wt, P00Wt2.
    all:destruct l; reflexivity.
  Qed.
  
  Lemma t5Wt : Γ ⊢< Ru i l > t5 : Pi i l A t4.
  Proof.
    unfold t5. econstructor; eauto using t3Wt, t4Wt.
  Qed.

  Context (A' : term) (A'Wt : Γ ⊢< Ax i > A' : Sort i) (A_conv_A' : Γ ⊢< Ax i > A ≡ A' : Sort i).

  Lemma Γ_A_SA' : ⊢ Γ ,, (i, A') ,, (i, S ⋅ A').
  Proof.
    econstructor. 1:econstructor; eauto using validity_ty_ctx.
    eapply type_ren; eauto. 1:econstructor; eauto using validity_ty_ctx.
    eapply WellRen_S.
  Qed.


  Lemma Γ_A_SA_conv : ⊢ Γ ,, (i, A') ,, (i, S ⋅ A') ≡ Γ ,, (i, A) ,, (i, S ⋅ A).
  Proof.
    econstructor. 1:econstructor; eauto using ctx_conv_refl, validity_ty_ctx, conv_sym.
    eapply conv_ren; eauto using validity_ty_ctx, conv_sym. 2: eapply WellRen_S.
    econstructor; eauto using validity_ty_ctx.
  Qed.

  Context (R' : term) (R_conv_R' : Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop).
  Context (P' : term) (P_conv_P' : Γ ,, (i, A) ⊢< Ax l > P ≡ P' : Sort l).
  Let R0' := (1 .: (0 .: (S >> S))) ⋅ R'.
  Let P0' := (1 .: (S >> S >> S)) ⋅ P'.
  Let B' := Pi i l (S ⋅ A') (Pi prop l R0' P0').
  Let P00' := (1.: (S >> S)) ⋅ P'.


  Lemma R0_conv_R0' : Γ,, (i, A),, (i, S ⋅ A) ⊢< Ax prop > R0 ≡ R0' : Sort prop.
  Proof.
    unfold R0.
    eapply conv_ren; eauto using validity_ty_ctx.
    econstructor. 1:econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. rasimpl; reflexivity.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl;reflexivity.
  Qed.

  Lemma P0_conv_P0' : Γ,, (i, A),, (i, S ⋅ A),, (prop, R0) ⊢< Ax l > P0 ≡ P0' : Sort l.
  Proof.
    unfold P0.
    eapply conv_ren;eauto.
    1:econstructor; eauto using validity_ty_ctx, R0Wt.
    1:econstructor. 
    - ssimpl. eapply WellRen_weak, WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Lemma B_conv_B' : Γ,, (i, A)⊢< Ax (Ru i l) > B ≡ B' : Sort (Ru i l).
  Proof.
    unfold B.
    econstructor.
    1:eapply type_ren; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    1:eapply conv_ren; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    eapply meta_lvl_conv. 1:eapply meta_conv_conv.
    1:econstructor; eauto using R0_conv_R0', P0_conv_P0', R0Wt.
    all: destruct l; reflexivity.
  Qed.

  Lemma P00_conv_P00' : Γ ,, (i, A) ,, (Ru i l, B) ⊢< Ax l > P00 ≡ P00' : Sort l.
  Proof.
    unfold P00.
    eapply conv_ren; eauto using validity_ty_ctx.
    econstructor. 
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl. reflexivity.
  Qed.

  (* Lemma Γ_A_B' : ⊢ Γ ,, (i, A') ,, (Ru i l, B').
  Proof.
    econstructor. 1:econstructor; eauto using validity_ty_ctx.

    eapply BWt. *)

  Lemma Γ_A_B_conv : ⊢ Γ ,, (i, A') ,, (Ru i l, B') ≡ Γ ,, (i, A) ,, (Ru i l, B).
  Proof.
    econstructor. 1:econstructor.
    all:eauto using A_conv_A', B_conv_B', ctx_conv_refl, validity_ty_ctx, conv_sym, pre_conv_in_ctx_conv.
    eapply pre_conv_in_ctx_conv; eauto using conv_sym, B_conv_B'.
    1:econstructor; eauto using validity_ty_ctx.
    econstructor; eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
  Qed.


End AccCompValidity.

Lemma meta_tm_conv Γ l t t' A : 
  Γ ⊢< l > t : A ->
  t = t' ->
  Γ ⊢< l > t' : A.
Proof.
  intros. subst. eauto.
Qed.

Lemma meta_ctx Γ l t A Γ' : 
  Γ ⊢< l > t : A ->
  Γ = Γ' ->
  Γ' ⊢< l > t : A.
Proof.
  intros. subst. eauto.
Qed.

Lemma meta_ctx_conv Γ Γ' Δ Δ' : 
  ⊢ Γ ≡ Δ ->
  Γ = Γ' ->
  Δ = Δ' ->
  ⊢ Γ' ≡ Δ'.
Proof.
  intros. subst. eauto.
Qed.


Lemma validity_gen :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    Γ ⊢< Ax l > A : Sort l
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    Γ ⊢< l > u : A ∧ Γ ⊢< l > v : A).
Proof.
  apply typing_mutind.
  all: try solve [ intros ; econstructor ; eauto using validity_ty_ctx, validity_conv_ctx].
  all: try solve [
    intros ; try econstructor ; try econstructor ; intuition eauto using validity_ty_ctx, validity_conv_ctx
  ].
  all:try solve [ intros ; intuition eauto 6 using conversion, typing].
  all: try solve [ intuition eauto using subst_ty, subst_one, validity_ty_ctx, conversion, typing, validity_ty_ctx, subst_one, valid_varty].
  all:intros.
  - eapply typing_conversion_ren in t as temp; eauto. 2:econstructor. Unshelve. 2:exact (fun _ => 0).
    rewrite closed_ren in temp; eauto using typing_closed.
  - eapply meta_lvl. 1:eapply type_sort. all:eauto.
  - econstructor. 1:eapply type_sort; eauto using validity_ty_ctx.
    all:eapply subst_ty; eauto.
    all:eauto using validity_ty_ctx, subst_one.
    eapply subst_one; eauto.
    unfold a1. eapply type_cast; eauto.
    eapply type_injpi1; eauto.
  - split ; econstructor. all: intuition eauto.
    eapply pre_conv_in_ctx_ty. all: eauto using ctx_typing, validity_ty_ctx, ctx_conv_refl, conv_ccons, conv_sym.
  - split.
    + econstructor. all: intuition eauto.
    + econstructor.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 9 using pre_conv_in_ctx_ty, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing, validity_ty_ctx.
        eapply pre_conv_in_ctx_ty.
        - eapply type_conv. all: intuition eauto.
        - econstructor; eauto using validity_ty_ctx.
        - econstructor; eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      }
      * apply conv_sym. constructor.
        all: intuition eauto.
  - split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 8 using type_conv, pre_conv_in_ctx_ty, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing, validity_ty_ctx.
        eapply type_conv. 1: intuition eauto.
        constructor. all: intuition eauto.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one, validity_ty_ctx.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto using validity_ty_ctx.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }
  - split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. all: intuition eauto.
        - eapply type_conv. 1: intuition eauto.
          eapply meta_conv_conv.
          + eapply typing_conversion_subst. 1,2: intuition eauto using validity_ty_ctx.
            eapply well_scons_alt.
            * apply subst_id. eauto using validity_ty_ctx.
            * cbn. constructor. eauto using validity_ty_ctx.
          + reflexivity.
        - eapply pre_conv_in_ctx_ty.
          + eapply type_conv. 1: intuition eauto.
            eapply meta_conv_conv.
            * {
              eapply typing_conversion_subst. 1: intuition eauto.
              1:econstructor; eauto using validity_ty_ctx.
              eapply well_scons_alt.
              - change (↑ >> (↑ >> var)) with (var >> ren_term S >> ren_term S).
                eapply WellSubst_weak.
                1:eapply WellSubst_weak.
                1:apply subst_id; eauto using validity_ty_ctx.
                1,2:eauto using typing, validity_ty_ctx.
              - cbn. constructor.
                eapply meta_conv.
                + repeat constructor. all:eauto using validity_ty_ctx.
                + reflexivity.
            }
            * reflexivity.
          + constructor. 1: eauto using ctx_conv_refl, validity_ty_ctx. eauto.
          + econstructor; eauto using ctx_conv_refl, conv_sym, validity_ty_ctx.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one, validity_ty_ctx.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto using validity_conv_ctx.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }
  - split; econstructor; intuition eauto using type_conv.
    eapply pre_conv_in_ctx_ty; eauto.
    1:econstructor. 1:econstructor. 
    4:econstructor. 4:econstructor.
    all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
    1:eapply type_ren; eauto using WellRen_S.
    2:eapply conv_ren; eauto using WellRen_S, conv_sym.
    all:econstructor; eauto using validity_ty_ctx.
  - assert (⊢ (Γ,, (i, A')),, (i, S ⋅ A')).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      1:eapply type_ren; eauto using WellRen_S. econstructor; eauto using validity_ty_ctx. } 
    assert (⊢ (Γ,, (i, A')),, (i, S ⋅ A') ≡ (Γ,, (i, A)),, (i, S ⋅ A)).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      eapply conv_ren; eauto using WellRen_S, conv_sym.
      econstructor; eauto using validity_ty_ctx. } 
    assert (⊢ Γ,, (i, A)) by (econstructor; eauto using validity_ty_ctx).
    assert (Γ,, (i, A) ⊢s (S ⋅ a .: (var 0 .: S >> var)) : (Γ,, (i, A)),, (i, S ⋅ A)).
    { intuition eauto. econstructor.
      2:ssimpl. 2:eapply type_ren; eauto.
      1:ssimpl; rewrite subst_id_reduce1; eapply subst_id; econstructor; eauto using validity_ty_ctx.
      1,2:rasimpl; eauto using WellRen_S. } 
    assert (Γ,, (i, A) ⊢< Ax prop > RR : Sort prop).
    { intuition eauto. unfold RR. eapply subst_ty; eauto. } 
    assert (⊢ (Γ,, (i, A)),, (prop, RR)).
    { econstructor; eauto. }
    split.
    1:econstructor.
    5:eapply type_conv. 5:econstructor.
    all: intuition eauto using type_conv.
    3:econstructor; eauto using conv_conv, conv_sym. 
    1:eapply pre_conv_in_ctx_ty; eauto.
    2:eapply pre_conv_in_ctx_conv; eauto using conv_sym.
    eapply type_conv; eauto.
    eapply meta_lvl_conv. 1:econstructor.
    1,2:eauto.
    2:eauto.
    eapply meta_lvl_conv. 1:econstructor; eauto.
    1:unfold RR.
    1:eapply pre_subst_conv; eauto.
    1:rewrite subst_id_reduce1.
    1:eapply substs_one. 1:eapply conv_ren; eauto using WellRen_S.
    2:eauto.
    unfold acc_wk, A_wk, R_wk.
    econstructor.
    4:eapply meta_conv_conv.
    4:econstructor;eauto. 4:econstructor. 4:econstructor.
    4:rasimpl; eauto.
    1:eapply type_ren; eauto.
    2:eapply conv_ren; eauto.
    1,2:eapply WellRen_weak; eapply WellRen_S.
    eapply conv_ren; eauto.
    2:eapply WellRen_up. 2: eapply WellRen_up.
    2:eapply WellRen_weak; eapply WellRen_S.
    2,3:rasimpl;reflexivity.
    econstructor. 1:econstructor; eauto.
    1:eapply type_ren; eauto.
    1:eapply WellRen_weak, WellRen_S.
    rasimpl.
    eapply type_ren; eauto.
    1:econstructor; eauto.
    1:eapply type_ren; eauto. 1:eapply WellRen_weak, WellRen_S.
    eapply WellRen_weak. eapply WellRen_weak. eapply WellRen_S.
  - assert (⊢ (Γ,, (i, A')),, (i, S ⋅ A')).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      1:eapply type_ren; eauto using WellRen_S. econstructor; eauto using validity_ty_ctx. } 
    assert (⊢ (Γ,, (i, A')),, (i, S ⋅ A') ≡ (Γ,, (i, A)),, (i, S ⋅ A)).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      eapply conv_ren; eauto using WellRen_S, conv_sym.
      econstructor; eauto using validity_ty_ctx. } 
    assert (⊢ Γ,, (i, A)) by (econstructor; eauto using validity_ty_ctx).
    assert (Γ,, (i, A) ⊢s (S ⋅ a .: (var 0 .: S >> var)) : (Γ,, (i, A)),, (i, S ⋅ A)).
    { intuition eauto. econstructor.
      2:ssimpl. 2:eapply type_ren; eauto.
      1:ssimpl; rewrite subst_id_reduce1; eapply subst_id; econstructor; eauto using validity_ty_ctx.
      1,2:rasimpl; eauto using WellRen_S. } 
    split.
    1:econstructor.
    5:eapply type_conv. 5:econstructor.
    all: intuition eauto using type_conv, conv_sym.
    eapply type_conv. 1:econstructor; eauto using type_conv.
    4:econstructor; eauto using conv_sym, conv_conv.
    2:eapply type_conv. 2:eauto.
    2:econstructor; eauto.
    1:eapply pre_conv_in_ctx_ty; eauto.
    2:eapply pre_conv_in_ctx_conv; eauto using conv_sym.
    eapply type_conv; eauto.
    eapply pre_subst_conv; eauto using validity_ty_ctx.
    1:econstructor. 1:ssimpl. 1:eapply subst_one.
    2:rasimpl; simpl. 1,2:eauto.
    econstructor. 1:rasimpl; eapply substs_one.
    2:rasimpl;simpl. 1,2:eauto.
  - intuition eauto. 1:econstructor; eauto.
    eapply type_conv. 1:econstructor; eauto using type_conv.
    4:eapply type_conv; eauto. 4:econstructor; eauto.
    4:eapply pre_subst_conv; eauto using validity_ty_ctx, conv_sym.
    4:eapply subst_one; eauto.
    4:eapply substs_one; eauto using conv_sym.
    2:eapply pre_conv_in_ctx_ty; eauto.
    1:eapply pre_conv_in_ctx_ty; eauto.
    1,2:econstructor.
    1,3,5,6:econstructor; eauto using conv_sym, validity_ty_ctx, ctx_conv_refl.
    1:eapply type_ren; eauto. 3:eapply conv_ren; eauto using conv_sym.
    1,3:econstructor; eauto using validity_ty_ctx.
    1,2:eapply WellRen_S.
    eapply type_conv. 1: eapply pre_conv_in_ctx_ty; eauto.
    * econstructor. 1:econstructor; eauto using validity_ty_ctx.
      eapply BWt; eauto.
      1:eapply pre_conv_in_ctx_ty; eauto. 
      2:eauto using Γ_A_SA_conv. 1:eapply Γ_A_SA'; eauto.
      eapply pre_conv_in_ctx_ty; eauto.
      1:econstructor; eauto using validity_ty_ctx.
      econstructor; eauto using conv_sym, ctx_conv_refl ,validity_ty_ctx.
    * eapply meta_ctx_conv. 1:eapply Γ_A_B_conv. 8:exact c. 8:exact c0. 8:exact c1.
      all:eauto.
    * eapply pre_conv_in_ctx_conv.
      1:unfold P''. 1:eapply conv_ren; eauto.
      Unshelve. 5:exact ((Γ,, (i, A)),, (Ru i l, B)).
      1:eauto using validity_ty_ctx.
      1:econstructor. 
      1:ssimpl; eapply WellRen_weak, WellRen_S.
      1: ssimpl; eapply varty_meta.
      1:econstructor. 1:econstructor.
      1:rasimpl;reflexivity.
      2:eapply Γ_A_B_conv; eauto.
      econstructor. 1:econstructor; eauto using validity_ty_ctx.
      eapply BWt; eauto.
      all:eapply pre_conv_in_ctx_ty.
      1,4:eauto.
      all:eauto using Γ_A_SA_conv, Γ_A_SA'.
      1:econstructor; eauto using validity_ty_ctx.
      econstructor; eauto using ctx_conv_refl, conv_sym, validity_ty_ctx.
  - destruct H0, H1, H2, H3, H4, H5. split.
    + eapply type_J; eauto.
    + eapply type_conv. 1:eapply type_J; eauto using type_conv, conv_obseq.
      1:eapply pre_conv_in_ctx_ty; eauto using ctx_typing, validity_ty_ctx, conv_ccons, ctx_conv_refl, conv_sym.
      1:eapply type_conv; eauto.
      1,2: eapply pre_subst_conv; eauto using subst_one, validity_ty_ctx, substs_one, conv_sym.
  - intuition eauto.
    1:econstructor.
    5: eapply type_conv. 5:econstructor.
    all:eauto using type_conv, conv_sym.
    eapply type_conv; eauto.
    econstructor; eauto using conversion, validity_ty_ctx.
  - intuition eauto.
    1:econstructor.
    6:eapply type_conv.
    6:econstructor.
    all:eauto.
    1,2:eapply pre_conv_in_ctx_ty; eauto.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
    1:eapply type_conv; eauto.
    1,2:econstructor; eauto using conv_sym, conversion, validity_ty_ctx.
  - intuition eauto.
    1:econstructor.
    7:eapply type_conv.
    7:econstructor.
    all:eauto using conv_sym, type_conv.
    1,2:eapply pre_conv_in_ctx_ty; eauto.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
    1:eapply type_conv; eauto.
    all:unfold a1.
    1,2:econstructor; eauto using conv_sym, conversion, validity_ty_ctx.
    all:eapply pre_subst_conv; eauto using conv_sym, validity_ty_ctx, subst_one, substs_one.
    1:eapply subst_one.
    2:eapply substs_one.
    2: { eapply conv_conv. 1:econstructor; eauto using conv_sym, conv_conv.
    1:econstructor; eauto using conv_sym.  
    1,2:eapply pre_conv_in_ctx_conv; eauto using conv_sym.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.   
    1:eapply conv_conv; eauto using conv_sym.
    1:econstructor. 
    2,3:econstructor.
    all:eauto using conversion, validity_ty_ctx. } 
    eapply type_conv.
    1:econstructor; eauto using type_conv. 2:eauto using conv_sym.
    econstructor; eauto.
    1,2:eapply pre_conv_in_ctx_ty; eauto using conv_sym.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
    eapply type_conv; eauto.
    econstructor; eauto using conv_sym, conversion, validity_ty_ctx. 
  - intuition eauto. 
    * econstructor. 
      1,2:econstructor; eauto.
      all: eauto.
    * unfold t8.
      econstructor; eauto.
      unfold t7.
      assert (Γ ,, (i, A2) ⊢< i > t5 : S ⋅ A1).
      { unfold t5. unfold A1'.
        econstructor. 
        ** unfold A2'. eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx. 
        ** eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** econstructor.
           1-4:eapply type_ren; eauto using WellRen_S.
           1,2,4,5:econstructor; eauto using validity_ty_ctx.
           1,2:eapply type_ren; eauto using WellRen_S.
           1,2:econstructor; eauto using validity_ty_ctx.
           1,2:eapply WellRen_up; eauto using WellRen_S.
           eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** eapply meta_conv. 1:econstructor. 2:econstructor.           
           1:econstructor; eauto using validity_ty_ctx.
           unfold A2'; eauto. } 
      econstructor; eauto.
      1:eapply subst_ty; eauto.
      1:econstructor; eauto using validity_ty_ctx.
      1:econstructor. 2:ssimpl; renamify; eauto.
      
      1:ssimpl. 
      3: {  unfold t6. 1:eapply meta_conv.
        1:econstructor; eauto. 4:unfold B1'; rasimpl; reflexivity.
        1,2:unfold A1', B1'.
        all:eapply type_ren; eauto using WellRen_S.
        1,2,4:econstructor; eauto using validity_ty_ctx.
        1:eapply type_ren; eauto using WellRen_S.
        1:econstructor; eauto using validity_ty_ctx.
        eapply WellRen_up; eauto using WellRen_S. }
      2:{ eapply meta_conv.
       1:econstructor.
       7:unfold B1', t5; rasimpl.
       7:f_equal. 7:unfold B2';rasimpl.
       7:setoid_rewrite subst_id_reduce1; rasimpl; reflexivity.
       6:eapply meta_conv. 6:econstructor. 7:econstructor.
       6:econstructor; eauto using validity_ty_ctx. 6:unfold A2'; reflexivity.
       all:unfold A1', B1'.
       all:eapply type_ren; eauto using WellRen_S.
       3,6:eapply WellRen_up; eauto.
       3,4:eapply WellRen_S.
       2,4:econstructor.
       3,5:unfold A2'; eapply type_ren; eauto using WellRen_S.
       all:econstructor; eauto using validity_ty_ctx. } 

      change (S >> var) with (var >> ren_term S).
      eapply WellSubst_weak; eauto using subst_id, validity_ty_ctx.
  - split.
    + econstructor. all: intuition eauto.
      econstructor. auto.
    + eapply meta_conv.
      { eapply typing_conversion_subst.
        - eauto using validity_ty_ctx.
        - eauto using validity_ty_ctx.
        - eapply well_scons_alt.
          + apply subst_one. assumption.
          + econstructor. all: intuition eauto.
      }
      rasimpl. reflexivity.
  - intuition eauto. 1:econstructor; eauto. 
    eapply subst_ty; eauto using validity_ty_ctx.
    2:unfold P''; rasimpl; reflexivity.
    econstructor. 1:econstructor.
    + ssimpl. eapply subst_id; eauto using validity_ty_ctx.
    + ssimpl. eauto.
    + ssimpl. unfold B. rasimpl.
      eapply meta_tm_conv. 1:eapply meta_conv.
      1: eapply t5Wt; eauto.
      * unfold R', P'. ssimpl. f_equal. f_equal. substify. ssimpl. reflexivity.
      * unfold t10, t9, t8, t7. f_equal. 
Qed.

Theorem validity_conv_left Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  Γ ⊢< l > t : A.
Proof.
  intros. eapply validity_gen in H as (H1 & H2); eauto.
Qed.

Theorem validity_conv_right Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  Γ ⊢< l > u : A.
Proof.
  intros. eapply validity_gen in H as (H1 & H2); eauto.
Qed.

Theorem validity_ty_ty Γ l t A :
  Γ ⊢< l > t : A ->
  Γ ⊢< Ax l > A : Sort l.
Proof.
  intros.
  eapply validity_gen in H. assumption.
Qed.

Lemma validity_subst_conv_left Δ Γ σ τ :
  Δ ⊢s σ ≡ τ : Γ ->
  Δ ⊢s σ : Γ.
Proof.
  intros. induction H; eauto using validity_conv_left, WellSubst.
Qed.

Lemma subst_sym Δ Γ σ τ :
  ⊢ Δ ->
  ⊢ Γ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Δ ⊢s τ ≡ σ : Γ.
Proof.
  intros. induction H1; eauto using ConvSubst.
  econstructor; dependent destruction H0; eauto.
  eapply conv_sym. eapply conv_conv. 1:eauto.
  eapply conv_substs in H1; eauto using validity_subst_conv_left.
  eauto.
Qed.


Lemma validity_subst_conv_right Δ Γ σ τ :
  ⊢ Δ ->
  ⊢ Γ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Δ ⊢s τ : Γ.
Proof.
  intros. eapply subst_sym in H1; eauto. eapply validity_subst_conv_left; eauto.
Qed.




Theorem subst_conv Γ l t u A Δ σ τ A' :
  ⊢ Δ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Γ ⊢< l > t ≡ u : A ->
  A' = A <[ σ ] ->
  Δ ⊢< l > t <[ σ ] ≡ u <[ τ ] : A'.
Proof.
  intros.
  eauto using pre_subst_conv, validity_conv_left, validity_conv_right, validity_subst_conv_left.
Qed.


Lemma validity_ctx_conv_left Γ Δ :
  ⊢ Γ ≡ Δ ->
  ⊢ Γ.
Proof.
  intros. induction H.
  - econstructor.
  - econstructor; eauto using validity_conv_left.
Qed.


Lemma ctx_conv_sym Γ Δ :
  ⊢ Γ ≡ Δ ->
  ⊢ Δ ≡ Γ.
Proof.
  intros. induction H.
  - econstructor.
  - econstructor; eauto.
    eapply conv_sym in H0.
    eapply pre_conv_in_ctx_conv; eauto using validity_ctx_conv_left.
Qed.


Lemma validity_ctx_conv_right Γ Δ :
  ⊢ Γ ≡ Δ ->
  ⊢ Δ.
Proof.
  intros. eauto using ctx_conv_sym, validity_ctx_conv_left.
Qed.



Theorem conv_in_ctx_ty Γ Δ l t A :
  ⊢ Γ ≡ Δ ->
  Γ ⊢< l > t : A ->
  Δ ⊢< l > t : A.
Proof.
  intros.
  eapply pre_conv_in_ctx_ty; eauto using validity_ctx_conv_right, ctx_conv_sym.
Qed.

Theorem conv_in_ctx_conv Γ Δ l t u A :
  ⊢ Γ ≡ Δ ->
  Γ ⊢< l > t ≡ u : A ->
  Δ ⊢< l > t ≡ u : A.
Proof.
  intros.
  eapply pre_conv_in_ctx_conv; eauto using validity_ctx_conv_right, ctx_conv_sym.
Qed.



(* composite lemmas, for helping automation *)

Lemma conv_ty_in_ctx_conv Γ l A A' l' t u B :
  Γ ,, (l , A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
Qed.


Lemma conv_ty_in_ctx_ty Γ l A A' l' t B :
  Γ ,, (l , A) ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_ty; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
Qed.

(* the following lemma helps automation to type some substitutions that appear often in the proof *)
Lemma subst_id_var1 Γ l P :
  Γ ,, (ty 0, Nat) ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ ,, (ty 0, Nat).
Proof.
  intro H.
  apply well_scons.
  - ssimpl.
    change (↑ >> (↑ >> var)) with ((var >> ren_term ↑) >> ren_term ↑).
    eapply WellSubst_weak; eauto.
    eapply validity_ty_ctx in H. dependent destruction H.
    eapply WellSubst_weak; eauto using subst_id.
  - ssimpl. apply type_succ. apply (type_var _ 1 _ Nat); eauto.
    all:eauto using validity_ty_ctx, ctx_cons.
    eapply (vartyS _ _ _ Nat _ 0). eapply vartyO.
Qed.

Derive NoConfusion for term.
Derive NoConfusion for level.

(* basic inversion lemmas *)


(* Lemma type_inv_var Γ l x T :
  Γ ⊢< l > var x : T →
  exists A, nth_error Γ x = Some (l , A).
Proof.
  intro H.
  dependent induction H; eauto.
Qed. *)

Lemma type_inv_pi Γ l' i j A B T:
  Γ ⊢< l' > Pi i j A B : T →
  Γ ⊢< Ax i > A : Sort i ∧ Γ ,, (i, A) ⊢< Ax j > B : Sort j.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_lam Γ i j A B t T l :
      Γ ⊢< l > lam i j A B t : T →
      Γ ⊢< Ax i > A : Sort i ∧
      Γ ,, (i , A) ⊢< Ax j > B : Sort j ∧
      Γ ,, (i , A) ⊢< j > t : B.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_app Γ i j A B t u l T :
      Γ ⊢< l > app i j A B  t u : T →
      Γ ⊢< Ax i > A : Sort i ∧
      Γ ,, (i , A) ⊢< Ax j > B : Sort j ∧
      Γ ⊢< Ru i j > t : Pi i j A B ∧
      Γ ⊢< i > u : A.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_succ Γ t T l :
      Γ ⊢< l > succ t : T →
      Γ ⊢< ty 0 > t : Nat.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_rec Γ l' l P p_zero p_succ t T :
  Γ ⊢< l' > rec l P p_zero p_succ t : T →
  Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ∧
  Γ ⊢< l > p_zero : P <[ zero .. ] ∧
  Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ∧
  Γ ⊢< ty 0 > t : Nat.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

(* newer versions of inversion lemmas.
   TODO: replace in Confluence.v the occurrences of older inversion lemmas by the newer ones *)

Lemma type_inv_var' Γ l x T :
  Γ ⊢< l > var x : T →
  Γ ⊢< l > var x : T ∧ exists A, nth_error Γ x = Some (l , A) ∧ Γ ⊢< Ax l > T ≡ (plus (S x)) ⋅ A : Sort l.
(* Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H.
  - eexists. split; eauto using conv_refl.
  - edestruct IHtyping as (C & eq & A_eq_C); eauto using validity_conv_left. eexists. split; eauto using conv_trans, conv_sym.
Qed. *)
Admitted.

Lemma type_inv_sort' Γ l' i T:
  Γ ⊢< l' > Sort i : T →
  Γ ⊢< l' > Sort i : T ∧
  l' = Ax (Ax i) ∧
  Γ ⊢< Ax (Ax (Ax i)) > T ≡ Sort (Ax i) : Sort (Ax (Ax i)).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_pi' Γ l' i j A B T:
  Γ ⊢< l' > Pi i j A B : T →
  Γ ⊢< l' > Pi i j A B : T ∧
  Γ ⊢< Ax i > A : Sort i ∧
  Γ ,, (i, A) ⊢< Ax j > B : Sort j ∧
  l' = Ax (Ru i j) ∧
  Γ ⊢< Ax (Ax (Ru i j)) > T ≡ Sort (Ru i j) : Sort (Ax (Ru i j)).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & BWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_lam' Γ i j A B t T l :
      Γ ⊢< l > lam i j A B t : T →
      Γ ⊢< l > lam i j A B t : T ∧
      Γ ⊢< Ax i > A : Sort i ∧
      Γ ,, (i , A) ⊢< Ax j > B : Sort j ∧
      Γ ,, (i , A) ⊢< j > t : B ∧
      l = Ru i j ∧
      Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A B : Sort (Ru i j).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & BWt & tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_app' Γ i j A B t u l T :
      Γ ⊢< l > app i j A B t u : T →
      Γ ⊢< l > app i j A B t u : T ∧
      Γ ⊢< Ax i > A : Sort i ∧
      Γ ,, (i , A) ⊢< Ax j > B : Sort j ∧
      Γ ⊢< Ru i j > t : Pi i j A B ∧
      Γ ⊢< i > u : A ∧
      l = j ∧
      Γ ⊢< Ax j > T ≡ B <[ u.. ] : Sort j.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & BWt & tWt & uWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_nat' Γ l' T:
  Γ ⊢< l' > Nat : T →
  Γ ⊢< l' > Nat : T ∧
  l' = ty 1 ∧
  Γ ⊢< ty 2 > T ≡ Sort (ty 0) : Sort (ty 1).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.


Lemma type_inv_zero' Γ l' T:
  Γ ⊢< l' > zero : T →
  Γ ⊢< l' > zero : T ∧
  l' = ty 0 ∧
  Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.


Lemma type_inv_succ' Γ t T l :
      Γ ⊢< l > succ t : T →
      Γ ⊢< l > succ t : T ∧
      Γ ⊢< ty 0 > t : Nat ∧
      l = ty 0 ∧
      Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_rec' Γ l' l P p_zero p_succ t T :
  Γ ⊢< l' > rec l P p_zero p_succ t : T →
  Γ ⊢< l' > rec l P p_zero p_succ t : T ∧
  Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ∧
  Γ ⊢< l > p_zero : P <[ zero .. ] ∧
  Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ∧
  Γ ⊢< ty 0 > t : Nat ∧
  l' = l ∧
  Γ ⊢< Ax l > T ≡ P <[ t.. ] : Sort l.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (PWt & p_zeroWt & p_succWt & tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_acc' Γ i A R a T l :
      Γ ⊢< l > acc i A R a : T →
      Γ ⊢< l > acc i A R a : T ∧
      Γ ⊢< Ax i > A : Sort i ∧
      Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop ∧
      Γ ⊢< i > a : A ∧
      l = Ax prop ∧
      Γ ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & RWt & aWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_accel' Γ i l A R a q P p T l' :
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ⊢< l' > accel i l A R P p a q : T →
    Γ ⊢< l' > accel i l A R P p a q : T ∧
    Γ ⊢< Ax i > A : Sort i ∧
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop ∧
    Γ ,, (i, A) ⊢< Ax l > P : Sort l ∧
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ∧
    Γ ⊢< i > a : A ∧
    Γ ⊢< prop > q : acc i A R a ∧
    l' = l ∧
    Γ ⊢< Ax l > T ≡ P <[a ..] : Sort l.
Proof.
  intros.
  apply validity_ty_ty in H as T_Wt.
  split. 1: auto.
  (* dependent induction H; eauto.
  - intuition eauto using conv_refl.
  - edestruct IHtyping as (AWt & RWt & PWt & pWt & aWt & qWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. intuition eauto using conv_trans, conv_sym. *)
Admitted.



Lemma type_inv_obseq Γ l T A i a b :
  Γ ⊢< l > obseq i A a b : T →
  Γ ⊢< Ax i > A : Sort i ∧
  Γ ⊢< i > a : A ∧
  Γ ⊢< i > b : A ∧
  l = Ax prop ∧
  Γ ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (H1 & H2 & H3 & H4 & H5); eauto using validity_conv_left.
    subst. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_accinv' Γ i A R a p b r l T :
    Γ ⊢< prop > p : acc i A R a →
    Γ ⊢< i > b : A →
    Γ ⊢< prop > r : R <[a.:b..] →
    T = acc i A R b →
    l = prop →
    Γ ⊢< l > accinv i A R a p b r : T.
Proof.
  intros. subst. eapply validity_ty_ty in H as temp.
  eapply type_inv_acc' in temp as (_ & AWt & RWt & aWt & _).
  eapply type_accinv; eauto.
Qed.

Lemma type_app' Γ i j A B t u T :
      Γ ⊢< Ru i j > t : Pi i j A B →
      Γ ⊢< i > u : A →
      (Γ ⊢< Ax j > B <[ u .. ] : Sort j → Γ ⊢< Ax j > T ≡ B <[ u .. ] : Sort j) →
      Γ ⊢< j > app i j A B  t u : T.
Proof.
  intros.
  eapply validity_ty_ty in H as temp.
  eapply type_inv_pi' in temp as (_ & AWt & BWt & _).
  assert (Γ ⊢< j > app i j A B t u : B<[u..]) as H2 by eauto using type_app.
  eapply type_conv.
  1: eauto.
  eapply conv_sym. eapply validity_ty_ty in H2. eauto.
Qed.

Lemma conv_app' Γ i j A B_ B t u A' B' t' u' :
  Γ ⊢< Ax i > A ≡ A' : Sort i →
  Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
  Γ ⊢< Ru i j > t ≡ t' : Pi i j A B →
  Γ ⊢< i > u ≡ u' : A →
  B_ = B <[ u .. ] →
  Γ ⊢< j > app i j A B t u ≡ app i j A' B' t' u' : B_.
Proof.
  intros. subst. eapply conv_app. all: eauto.
  eapply validity_conv_left. all: eassumption.
Qed.

Lemma conv_pi' Γ i j l A B A' B' :
  Γ ⊢< Ax i > A ≡ A' : Sort i →
  Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j →
  l = Ru i j →
  Γ ⊢< Ax l > Pi i j A B ≡ Pi i j A' B' : Sort l.
Proof.
  intros. subst. eapply conv_pi. all: eauto.
  eapply validity_conv_left. all: eassumption.
Qed.

Lemma conv_var' Γ x l A T :
      nth_error Γ x = Some (l , A) →
      ⊢ Γ →
      T = ((plus (S x)) ⋅ A) →
      Γ ⊢< l > (var x) ≡ (var x) : T.
(* Proof.
  intros. subst. eauto using conv_var.
Qed. *)
Admitted.

Lemma conv_lam' Γ i j A B t A' B' t' l T:
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≡ t' : B →
      l = Ru i j →
      T = Pi i j A B →
      Γ ⊢< l > lam i j A B t ≡ lam i j A' B' t' : T.
Proof.
  intros. subst. eapply conv_lam. all: eauto.
  eapply validity_conv_left. all: eassumption.
Qed.

Lemma conv_sort' l l' Γ T :
      ⊢ Γ →
      T = Sort (Ax l) →
      l' = Ax (Ax l) →
      Γ ⊢< l' > Sort l ≡ Sort l : T.
Proof.
  intros. subst. eauto using conv_sort.
Qed.




Lemma lift_subst σ1 σ2 i A A' Γ:
    ⊢ Γ ,, (i, A) →
    ∙ ⊢s σ1 ≡ σ2 : Γ →
    A' = A <[ σ1] →
    ∙ ,, (i, A') ⊢s ((var 0) .: (σ1 >> ren_term S)) ≡ ((var 0) .: (σ2 >> ren_term S)) : (Γ ,, (i, A)).
(* Proof.
    intros. subst. eapply conv_scons.
    1: admit. (* consequence of weakening *)
    rasimpl. assert (A <[ σ1 >> ren_term S] = (plus (S 0)) ⋅ (A <[ σ1])). simpl. ssimpl. eauto.
    rewrite H1.
    eapply conv_var. eauto. inversion H.
    eapply validity_subst_conv_left in H0.
    econstructor. econstructor.
    eauto using validity_conv_left, subst, refl_subst, conv_refl. *)
Admitted.


Lemma lift_subst2 σ1 σ2 i j B A _A _B Γ:
    ⊢ Γ ,, (i, A) ,,(j, B) →
    ∙ ⊢s σ1 ≡ σ2 : Γ →
    _A = A <[ σ1] →
    _B = B<[var 0 .: σ1 >> ren_term S] →
    ∙ ,, (i, _A) ,, (j, _B) ⊢s ((var 0) .: (var 1 .: (σ1 >> ren_term (S >> S)))) ≡ ((var 0) .: (var 1 .: (σ2 >> ren_term (S >> S)))) : (Γ ,, (i, A)) ,,(j, B).
Proof.
    (* intros. subst. eapply conv_scons. eapply conv_scons. ssimpl. admit. (* consequence of weakening *)
    ssimpl. assert (A <[ σ1 >> ren_term (S >> S)] = (plus (S 1)) ⋅ A <[σ1]). ssimpl. reflexivity.
    rewrite H1. eapply conv_var. eauto. shelve.
    ssimpl. assert (B <[ var 1 .: σ1 >> ren_term (S >> S)] = (plus (S 0)) ⋅ B<[ var 0 .: σ1 >> ren_term S]). ssimpl. reflexivity.
    rewrite H1. eapply conv_var. eauto.
    dependent destruction H. eapply lift_subst in H; eauto.
    dependent destruction H. asimpl in H3.
    econstructor.
    eauto using validity_ty_ctx, validity_conv_left.
    eapply lift_subst in H1; eauto using validity_ty_ctx.
    eauto using validity_conv_left, subst, refl_subst, conv_refl. *)
Admitted.

Definition obseq_sym l A a b e : term :=
  J l A a (obseq l (S ⋅ A) (var 0) (S ⋅ a)) (obsrefl l A a) b e.

Lemma type_obseq_sym : forall Γ l A a b e,
    Γ ⊢< prop > e : obseq l A a b →
    Γ ⊢< prop > obseq_sym l A a b e : obseq l A b a.
Proof.
  (* intros. eapply validity_ty_ty in H as H'.
  eapply type_inv_obseq in H' as (H1 & H2 & H3 & _).
  unfold obseq_sym.
  eapply meta_conv.
  eapply type_J; eauto. all: rasimpl. 3:reflexivity.
  2:eapply type_obsrefl; eauto.
  eapply type_obseq.
  2:eapply meta_conv. 2: eapply type_var.
  2:eauto using validity_ty_ctx, ctx_cons.
  2:reflexivity.
  2:reflexivity.
  1,2:admit. (* consequences of renaming *) *)
Admitted.


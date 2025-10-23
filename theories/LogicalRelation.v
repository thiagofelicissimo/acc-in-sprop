(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory Reduction. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.



Definition lvl_to_nat l :=
    match l with 
    | prop => O
    | ty n => S n
    end.

Notation "l ⊴ l'" :=  ((lvl_to_nat l) <= (lvl_to_nat l')) (at level 50, l' at next level).

Notation "l ◃ l'" :=  ((lvl_to_nat l) < (lvl_to_nat l')) (at level 50, l' at next level).


Lemma lvl_leq_prop l : prop ⊴ l.
Proof.
    simpl. destruct l; lia.
Qed.


Lemma lvl_eq_to_leq {i j} : i = j -> i ⊴ j.
Proof.
    intro H. rewrite H. auto.
Qed.

Fixpoint mk_Nat k := 
    match k with 
    | O => zero 
    | S k => succ (mk_Nat k)
    end.

Lemma sim_nat_to_eq k Γ l v A : Γ ⊢< l > (mk_Nat k) ~ v : A -> mk_Nat k = v.
Proof.
    generalize Γ l v A. clear  Γ l v A. destruct k.
    - intros. apply aconv_inv in H. eauto.
    - intros. apply aconv_inv in H. simpl in H. rewrite H. eauto.
Qed.  
    

Lemma sim_left_redd_whnf_mknat Γ l t k u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->>! mk_Nat k : A ->
    Γ ⊢< l > u -->>! mk_Nat k : A.
Proof.
    intros. eapply sim_left_redd_whnf in H0 as (v & H1 & H2); eauto.
    eapply sim_nat_to_eq in H2. subst. eauto.
Qed.


Lemma sim_left_redd_whnf_sort Γ l t l' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->>! Sort l' : A ->
    Γ ⊢< l > u -->>! Sort l' : A.
Proof.
    intros. eapply sim_left_redd_whnf in H0 as (v & H1 & H2); eauto.
    eapply aconv_inv in H2. simpl in H2. subst. eauto.
Qed.

Lemma leq_ru_left {i} {k} : i ⊴ Ru i (ty k).
Proof.
    destruct i; simpl; lia. 
Qed.
 
Lemma leq_ru_right {i} {k} : ty k ⊴ Ru i (ty k).
Proof.
    destruct i; simpl; lia.
Qed.


Lemma lt_ty_ax {l} : l ◃ ty (ax l).
Proof.
    destruct l; simpl; lia.
Qed.

Lemma aux {i j k} : j ◃ ty k -> j ◃ ty (ru i k).
Proof.
    intro H. unfold ru. destruct i; simpl in *; lia.
Qed.


Definition TmRel := term -> term -> Prop.

Definition LogRel := term -> term -> TmRel -> Prop.

Definition LRΩ : LogRel := fun A B R => ∙ ⊢< Ax prop > A ≡ B : Sort prop /\ forall t u : term, R t u <-> ∙ ⊢< prop > t ≡ u : A.

Definition ϵNat : TmRel := 
    fun t1 t2 => exists k, ∙ ⊢< ty 0 > t1 -->>! (mk_Nat k) : Nat /\ ∙ ⊢< ty 0 > t2 -->>! (mk_Nat k) : Nat.

Definition ϵPi i j S1 S2 (ϵS : TmRel) T1 T2 (ϵT : forall s1 s2, ϵS s1 s2 -> TmRel) : TmRel 
    := fun f1 f2 => 
        ∙ ⊢< Ru i j > f1 ≡ f2 : Pi i j S1 T1 /\
        forall s1 s2 (ϵs : ϵS s1 s2), ϵT s1 s2 ϵs (app i j S1 T1 f1 s1) (app i j S2 T2 f2 s2).

Definition same_rel (R1 R2 : term -> term -> Prop) := forall t u, R1 t u <-> R2 t u.

Notation "R1 <~> R2" :=  (forall t u, R1 t u <-> R2 t u) (at level 50, R2 at next level).

Inductive LRTy : forall (k : nat) (rec : forall j, j ◃ (ty k) -> LogRel), LogRel :=
| LRTy_nat A1 A2 rec R : 
    ∙ ⊢< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) -> 
    ∙ ⊢< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) ->
    R <~> ϵNat ->
    LRTy 0 rec A1 A2 R
| LRTy_pi1 i k A1 A2 S1 S2 ϵS T1 T2 ϵT R
    (rec : forall j, j ◃ ty k -> LogRel)
    (q : i ◃ ty k) :
    ∙ ⊢< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) -> 
    ∙ ⊢< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
    (* ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ A2 : Sort (Ru i (ty k)) -> *)
    ∙ ⊢< Ax i > S1 ≡ S2 : Sort i -> 
    ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    rec i q S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LRTy k rec (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)) ->
    R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LRTy k rec A1 A2 R
| LRTy_pi2 k A1 A2 S1 S2 ϵS T1 T2 ϵT R
    (rec : forall j, j ◃ ty k -> LogRel) :
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A1 -->>! Pi (ty k) (ty k) S1 T1 : Sort (Ru (ty k) (ty k)) -> 
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A2 -->>! Pi (ty k) (ty k) S2 T2 : Sort (Ru (ty k) (ty k)) ->
    (* ∙ ⊢< Ax (Ru (ty k) (ty k)) > A1 ≡ A2 : Sort (Ru (ty k) (ty k)) -> *)
    ∙ ⊢< Ax (ty k) > S1 ≡ S2 : Sort (ty k) -> 
    ∙ ,, (ty k, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LRTy k rec S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LRTy k rec (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)) ->
    R <~> (ϵPi (ty k) (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LRTy k rec A1 A2 R
| LRTy_pi3 n k A1 A2 S1 S2 ϵS T1 T2 ϵT R
    (rec : forall j, j ◃ ty n -> LogRel)
    (q : k < n) :
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A1 -->>! Pi (ty n) (ty k) S1 T1 : Sort (Ru (ty n) (ty k)) -> 
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A2 -->>! Pi (ty n) (ty k) S2 T2 : Sort (Ru (ty n) (ty k)) ->
    (* ∙ ⊢< Ax (Ru (ty n) (ty k)) > A1 ≡ A2 : Sort (Ru (ty n) (ty k)) -> *)
    ∙ ⊢< Ax (ty n) > S1 ≡ S2 : Sort (ty n) -> 
    ∙ ,, (ty n, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LRTy n rec S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        rec (ty k) (ltac :(simpl; lia)) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)) ->
    R <~> (ϵPi (ty n) (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LRTy n rec A1 A2 R
| LRTy_U l A1 A2 rec R : 
    ∙ ⊢< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l) -> 
    ∙ ⊢< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l) ->
    R <~> (fun B1 B2 => exists R, rec l lt_ty_ax B1 B2 R) ->
    LRTy (ax l) rec A1 A2 R.


Definition LR (l : level) : LogRel.
    refine (@Fix_F _ (fun i j => i ◃ j) (fun _ => LogRel) _ l _).
    - intros. destruct x.
        + apply (LRTy n). apply X.
        + apply LRΩ.
    - apply wf_inverse_image. apply lt_wf.
Defined.


Notation "⊩< l > A ≡ B ↓ R" :=  (LR l A B R) (at level 50, A, B, R at next level).

Axiom proof_irrel : forall (P : Prop) (p q : P), p = q.

Lemma acc_irrel i (f g : forall (l : level) (p : l ◃ ty i), Acc (λ i j : level, i ◃ j) l) : f = g.
Proof.
    apply proof_irrel.
Qed.

Lemma LR_prop_eq : LR prop = LRΩ.
Proof.
    unfold LR. rewrite <- Fix_F_eq. auto.
Qed.

Definition nat_to_lvl n := 
    match n with 
    | O => prop 
    | S n => ty n 
    end.

Lemma lvl_to_nat_to_lvl l : nat_to_lvl (lvl_to_nat l) = l.
Proof.
    destruct l.
    - auto.
    - auto.
Qed.


Lemma LR_ty_eq i : 
    LR (ty i) = LRTy i (fun l _ => LR l).
Proof.
    unfold LR. rewrite <- Fix_F_eq. f_equal. 
(* Set Printing Implicit. *)
    pattern (fun l => wf_inverse_image level nat lt lvl_to_nat lt_wf l). 
    set (G := (λ (F : forall l (p : l ◃ ty i), Acc (λ i j : level, i ◃ j) l) (l : level) (p : l ◃ ty i),
@Fix_F _ (fun x y => x ◃ y) (λ _ : level, LogRel)
(λ (x : level) (H : ∀ y : level, y ◃ x → LogRel),
match x as l0 return ((∀ y : level, y ◃ l0 → LogRel) → LogRel) with
| ty n => λ X : ∀ y : level, y ◃ ty n → LogRel, LRTy n X
| prop => λ _ : ∀ y : level, y ◃ prop → LogRel, LRΩ
end H) _ (F l p))).
    transitivity (G (fun l p => wf_inverse_image level nat lt lvl_to_nat lt_wf l)).
    erewrite (@acc_irrel i (fun l _ => wf_inverse_image level nat lt lvl_to_nat lt_wf l)). reflexivity. reflexivity.
Qed.

Definition LR_prop A1 A2 R : 
    ∙ ⊢< Ax prop > A1 ≡ A2 : Sort prop ->
    R <~> (fun t u => ∙ ⊢< prop > t ≡ u : A1) ->
    LR prop A1 A2 R.
Proof.
    intros.
    rewrite LR_prop_eq. split; eauto.
Qed.

Definition LR_nat A1 A2 R : 
    ∙ ⊢< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) -> 
    ∙ ⊢< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) ->
    R <~> ϵNat ->
    LR (ty 0) A1 A2 R.
Proof.
    intros. rewrite LR_ty_eq.
    constructor; eauto.
Qed.

Definition LR_U l A1 A2 R : 
    ∙ ⊢< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l) -> 
    ∙ ⊢< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l) ->
    R <~> (fun B1 B2 => exists R, LR l B1 B2 R) ->
    LR (Ax l) A1 A2 R.
Proof.
    intros. unfold Ax. rewrite LR_ty_eq.
    constructor; eauto.
Qed.


Definition LR_pi i k A1 A2 S1 S2 ϵS T1 T2 ϵT R : 
    ∙ ⊢< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) -> 
    ∙ ⊢< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
    ∙ ⊢< Ax i > S1 ≡ S2 : Sort i -> 
    ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LR i S1 S2 ϵS -> 
    (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)) ->
    R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LR (Ru i (ty k)) A1 A2 R.
Proof.
    intros. unfold Ru. rewrite LR_ty_eq.
    assert (i ⊴ (ty k) \/ ty k ◃ i) by eauto using Nat.le_gt_cases.
    destruct H6. inversion H6.
    - pose proof (f_equal nat_to_lvl H8) as H'. rewrite lvl_to_nat_to_lvl in H'. rewrite H' in *. 
      simpl. assert (max k k = k) by lia. rewrite H7. eapply LRTy_pi2; eauto. 
      rewrite <- LR_ty_eq. auto.
      rewrite <- LR_ty_eq. auto.
    - assert (ru i k = k). unfold ru. destruct i. simpl in H8. lia. auto.
      rewrite H9. eapply LRTy_pi1; eauto. 
      simpl. lia.
      rewrite <- LR_ty_eq. auto.
    - destruct i. 2:inversion H6.
      simpl in H6. assert (ru (ty n) k = n). unfold ru. lia.
      rewrite H7. eapply LRTy_pi3; eauto. lia. 
      rewrite <- LR_ty_eq. eauto.
Qed.


Definition LR_ind 
    (P : forall l A B R, Prop)
    (p_prop : forall A B R (p : LRΩ A B R), P prop A B R) 
    (p_nat : forall A1 A2 R
        (A1_red_nat : ∙ ⊢< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0))
        (A2_red_nat : ∙ ⊢< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0)),
        R <~> ϵNat ->
        P (ty 0) A1 A2 R)
    (p_U : forall l A1 A2 R
        (A1_red_U : ∙ ⊢< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l))
        (A2_red_U : ∙ ⊢< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l)),
        (forall B1 B2 R, LR l B1 B2 R -> P l B1 B2 R) ->
        R <~> (fun B1 B2 => exists R, LR l B1 B2 R) ->
        P (Ax l) A1 A2 R)
    (p_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT R
        (A1_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)))
        (A2_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)))
        (S1_eq_S2 : ∙ ⊢< Ax i > S1 ≡ S2 : Sort i) 
        (T1_eq_T2 : ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k))
        (LR_S : LR i S1 S2 ϵS)
        (LR_T : forall s1 s2 (ϵs : ϵS s1 s2), 
                LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)),
        R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        P i S1 S2 ϵS -> 
        (forall s1 s2 (ϵs : ϵS s1 s2), P (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)) ->
        P (Ru i (ty k)) A1 A2 R)
    (l : level) (A B : term) (R : TmRel) (x : LR l A B R) : P l A B R.
Proof.
    generalize l A B R x.
    clear A B R l x.
    refine (@well_founded_ind _ (fun l l' => l ◃ l') _ _ _).
    apply wf_inverse_image. apply lt_wf.
    intros l H A B R x.
    destruct l.
    - rewrite LR_ty_eq in x. 
      set (rec := (λ (l : level) (_ : l ◃ ty n), LR l)).
        assert (rec = (λ (l : level) (_ : l ◃ ty n), LR l)) by reflexivity.
        rewrite <- H0 in x.
        induction x.
        + apply p_nat; auto.
        + rewrite H0 in H5. rewrite H0 in H6. rewrite <- LR_ty_eq in H6.
          assert (k = ru i k). unfold ru. destruct i. simpl in q. lia. lia.
          rewrite H9 at 1. eapply p_pi; eauto.
        + rewrite H0 in H5. rewrite <- LR_ty_eq in H5.
          rewrite H0 in x. rewrite <- LR_ty_eq in x.
          assert (k = ru (ty k) k). simpl. lia.
          rewrite H8 at 1. eapply p_pi; eauto.
        + rewrite H0 in *. rewrite <- LR_ty_eq in x.
          assert (ty n = Ru (ty n) (ty k)). simpl. f_equal. lia. rewrite H7 at 1.
          eapply p_pi; eauto. 
          intros. apply H. simpl. lia. auto.
        + rewrite H0 in H3. eapply p_U; eauto.
    - rewrite LR_prop_eq in x. apply p_prop. auto.
Qed.

Lemma LR_escape l A B R : 
    LR l A B R -> ∙ ⊢< Ax l > A ≡ B : Sort l /\ forall t u, R t u -> ∙ ⊢< l > t ≡ u : A.
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. split.
      + destruct p. auto.
      + destruct p. intros. eapply H0. eauto.
    - intros. split.
      + eauto using redd_whnf_to_conv, conv_trans, conv_sym.
      + intros. unfold ϵNat in H. apply H in H0 as (k & H1 & H2). eauto 8 using redd_whnf_to_conv, conv_trans, conv_sym, conv_conv.
    - intros. split.
      + eauto using redd_whnf_to_conv, conv_trans, conv_sym.
      + intros. apply H0 in H1 as (R' & lr). apply H in lr as (t_eq_u & _). eauto 8 using redd_whnf_to_conv, conv_trans, conv_sym, conv_conv.
    - intros. split; auto.
      intros. eapply redd_whnf_to_conv in A1_red_pi, A2_red_pi.
      eapply conv_trans. eapply A1_red_pi. eapply conv_trans. 2:(eapply conv_sym; eapply A2_red_pi).
      eapply conv_pi; eauto.
      intros. apply H in H2. destruct H2. eauto using conv_conv, redd_whnf_to_conv, conv_sym.
Qed.


(* we split the result in two, so we can use eauto with it *)
Corollary LR_escape_ty {l A B R} : 
    LR l A B R -> ∙ ⊢< Ax l > A ≡ B : Sort l.
Proof.
    intros. eapply LR_escape in H as (H1 & H2). eauto.
Qed.

Corollary LR_escape_tm  {l A B R t u }: 
    LR l A B R -> R t u -> ∙ ⊢< l > t ≡ u : A.
Proof.
    intros. eapply LR_escape in H as (H1 & H2). eauto.
Qed.

Lemma conv_aux {i j s1 s2 S1 T1 T2} : 
    ∙ ⊢< i > s1 ≡ s2 : S1 -> ∙,, (i, S1) ⊢< Ax j > T1 ≡ T2 : Sort j -> ∙ ⊢< Ax j > T1 <[ s1 ..] ≡ T2 <[ s2.. ] : Sort j.
Proof.
    intros. assert (Sort j = Sort j <[ s1 ..]). ssimpl; eauto.
    rewrite H1. eapply subst. eapply (conv_scons _ _ _ ∙  i S1). ssimpl. eapply refl_subst. eapply subst_id. eauto using ctx_typing.
    ssimpl. eauto. eauto.
Qed.

Lemma LR_erasure l A B R : 
    LR l A B R -> 
    (forall A' B', 
        ∙ ⊢< Ax l > A ~ A' : Sort l ->
        ∙ ⊢< Ax l > B ~ B' : Sort l ->
        LR l A' B' R) 
    /\
    (forall t u t' u', 
        ∙ ⊢< l > t ~ t' : A -> 
        ∙ ⊢< l > u ~ u' : A -> 
        R t u -> 
        R t' u').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. destruct p. split; intros.
        + rewrite LR_prop_eq. split.
            ++ eauto 6 using conv_sym, conv_trans, sim_to_conv.
            ++ intros. destruct (H0 t u). split; eauto using conv_conv, conv_sym, sim_to_conv.
        + destruct (H0 t' u'). destruct (H0 t u). eauto 8 using sim_to_conv, conv_trans, conv_sym.
    - intros. split; intros.
        + eapply sim_left_redd_whnf in A1_red_nat as (_Nat & A'_redd_nat & nat_sim); eauto.
          eapply aconv_inv in nat_sim. simpl in nat_sim. subst.
          eapply sim_left_redd_whnf in A2_red_nat as (_Nat & B'_redd_nat & nat_sim); eauto.
          eapply aconv_inv in nat_sim. simpl in nat_sim. subst.
          apply LR_nat; eauto.
        + rewrite H in *. destruct H2 as (k & t_redd_k & u_redd_k).
          unfold ϵNat. exists k. eauto 8 using sim_left_redd_whnf_mknat, sim_sym, aconv_conv, redd_whnf_to_conv.
    - intros. split; intros.
        + apply LR_U; eauto using sim_left_redd, sim_sym, sim_left_redd_whnf_sort.
        + rewrite H0 in *. destruct H3 as (R' & lr). destruct (H t u R' lr).
          apply redd_whnf_to_conv in A1_red_U as A1_conv_U.
          exists R'. eapply H3; eauto using aconv_conv, conv_sym.
    - intros. split; intros.
        + eapply sim_left_redd_whnf in A1_red_pi as (_pi & A'_redd_pi & pi_sim); eauto.
          eapply aconv_inv in pi_sim. simpl in pi_sim. subst.
          eapply sim_left_redd_whnf in A2_red_pi as (_pi & B'_redd_pi & pi_sim); eauto.
          eapply aconv_inv in pi_sim. simpl in pi_sim. subst.
          eapply LR_pi; eauto 6 using sim_left_redd, sim_sym, sim_to_conv, conv_trans, conv_sym.
        + rewrite H in *. destruct H4. apply redd_whnf_to_conv in A1_red_pi as A1_conv_pi. split.
            ++ eauto 8 using sim_to_conv, conv_trans, conv_sym, conv_conv.
            ++ intros.
               destruct (H1 s1 s2 ϵs). eapply H7; eauto.
               +++ eapply aconv_app; eauto 7 using validity_conv_left, refl_ty, LR_escape_tm, redd_whnf_to_conv, aconv_conv.
               +++ eapply aconv_conv; eauto using conv_aux, conv_sym, LR_escape_tm.
                   eapply aconv_app; eauto 9 using validity_conv_right, refl_ty, conv_ty_in_ctx_ty, LR_escape_tm, LR_escape_ty, type_conv.
                   eauto using aconv_conv, redd_whnf_to_conv, conv_sym, conv_trans, conv_pi.
Qed.

Definition LR_inv_type l A1 A2 A1' R (A1_redd_A1' : ∙ ⊢< Ax l > A1 -->>! A1' : Sort l) : Prop :=
    match l, A1' with 
    | prop, _ => LRΩ A1 A2 R
    | _, Nat => 
        l = ty 0 /\ 
        ∙ ⊢< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) /\ 
        ∙ ⊢< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) /\ 
        R <~> ϵNat
    | _, Sort l' => 
        l = Ax l' /\ 
        ∙ ⊢< Ax (Ax l') > A1 -->>! Sort l' : Sort (Ax l') /\ 
        ∙ ⊢< Ax (Ax l') > A2 -->>! Sort l' : Sort (Ax l') /\ 
        R <~> (fun B1 B2 => exists R', LR l' B1 B2 R')
    | _, Pi i (ty k) S1 T1 => exists S2 T2 ϵS ϵT,
        l = Ru i (ty k) /\ 
        ∙ ⊢< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) /\
        ∙ ⊢< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) /\
        ∙ ⊢< Ax i > S1 ≡ S2 : Sort i /\
        ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) /\
        LR i S1 S2 ϵS /\
        (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2 ϵs)) /\
        R <~> ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT
    | _, _ => True
    end.

Lemma LR_inv {l A1 A2 A1' R} (A1_redd_A1' : ∙ ⊢< Ax l > A1 -->>! A1' : Sort l) : LR l A1 A2 R -> LR_inv_type l A1 A2 A1' R A1_redd_A1'.
Proof.
    intro lr. generalize l A1 A2 R lr A1' A1_redd_A1'. clear l A1 A2 R lr A1' A1_redd_A1'.
    refine (LR_ind _ _ _ _ _).
    - intros. auto. 
    - intros. 
      eapply redd_whnf_det in A1_red_nat as A1'_eq_Nat; eauto. subst.
      simpl. eauto.
    - intros.
      eapply redd_whnf_det in A1_red_U as A1'_eq_U; eauto. subst.
      simpl. eauto.
    - intros. 
      eapply redd_whnf_det in A1_red_pi as A1'_eq_pi; eauto. subst.
      simpl. do 4 eexists. 
      split; eauto.
      split; eauto. split; eauto.
Qed.

Lemma LR_irrel l A B B' R1 R2 : 
    LR l A B R1 -> 
    LR l A B' R2 -> 
    forall t1 t2, R1 t1 t2 <-> R2 t1 t2.
Proof.
    intro lr1. generalize l A B R1 lr1 B' R2. clear l A B R1 lr1 B' R2.
    refine (LR_ind _ _ _ _ _).
    - intros. rewrite LR_prop_eq in H. destruct p, H. destruct (H1 t1 t2), (H2 t1 t2). split; eauto.
    - intros. eapply (LR_inv A1_red_nat) in H0. destruct H0 as (_ & _ & _ & H0). symmetry. rewrite H. auto.
    - intros. eapply (LR_inv A1_red_U) in H1. destruct H1 as (_ & _ & _ & H'). rewrite H0. rewrite H'. split; eauto.
    - intros. eapply (LR_inv A1_red_pi) in H2. 
      destruct H2 as (S2' & T2' & ϵS' & ϵT' & l_eq & A1_red' & A2_red' & S_eq & T_eq & LR_S' & LR_T' & R_eq).
      assert (ϵS <~> ϵS') by eauto. 
      rewrite R_eq, H. 
      split.
      + intros. destruct H3. split. eauto. intros.
        assert (forall s1 s2 ϵs, ϵT s1 s2 (proj2 (H2 s1 s2) ϵs) <~> ϵT' s1 s2 ϵs).
            { intros. eapply H1. eauto. }
        eapply H5. eapply LR_erasure; eauto. 
        ++ rewrite <- H2 in ϵs. unshelve eauto using aconv_refl, type_app, LR_escape_tm, validity_conv_left; eauto.
        ++ eapply aconv_conv; eauto using conv_aux, LR_escape_tm, conv_sym.
           eapply sim_sym. eapply aconv_app; eauto using conv_trans, conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, LR_escape_ty, type_conv, validity_conv_right.
           eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi, conv_sym, conv_trans, conv_ty_in_ctx_conv.
      + intros. destruct H3. split. eauto. intros.
        assert (forall s1 s2 ϵs, ϵT' s1 s2 (proj1 (H2 s1 s2) ϵs) <~> ϵT s1 s2 ϵs).
            { intros. symmetry. eapply H1. eauto. }
        eapply H5.  eapply LR_erasure; eauto.
        ++ rewrite H2 in ϵs. unshelve eauto using aconv_refl, type_app, LR_escape_tm, validity_conv_left; eauto.
        ++ eapply aconv_conv; eauto using conv_aux, LR_escape_tm, conv_sym.
           eapply aconv_app; eauto using conv_trans, conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, LR_escape_ty, type_conv, validity_conv_right.
           eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi, conv_sym, conv_trans, conv_ty_in_ctx_conv.
Qed.

Definition PER {A} (R:A -> A -> Prop) := 
    (forall t u, R t u -> R u t) /\ (forall t u v, R t v -> R v u -> R t u).

Lemma PER_refl {A} {R : A -> A -> Prop} {t u} : PER R -> R t u -> R t t.
Proof.
    intros. destruct H. eapply H1; eauto.
Qed.

Lemma LR_iff_rel l A B R R' :
    R <~> R' ->
    LR l A B R -> 
    LR l A B R'.
Proof.
    intros. generalize l A B R H0 R' H. clear l A B R H0 R' H. 
    refine (LR_ind _ _ _ _ _); intros.
    - rewrite LR_prop_eq. destruct p. split; eauto. intros. rewrite <- H. eauto.
    - eapply LR_nat; eauto. intros. rewrite <- H0. eauto.
    - eapply LR_U; eauto. intros. rewrite <- H1. eauto.
    - eapply LR_pi; eauto. intros. rewrite <- H2. eauto.
Qed. 



(* there are different ways to prove the basic properties of the LR  
    TODO finish writing this
   1) Prove all the properties together, using Angiuli's 'power move' as described in 
        page 26 of the technical report for "Implementing a modal dependent type theory"
        (...)

   2) Jason Hu's Mctt : Changing the def of the logical relation, so that the fact that 
        ϵS is a PER is built in
   3) MLTT à la Coq & Jason Hu's MINT: 
        Prove first weaker statements and prove the real statements after.
        For instance, weakened symmetry then becomes 
          LR l A B R -> exists R', LR l B A R' /\ forall t u, R t u -> R' u t  
        However, when placing the logical relation in Prop, this seems
        to require eliminating from Prop to Type. 
        Indeed, in the case of Pi, the ih of the codomain T gives 
          forall s1 s2 (ϵs : ϵS s1 s2), exists ϵT', ... 
        But we would need some form of choice to extract 
          ϵT' : forall s1 s2 (ϵs : ϵS s1 s2), TmRel
        Thankfully, in McTT a way to sidestep the need of choice is given
        (altough they do not use it specifically for deriving the basic properties,
        as already mentioned). This is given by the following eT construction,
        along with the lemma ϵT_iff_eT stating that eT corresponds to the right 
        relation ϵT, whenever we have enough information to obtain ϵT.
   *)

Definition eT j ϵS T1 T2 := 
    fun s1 s2 (ϵs : ϵS s1 s2) a1 a2 => forall R, LR j (T1 <[ s1..]) (T2 <[ s2..]) R -> R a1 a2.
 
Lemma ϵT_iff_eT i j S1 S2 ϵS T1 T2 ϵT s1 s2 ϵs :
    LR i S1 S2 ϵS ->
    LR j (T1 <[ s1..]) (T2 <[ s2..]) ϵT-> 
    ϵT <~> eT j ϵS T1 T2 s1 s2 ϵs.
Proof.
    intros; split; intros.
    - unfold eT. intros. assert (R <~> ϵT) by eauto using LR_irrel.
      rewrite H3. eauto.
    - eapply H1 in H0. eauto.
Qed.

Lemma split_iff (R R': TmRel) : R <~> R' -> (forall t u, R t u -> R' t u) /\ (forall t u, R' t u -> R t u).
Proof.
    split; intros; rewrite H in *; eauto.
Qed.

Lemma LR_sym' l A B R : 
    LR l A B R -> exists R', LR l B A R' /\ forall t u, R t u <-> R' u t.
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. exists R.
      split. 
      + rewrite LR_prop_eq. 
        split; eauto using conv_sym.   
        setoid_rewrite H0. split; eauto using conv_conv, conv_sym.
      + setoid_rewrite H0. split; eauto using conv_sym.
    - eexists. split.
      + eapply LR_nat; eauto.
      + setoid_rewrite H. intros. 
        split; intros H0; destruct H0 as (k & redd_to_k1 & redd_to_k2);
        eexists; split; eauto.
    - exists (fun A B => exists R, LR l A B R).
      split.
      + eapply LR_U; eauto. split; eauto.
      + intros B1 B2; split; intros LR_B; rewrite H0 in *.
        all: destruct LR_B as (R' & LR_B); eapply H in LR_B as (R'' & LR_B' & _); eauto.
    - destruct H0 as (ϵS' & LR_S' & ϵS_iff_ϵS').
      eapply split_iff in ϵS_iff_ϵS' as (ϵS_to_ϵS' & ϵS'_to_ϵS).
      exists (ϵPi i (ty k) S2 S1 ϵS' T2 T1 (eT (ty k) ϵS' T2 T1)).
      split.
      + eapply LR_pi; eauto using conv_sym, conv_ty_in_ctx_conv. 
        intros. apply ϵS'_to_ϵS in ϵs as ϵs'.
        destruct (H1 _ _ ϵs') as (ϵT' & LR_T' & ϵT_iff_ϵT'). 
        eapply LR_iff_rel; eauto using ϵT_iff_eT.
        split; eauto.
      + intros; split; intros; rewrite H in *.
        ++  destruct H0. split; eauto using conv_pi, conv_sym, conv_conv.
            intros.  apply ϵS'_to_ϵS in ϵs as ϵs'.
            destruct (H1 _ _ ϵs') as (ϵT' & LR_T' & ϵT_iff_ϵT').
            rewrite <- ϵT_iff_eT; eauto. rewrite <- ϵT_iff_ϵT'. eauto.
        ++  destruct H0. split; eauto using conv_pi, conv_sym, conv_conv.
            intros.
            destruct (H1 _ _ ϵs) as (ϵT' & LR_T' & ϵT_iff_ϵT'). 
            eapply H2 in LR_T'; eauto. rewrite ϵT_iff_ϵT'. eauto.
Qed.

Lemma LR_trans' l A B C R R' :
    LR l A B R -> LR l B C R' -> exists R'', LR l A C R'' /\ forall t v u, R t v -> R' v u -> R'' t u.
Proof.
    intro lr. generalize l A B R lr C R'. clear l A B R lr C R'.
    refine (LR_ind _ _ _ _ _); intros.
    - rewrite LR_prop_eq in H. destruct H. destruct p.
      exists R. split.
      + rewrite LR_prop_eq. split; eauto using conv_trans.
      + intros. rewrite H2 in H3. rewrite H2. rewrite H0 in H4. 
        eauto using conv_trans, conv_conv, conv_sym.
    - unshelve eapply LR_inv in H0 as temp. 2:eauto.
      destruct temp as (_ & _ & C_red & H').
      eexists. split.
      + eapply LR_nat; eauto.
      + intros. rewrite H in *. rewrite H' in *.
        destruct H1 as (k1 & t_red & v_red). 
        destruct H2 as (k2 & v_red' & u_red).
        eapply redd_whnf_det in v_red; eauto. 
        rewrite v_red in u_red.
        eexists. split; eauto.
    - unshelve eapply LR_inv in H1 as temp. 2:eauto. 
      destruct temp as (_ & _ & C_red & H').
      exists (fun A B => exists R, LR l A B R).
      split. 
      + eapply LR_U; eauto. split; eauto.
      + intros. rewrite H0 in H2. rewrite H' in H3.
        destruct H2. destruct H3.
        eapply H in H3; eauto. 
        destruct H3 as (R'' & LR & _). 
        eexists. eauto.
    - unshelve eapply LR_inv in H2. 2: eauto.
      destruct H2 as (S' & T' & ϵS' & ϵT' & _ & _ & C_red & S2_eq_S' & T2_eq_T' & LR_S' & LR_T' & R'_iff).
      pose proof LR_S' as temp. eapply H0 in temp as (ϵS'' & LR_S'' & ϵS_to).
      
      (* we first show that the ϵS, ϵS', ϵS'' are all equivalent *)
      assert (ϵS <~> ϵS'') as _temp by eauto using LR_irrel.
      eapply split_iff in _temp as (ϵS_to_ϵS'' & ϵS''_to_ϵS).      

      eapply LR_sym' in LR_S'' as temp. destruct temp as (ϵSc & LR_Sc & ϵSc_to).
      eapply LR_sym' in LR_S' as temp. destruct temp as (ϵSc' & LR_Sc' & ϵSc_to').
      assert (ϵSc <~> ϵSc') as _temp by eauto using LR_irrel. 
      setoid_rewrite _temp in ϵSc_to. setoid_rewrite <- ϵSc_to in ϵSc_to'. 
      eapply split_iff in ϵSc_to' as (ϵS'_to_ϵS'' & ϵS''_to_ϵS').   
      clear ϵSc ϵSc' LR_Sc LR_Sc' _temp ϵSc_to.

      (* finally, we show that ϵS is symmetric *)
      eapply LR_sym' in LR_S as temp. destruct temp as (ϵSc & LR_Sc & ϵSc_to).
      assert (ϵSc <~> ϵS') by eauto using LR_irrel. setoid_rewrite H2 in ϵSc_to.
      eapply split_iff in ϵSc_to as (temp1 & temp2).
      assert (forall t u, ϵS t u -> ϵS u t) as ϵS_sym by eauto.
      clear ϵSc LR_Sc H2 temp1 temp2.

      exists (ϵPi i (ty k) S1 S' ϵS'' T1 T' (eT (ty k) ϵS'' T1 T')).
      split.
      + eapply LR_pi; eauto using conv_trans, conv_ty_in_ctx_conv, conv_sym.
        intros. assert (ϵS s1 s2) as ϵs' by eauto. pose (LR_T_1 := LR_T _ _ ϵs').
        assert (ϵS' s2 s2) as ϵs'' by eauto. pose (LR_T_2 := LR_T' _ _ ϵs'').
        unshelve eapply H1 in LR_T_2. 2: eauto. 
        destruct LR_T_2 as (ϵT'' & LR_T'' & ϵT_to).
        eapply LR_iff_rel. 2:eauto. 
        eapply ϵT_iff_eT; eauto.
        split; eauto.
      + intros. rewrite H, R'_iff in *.
        destruct H2, H3.
        split; eauto using conv_trans, conv_conv, conv_sym, conv_pi, conv_ty_in_ctx_conv.
        intros.
        assert (ϵS s1 s2) as ϵs' by eauto. pose (LR_T_1 := LR_T _ _ ϵs').
        assert (ϵS' s2 s2) as ϵs'' by eauto. pose (LR_T_2 := LR_T' _ _ ϵs'').
        unshelve eapply H1 in LR_T_2. 2: eauto. 
        destruct LR_T_2 as (ϵT'' & LR_T'' & ϵT_to).        
        rewrite <- ϵT_iff_eT; eauto. eauto.
Qed.

Lemma LR_refl_r l A B R : LR l A B R -> LR l B B R.
Proof.
    intros. eapply LR_sym' in H as temp.
    destruct temp as (R' & H' & X).
    eapply LR_trans' in H as (R'' & H'' & _); eauto.
    assert (R' <~> R'') by eauto using LR_irrel.
    eapply LR_sym' in H'' as (R''' & H''' & Y).
    eapply LR_iff_rel; eauto.
    setoid_rewrite X. setoid_rewrite <- Y. 
    symmetry. eauto.
Qed.


Lemma LR_sym l A B R : 
    LR l A B R -> LR l B A R.
Proof.
    intros.
    eapply LR_refl_r in H as ϵB_B.
    eapply LR_sym' in H as (R' & ϵB_A & equiv1).
    eapply LR_iff_rel; eauto using LR_irrel.
Qed.

Lemma LR_trans l A B C R R' : 
    LR l A B R -> LR l B C R' -> LR l A C R.
Proof.
    intros.
    eapply LR_trans' in H0; eauto.
    destruct H0 as (R'' & lr & _).
    eapply LR_iff_rel; eauto using LR_irrel.
Qed.

Lemma LR_sym_tm l A B R t u : LR l A B R -> R t u -> R u t.
Proof.
    intros. eapply LR_sym' in H as temp. 
    destruct temp as (R' & lr & equiv).
    eapply LR_refl_r in H. 
    assert (R <~> R') by eauto using LR_irrel.
    rewrite H1. eapply equiv in H0. eauto.
Qed.

Lemma LR_trans_tm l A B R t u v : 
    LR l A B R -> 
    R t v -> R v u -> R t u.
Proof.
    intros. eapply LR_refl_r in H as H'.
    eapply LR_trans' in H' as temp; eauto.
    destruct temp as (R' & lr & imp).
    assert (R <~> R') by eauto using LR_irrel. 
    setoid_rewrite <- H2 in imp.
    eauto.
Qed.

Section old_basics_props_proof.
(* old proof, much bigger *)

Lemma helper_ϵT_irrel {ϵS : TmRel} 
    (ϵT : forall s1 s2, ϵS s1 s2 -> TmRel) {s1 s2} {ϵs ϵs'} {t u}: 
    ϵT s1 s2 ϵs t u -> ϵT s1 s2 ϵs' t u.
Proof.
    intros. assert (ϵs = ϵs') by eauto using proof_irrel. subst. eauto.
Qed.
Lemma LR_basic_props l A B R :
    LR l A B R ->
    PER R /\
    LR l B A R /\ 
    (forall R' C, LR l B C R' -> LR l A C R' /\ R <~> R').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. split. 2:split.
      + destruct p. split; intros; rewrite H0 in *; eauto using conv_sym, conv_trans.
      + rewrite LR_prop_eq. destruct p. split; eauto using conv_sym. intros. 
        rewrite (H0 t u). split; intros; eauto using conv_conv, conv_sym.
      + intros. rewrite LR_prop_eq in *. destruct H, p. split. split; eauto using conv_trans.
        intros. rewrite (H0 t u). split; intros; eauto using conv_conv, conv_sym.
        intros. rewrite (H2 t u). rewrite (H0 t u).  split; intros; eauto using conv_conv, conv_sym.
    - intros. split. 2:split.
      + split; intros; rewrite H in *. 
        destruct H0 as (k & H1 & H2). eexists. split; eauto.
        destruct H0 as (k & t_red & v_red). destruct H1 as (k' & v_red' & u_red).
        exists k. split. eauto. 
        eapply redd_whnf_det in v_red'. 2:eapply v_red. rewrite v_red'. eauto.
      + eapply LR_nat; eauto.
      + intros. unshelve eapply LR_inv in H0. shelve. eapply A2_red_nat. 
        destruct H0 as (_ & _ & C_red & R'_iff_nat). 
        split. eauto using LR_nat. intros. rewrite H. rewrite R'_iff_nat. split; auto.
    - intros. split. 2:split.
      + split; intros; rewrite H0 in *. destruct H1. destruct (H _ _ _ H1) as (_ & H' & _). eexists. eauto.
        destruct H1. destruct H2. destruct (H _ _ _ H1) as (_ & _  & H').
        destruct (H' _ _ H2). eexists. eauto.
      + eapply LR_U; eauto. 
      + intros. pose proof H1 as H1'. unshelve eapply LR_inv in H1. shelve. eauto. destruct H1 as (_ & _ & C_red & H').
        split. eapply LR_U; eauto.
        intros; split; rewrite H'; rewrite H0; intros; eauto.
    - intros. 
      destruct H0 as (PER_ϵS & LR_S_sym & LR_S_trans).
      pose proof PER_ϵS as PER_ϵS'.
      destruct PER_ϵS as (ϵS_sym & ϵS_trans). rename PER_ϵS' into PER_ϵS.
      assert (forall s1 s2 ϵs, 
        ϵT s1 s2 ϵs <~> ϵT s2 s1 (ϵS_sym _ _ ϵs) /\ ϵT s1 s2 ϵs <~> ϵT s2 s2 (PER_refl PER_ϵS (ϵS_sym _ _ ϵs))).
      { intros. pose (ϵs' := ϵS_sym _ _ ϵs). pose (ϵs'' := PER_refl PER_ϵS ϵs').
        destruct (H1 _ _ ϵs) as (_ & LR_T_s1_s2 & _).
        destruct (H1 _ _ ϵs'') as (_ & LR_T_s2_s2 & _).
        pose (HA' := LR_T _ _ ϵs''). pose (HB' := LR_T _ _ ϵs').
        assert (ϵT s2 s1 ϵs' <~> ϵT s2 s2 ϵs'') as ϵT_21_22 
            by eauto using LR_irrel.
        assert (ϵT s1 s2 ϵs <~> ϵT s2 s2 ϵs'') as ϵT_12_22
            by eauto using LR_irrel.
        unfold ϵs' in ϵT_21_22.
        split. 
        + split; rewrite ϵT_21_22; rewrite ϵT_12_22; eauto.
        + unfold ϵs'', ϵs' in ϵT_12_22. eauto. }
      split. 2:split.
      + split; intros; rewrite H in *. 
        ++ destruct H2. split; eauto using conv_sym.
           intros. destruct (H1 _ _ ϵs) as ((ϵT_sym & ϵT_trans) & _). eapply ϵT_sym.
           eapply (proj1 (H0 _ _ _)). 
           eapply LR_erasure; eauto. 
           +++ eapply aconv_app; eauto using aconv_refl, validity_conv_left, LR_escape_tm, validity_conv_right.
           +++ eapply aconv_conv; eauto using conv_aux, conv_sym, LR_escape_tm.
               eapply aconv_app; eauto using LR_escape_tm, validity_conv_right, conv_sym, conv_ty_in_ctx_conv.
               eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi.
        ++ destruct H2, H3. split; eauto using conv_trans.
           intros. destruct (H1 _ _ ϵs) as ((ϵT_sym & ϵT_trans) & _). eapply ϵT_trans.
           eapply H4. clear H4. eapply (proj2 (H0 _ _ _)). 
           eapply LR_erasure; eauto. 
           +++ eapply aconv_app; eauto using aconv_refl, validity_conv_left, LR_escape_tm, validity_conv_right.
           +++ eapply aconv_conv.
               eapply aconv_app; eauto using LR_escape_tm, validity_conv_left, refl_ty, conv_sym, conv_ty_in_ctx_conv.
               eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi.
               eauto 6 using conv_aux, conv_sym, LR_escape_tm, validity_conv_right, refl_ty.
      + eapply LR_pi; eauto using conv_sym, conv_ty_in_ctx_conv. 
        ++ intros.
            destruct (H1 _ _ (ϵS_sym _ _ ϵs)) as (_ & H3' & _).
            eapply LR_iff_rel.  eapply (proj1 (H0 _ _ _)). eapply H3'.
        ++ split; intros; rewrite H in *. 
            +++ destruct H2. split. 
                eauto using conv_conv, conv_pi. 
                intros. eapply LR_erasure; eauto. 
                ++++ eapply aconv_app; eauto using aconv_refl, validity_conv_left, LR_escape_tm, validity_conv_right.
                ++++ eapply aconv_conv. 
                     eapply aconv_app; eauto using aconv_refl, validity_conv_left, LR_escape_tm, validity_conv_right, conv_ty_in_ctx_conv, conv_sym.
                     eapply aconv_conv; eauto using validity_conv_right, aconv_refl, conv_pi. 
                     eauto using conv_sym, LR_escape_tm, conv_aux.
            +++ destruct H2. split. 
                eauto using conv_conv, conv_pi, conv_sym.
                intros. 
                eapply (helper_ϵT_irrel ϵT).
                eapply LR_erasure; eauto.
                ++++ eapply aconv_conv.
                     eapply aconv_app; eauto using conv_sym, conv_ty_in_ctx_conv, validity_conv_left, aconv_refl, LR_escape_tm, type_conv.
                     eauto 6 using conv_sym, conv_aux, LR_escape_tm, validity_conv_left, type_conv. Unshelve. eauto.
                ++++ eapply aconv_conv.
                     eapply aconv_app; eauto using validity_conv_right, type_conv, conv_sym, LR_escape_tm. 
                     eapply aconv_conv; eauto using validity_conv_right, aconv_refl, conv_pi, conv_sym, conv_ty_in_ctx_conv.
                     eauto 7 using conv_aux, LR_escape_tm, conv_sym, validity_conv_left, refl_ty.
      + intros. 
      
        pose proof H2 as H2'. unshelve eapply LR_inv in H2. shelve. eauto. 
        destruct H2 as (S' & T' & ϵS' & ϵT' & _ & _ & C_red & S2_eq_S' & T2_eq_T' & LR_S' & LR_T' & R'_iff).

        assert (ϵS <~> ϵS') as ϵS_iff_ϵS' by eauto using LR_irrel.

        assert (forall s1 s2 ϵs, ϵT s1 s2 ϵs <~> ϵT' s1 s2 (proj1 (ϵS_iff_ϵS' _ _) ϵs)) as ϵT_iff_ϵT'.
        { intros. destruct (H1 _ _ (ϵS_sym _ _ ϵs)) as (_ & K & _).
          pose (ϵs' := proj1 (ϵS_iff_ϵS' _ _) ϵs).
          pose (K' := LR_T' _ _ ϵs'). pose proof (L := LR_irrel _ _ _ _ _ _ K K').
          destruct (H0 _ _ ϵs) as (L' & _). rewrite L'. rewrite L. unfold ϵs'. 
          split; eauto. } 

        split.
        ++ eapply (LR_pi _ _ _ _ _ _ ϵS' _ _ ϵT'); eauto using conv_trans, conv_sym, conv_ty_in_ctx_conv.
            +++ eapply LR_S_trans in LR_S' as (S1_eq_S' & _). eauto.
            +++ intros. pose proof (ϵs' := proj2 (ϵS_iff_ϵS' s1 s2) ϵs).
                eapply ϵS_sym in ϵs' as ϵs''. 
                eapply PER_refl in ϵs''; eauto.
                rewrite ϵS_iff_ϵS' in ϵs''.
                pose (LR_T'' := LR_T' _ _ ϵs'').
                destruct (H1 _ _ ϵs') as (K & K1 & K2).
                unshelve eapply (proj1 (K2 _ _ _)).
                eapply LR_iff_rel. 2: apply LR_T''. 
                split; intros ϵT'_t_u;
                eapply (helper_ϵT_irrel ϵT'); eapply (helper_ϵT_irrel ϵT') in ϵT'_t_u;rewrite <- ϵT_iff_ϵT'; rewrite <- ϵT_iff_ϵT' in ϵT'_t_u.
                ++++ rewrite (proj2 (H0 _ _ _)). eauto.
                ++++ rewrite (proj2 (H0 _ _ _)) in ϵT'_t_u. eauto. 
            +++ intros; split; intros; rewrite R'_iff in *.
                * destruct H2. split. eauto using conv_conv, conv_pi, conv_sym. 
                  intros. eapply LR_erasure; eauto. 
                  ** eapply aconv_app; eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, type_conv, validity_conv_left, aconv_refl.
                  ** eapply aconv_conv. 
                     eapply aconv_app; eauto using validity_conv_right, refl_ty, conv_ty_in_ctx_conv, LR_escape_tm, conv_sym, type_conv.
                     eapply aconv_conv; eauto using validity_conv_right, aconv_refl, conv_pi.
                     eauto using conv_aux, LR_escape_tm, conv_sym. Unshelve. eauto. eauto.
                * destruct H2. split. eauto using conv_conv, conv_pi.
                intros. eapply LR_erasure; eauto. 
                ** eapply aconv_conv. 
                   eapply aconv_app; eauto using LR_escape_tm, validity_conv_left, type_conv, conv_sym, aconv_refl.
                   eauto 7 using conv_aux, LR_escape_tm, validity_conv_left, type_conv, conv_sym, refl_ty.
                ** eapply aconv_conv.
                   eapply aconv_app; eauto using validity_conv_right, refl_ty, conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, type_conv.
                   eapply aconv_conv; eauto using validity_conv_right, aconv_refl, conv_sym, conv_trans, conv_pi, conv_ty_in_ctx_conv.
                   eauto using conv_aux, LR_escape_tm, conv_sym, conv_conv.
        ++ intros; split; intro; rewrite H in *; rewrite R'_iff in *.
            +++ destruct H2. split. eauto using conv_conv, conv_pi. 
                intros. eapply (helper_ϵT_irrel ϵT'). rewrite <- ϵT_iff_ϵT'. 
                eapply LR_erasure; eauto.
                * eapply aconv_app; eauto using LR_escape_tm, validity_conv_left, type_conv, conv_sym, aconv_refl.
                * eapply aconv_conv.
                  eapply aconv_app; eauto using LR_escape_tm, validity_conv_right.
                  eapply aconv_conv; eauto using validity_conv_right, aconv_refl, conv_pi.
                  eauto 6 using LR_escape_tm, conv_aux, conv_sym, conv_conv. 
                  Unshelve. apply ϵS_iff_ϵS'. eauto.
            +++ destruct H2. split. eauto using conv_conv, conv_pi, conv_sym.
                intros. rewrite ϵT_iff_ϵT'.
                eapply LR_erasure; eauto.
                * eapply aconv_app; eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, validity_conv_left, validity_conv_left, aconv_refl.
                * eapply aconv_conv.
                  eapply aconv_app; eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, validity_conv_right, type_conv.
                  eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi.
                  eauto using conv_aux, conv_sym, LR_escape_tm.
Qed.


Corollary old_LR_sym l A B R : LR l A B R -> LR l B A R.
Proof.
    intros. eapply LR_basic_props in H as (_ & H & _). eauto.
Qed.

Corollary old_LR_trans l A B C R R0 : LR l A B R -> LR l B C R0 -> LR l A C R.
Proof.
    intros. eapply LR_basic_props in H as (_ & _ & H). eapply H in H0 as (H1 & H2).
    eapply LR_iff_rel; eauto. symmetry. eauto.
Qed.

Corollary old_LR_sym_tm l A B R t u : LR l A B R -> R t u -> R u t.
Proof.
    intros. eapply LR_basic_props in H as ((sym & trans) & _). eauto.
Qed.

Corollary old_LR_trans_tm l A B R t u v : LR l A B R -> R t u -> R u v -> R t v.
Proof.
    intros. eapply LR_basic_props in H as ((sym & trans) & _). eauto.
Qed.


Definition TmLR l t u A := exists B R, LR l A B R /\ R t u.

Notation "⊩< l > t ≡ u : A" := (TmLR l t u A) (at level 50, t, u, A at next level).


Lemma LR_conv l A B t u R : 
    LR l A B R -> TmLR l t u A -> TmLR l t u B.
Proof.
    intros. destruct H0 as (B' & R' & LR & R'_t_u).
    eapply LR_irrel in R'_t_u as R_t_u. 2: apply H. 2:eauto.
    exists A. exists R. split; auto. eauto using LR_sym.
Qed.

End old_basics_props_proof.



Reserved Notation "⊩s σ ≡ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive LR_subst : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
| LR_sempty (σ τ : nat -> term) : ⊩s σ ≡ τ : ∙
| LR_scons (σ τ : nat -> term) (Δ : ctx) l A R :
  ⊩s (↑ >> σ) ≡ (↑ >> τ) : Δ -> 
  LR l (A <[ (↑ >> σ) ]) (A <[ (↑ >> τ)] ) R ->
  R (σ var_zero) (τ var_zero) ->
  ⊩s σ ≡ τ : Δ ,, (l , A)
where "⊩s σ ≡ τ : Δ" := (LR_subst Δ σ τ).

Lemma LR_subst_escape σ τ Δ : LR_subst Δ σ τ -> ∙ ⊢s σ ≡ τ : Δ.
Proof.
    intro. induction H. eauto using ConvSubst.
    eapply LR_escape_tm in H1; eauto. eauto using ConvSubst.
Qed.

Lemma LR_subst_sym σ τ Δ : LR_subst Δ σ τ -> LR_subst Δ τ σ.
Proof.
    intros. induction H. eauto using LR_subst.
    eapply LR_sym_tm in H1; eauto. eapply LR_sym in H0. eauto using LR_subst.
Qed.

Lemma LR_subst_trans σ τ θ Δ : LR_subst Δ σ τ -> LR_subst Δ τ θ -> LR_subst Δ σ θ.
Proof.
    intros. generalize θ H0. clear θ H0. induction H. eauto using LR_subst.
    intros. dependent destruction H2. 
    assert (R <~> R0) by eauto using LR_irrel, LR_sym.
    rewrite <- H5 in H4.
    eapply LR_trans_tm in H4; eauto. 
    eapply LR_trans in H3; eauto.
    eauto using LR_subst.
Qed.

Definition LRv Γ l t u A := 
    forall σ1 σ2, 
        LR_subst Γ σ1 σ2 -> 
        exists R, LR l (A <[ σ1 ]) (A <[ σ2 ]) R /\ 
        R (t <[ σ1 ]) (u <[ σ2 ]).

Lemma LRv_sym Γ l t u A : LRv Γ l t u A -> LRv Γ l u t A.
Proof.
    intros ϵtu. unfold LRv. intros σ1 σ2 ϵσ12. 
    destruct (ϵtu _ _ ϵσ12) as (R & ϵA & ϵt). exists R. split; auto.
    eapply LR_subst_sym in ϵσ12 as ϵσ21. destruct (ϵtu _ _ ϵσ21) as (R' & ϵA' & ϵt').
    eapply LR_sym_tm in ϵt'; eauto. eapply LR_sym in ϵA'. 
    eapply LR_irrel in ϵA; eauto. eapply ϵA. auto.
Qed.

Lemma LRv_trans Γ l t u v A : LRv Γ l t v A -> LRv Γ l v u A -> LRv Γ l t u A.
Proof.
    intros ϵtv ϵvu. unfold LRv. intros σ1 σ2 ϵσ12.  
    destruct (ϵtv _ _ ϵσ12) as (R & ϵA & ϵt).
    assert (⊩s σ2 ≡ σ2 : Γ) as ϵσ22 by eauto using LR_subst_trans, LR_subst_sym.
    destruct (ϵvu _ _ ϵσ22) as (R' & ϵA' & ϵt'). 
    assert (R <~> R') as R_iff_R' by eauto using LR_irrel, LR_sym.
    exists R. split; eauto. rewrite <- R_iff_R' in ϵt'.
    eapply LR_trans_tm; eauto.
Qed.

Notation "Γ ⊨< l > t ≡ u : A" := (LRv Γ l t u A) (at level 50, l, t, u, A at next level).
    
Hint Unfold val.

Lemma prefundamental_sort l : LR (Ax l) (Sort l) (Sort l) (fun A B => exists R, LR l A B R).
Proof.
    intros. eapply LR_U.
    1,2: eauto using val_redd_to_whnf, typing, ctx_nil.
    intros; split; eauto.
Qed.

Lemma fundamental_sort Γ l : ⊢ Γ -> Γ ⊨< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l).
Proof.
    intros Γ_Wt. unfold LRv. intros σ1 σ2 ϵσ12.
    eexists. split; eauto using prefundamental_sort. simpl. eexists. eauto using prefundamental_sort.
Qed.

Lemma helper_LR i A B :
    (exists R, LR i A B R) <->
    (exists R, LR (Ax i) (Sort i) (Sort i) R ∧ R A B).
Proof.
    split.
    - intros ϵAB.
      exists (fun A B => exists R, LR i A B R).
      split; eauto using prefundamental_sort.
    - intros ϵsort. destruct ϵsort as (R & ϵsort & ϵAB).
      unshelve eapply LR_inv in ϵsort. shelve. eauto using  val_redd_to_whnf, typing, ctx_nil.
      destruct ϵsort as (_ & _ & _ & equiv). rewrite <- equiv. eauto.
Qed. 


Lemma LRv_apply_subst Γ σ1 σ2 i A1 A2 j B1 B2 : 
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->        
    Γ ,, (i, A1) ⊨< Ax j > B1 ≡ B2 : Sort j -> 
    ⊩s σ1 ≡ σ2 : Γ -> 
    exists ϵA ϵB, 
        LR i (A1 <[ σ1]) (A2 <[ σ2]) ϵA /\
        forall a1 a2 (ϵa : ϵA a1 a2), 
        LR j ((B1 <[ var 0 .: (σ1 >> ren_term S)]) <[a1 ..]) 
             ((B2 <[ var 0 .: (σ2 >> ren_term S)]) <[a2 ..]) 
             (ϵB a1 a2 ϵa).
Proof.
    intros LRv_A12 LRv_B12 ϵσ12. 

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 by eauto using LRv_sym, LRv_trans.
    
    unfold LRv in LRv_A12. simpl in LRv_A12. setoid_rewrite <- helper_LR in LRv_A12.
    eapply LRv_A12 in ϵσ12 as LR_A12. destruct LR_A12 as (ϵA12 & LR_A12).

    unfold LRv in LRv_A11. simpl in LRv_A11. setoid_rewrite <- helper_LR in LRv_A11.
    eapply LRv_A11 in ϵσ12 as LR_A11. destruct LR_A11 as (ϵA11 & LR_A11).
    
    assert (ϵA11 <~> ϵA12) by eauto using LR_irrel.

    exists ϵA12. exists (eT j ϵA12 (B1 <[ var 0 .: (σ1 >> ren_term S)]) (B2 <[ var 0 .: (σ2 >> ren_term S)])). split; eauto; intros.
    assert (⊩s (a1 .: σ1) ≡ (a2 .: σ2) : (Γ ,, (i, A1))) as ϵaσ by eauto using LR_subst, LR_iff_rel.
    unfold LRv in LRv_B12. simpl in LRv_B12. setoid_rewrite <- helper_LR in LRv_B12.
    eapply LRv_B12 in ϵaσ as (ϵB & LR_B).
    eapply LR_iff_rel; eauto. 
    eapply ϵT_iff_eT; eauto.
    Unshelve. 3: eapply ϵB. 
    1,2:ssimpl; eauto.
Qed.


Lemma lift_subst σ1 σ2 i A Γ: 
    ⊢ Γ ,, (i, A) -> 
    ∙ ⊢s σ1 ≡ σ2 : Γ -> 
    ∙ ,, (i, A <[ σ1]) ⊢s ((var 0) .: (σ1 >> ren_term S)) ≡ ((var 0) .: (σ2 >> ren_term S)) : (Γ ,, (i, A)).
Proof.
    intros. eapply conv_scons.
    ssimpl.  admit.
    ssimpl. assert (A <[ σ1 >> ren_term S] = (plus (S 0)) ⋅ (A <[ σ1])). simpl. ssimpl. eauto. 
    rewrite H1. 
    eapply conv_var. eauto. inversion H. 
    eapply validity_subst_conv_left in H0. eapply subst_ty' in H6; eauto.
    eauto using ctx_typing.
Admitted.


Lemma prefundamental_prop A B : 
    ∙ ⊢< Ax prop > A ≡ B : Sort prop -> 
    exists R, LR prop A B R.
Proof.
    intros.
    exists (fun t u => ∙ ⊢< prop > t ≡ u : A).
    rewrite LR_prop_eq. split. eauto. reflexivity.
Qed.

Lemma fundamental_pi {Γ i k A1 B1 A2 B2} : 
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊨< Ax (Ru i (ty k)) > Pi i (ty k) A1 B1 ≡ Pi i (ty k) A2 B2 : Sort (Ru i (ty k)).
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12.
    unfold LRv. intros σ1 σ2 ϵσ12.
    eapply helper_LR.
    
    eapply LRv_apply_subst in ϵσ12 as temp; eauto.
    destruct temp as (ϵA & ϵB & LR_A & LR_B).

    eapply LR_subst_escape in ϵσ12 as Wt_σ12. 
    eapply subst_ty'' in A1_conv_A2 as A1_conv_A2'; eauto.

    eapply lift_subst in Wt_σ12 as Wt_σ_lifted; eauto using validity_conv_left, validity_ty_ctx.
    eapply subst_ty'' in B1_conv_B2 as B1_conv_B2'; eauto.

    eexists. eapply LR_pi; eauto.
    1,2: ssimpl; eauto using val_redd_to_whnf, conv_pi, validity_conv_left,
            validity_conv_right, conv_ty_in_ctx_conv.
    reflexivity.
Qed.
    

Lemma old_fundamental_pi {Γ i j A1 B1 A2 B2} : 
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax j > B1 ≡ B2 : Sort j ->
    Γ,, (i, A1) ⊨< Ax j > B1 ≡ B2 : Sort j ->
    Γ ⊨< Ax (Ru i j) > Pi i j A1 B1 ≡ Pi i j A2 B2 : Sort (Ru i j).
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12.
    unfold LRv. intros σ1 σ2 ϵσ12.
    eapply helper_LR.
    
    eapply LRv_apply_subst in ϵσ12 as temp; eauto.
    destruct temp as (ϵA & ϵB & LR_A & LR_B).

    eapply LR_subst_escape in ϵσ12 as Wt_σ12. 
    eapply subst_ty'' in A1_conv_A2 as A1_conv_A2'; eauto.

    eapply lift_subst in Wt_σ12 as Wt_σ_lifted; eauto using validity_conv_left, validity_ty_ctx.
    eapply subst_ty'' in B1_conv_B2 as B1_conv_B2'; eauto.

    destruct j.
    -  eexists. eapply LR_pi; eauto.
        1,2: ssimpl; eauto using val_redd_to_whnf, conv_pi, validity_conv_left,
            validity_conv_right, conv_ty_in_ctx_conv.
        reflexivity.
    - eapply prefundamental_prop. eauto using (conv_pi _ _ prop).
Qed.

Lemma fundamental_lam Γ i k A1 B1 t1 A2 B2 t2 :
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊢< (ty k) > t1 ≡ t2 : B1 ->
    Γ,, (i, A1) ⊨< (ty k) > t1 ≡ t2 : B1 ->
    Γ ⊨< Ru i (ty k) > lam i (ty k) A1 B1 t1 ≡ lam i (ty k) A2 B2 t2 : Pi i (ty k) A1 B1.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 t1_conv_t2 LRv_t12.
    intros σ1 σ2 ϵσ12.
    
    eapply fundamental_pi in ϵσ12 as LR_Pi12; eauto.
    rewrite <- helper_LR in LR_Pi12.
    destruct LR_Pi12 as (ϵPi12 & LR_Pi12).
    
    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 
        by eauto using LRv_sym, LRv_trans.
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11
        by eauto using LRv_sym, LRv_trans.

    eapply fundamental_pi in ϵσ12 as LR_Pi11. 
    3:exact LRv_A11. 4:exact LRv_B11. 2,3:eauto using validity_conv_left, refl_ty.
    rewrite <- helper_LR in LR_Pi11.
    destruct LR_Pi11 as (ϵPi11 & LR_Pi11).

    assert (ϵPi11 <~> ϵPi12) by eauto using LR_irrel.

    exists ϵPi12. split; eauto using LR_iff_rel.

    unshelve eapply LR_inv in LR_Pi12 as temp. shelve. 
    eapply val_redd_to_whnf. eapply validity_conv_left. eapply LR_escape_ty. eauto. simpl val. eauto. 
    destruct temp as (A1' & B1' & ϵA' & ϵB' & _ & _ & _ & S2_eq_S' & T2_eq_T' & LR_A' & LR_B' & R'_iff).
    rewrite R'_iff. split. admit.
    intros. 
Admitted.

Lemma prefundamental_nat : 
    LR (ty 0) Nat Nat ϵNat.
Proof.
    eapply LR_nat; eauto using val_redd_to_whnf, typing, ctx_typing.
    reflexivity.
Qed.

Lemma fundamental_nat Γ : 
    ⊢ Γ -> 
    Γ ⊨< Ax (ty 0) > Nat ≡ Nat : Sort (ty 0).
Proof.
    unfold LRv. intros. simpl. rewrite <- helper_LR.
    eexists. eapply prefundamental_nat.
Qed.

Lemma fundamental_zero Γ : 
    ⊢ Γ -> 
    Γ ⊨< ty 0 > zero ≡ zero : Nat.
Proof.
    unfold LRv. intros. simpl.
    eexists. split. eauto using prefundamental_nat. 
    exists O. split; simpl; eauto using val_redd_to_whnf, typing, ctx_typing.
Qed.

Lemma fundamental_succ Γ t1 t2 : 
    Γ ⊢< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty 0 > succ t1 ≡ succ t2 : Nat.
Proof.
    unfold LRv. intros. simpl. 
    eexists. split. eauto using prefundamental_nat. 
    destruct (H0 _ _ H1) as (R & LR_nat & lr).
    assert (R <~> ϵNat) by eauto using LR_irrel, prefundamental_nat. 
    rewrite H2 in lr. destruct lr as (k & redd_to_k1 & redd_to_k2).
    exists (S k).
Admitted.

Theorem fundamental : 
    (forall Γ l t A, Γ ⊢< l > t : A -> Γ ⊨< l > t ≡ t : A) /\ 
    (forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A).
Proof.
    apply typing_conversion_mutind; intros.
    1-10:admit.
    - admit.
    - eauto using fundamental_sort.
    - destruct j. 
        + eauto using fundamental_pi.
        + unfold LRv. intros. rewrite <- helper_LR. eapply prefundamental_prop.
          eauto using (conv_pi _ _ prop). admit.
    - admit.
    - admit.
    - eauto using fundamental_nat.
    - eauto using fundamental_zero.
    - 
Admitted.
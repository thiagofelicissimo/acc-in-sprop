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

(* TODO replace conv by reduction *)


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
      intros. rewrite H in H2. destruct H2. eauto using conv_conv, redd_whnf_to_conv, conv_sym.
Qed.


Lemma conv_aux i j s1 s2 S1 T1 T2 : 
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
               destruct (H1 s1 s2 ϵs). 
               destruct (LR_escape _ _ _ _ (LR_T s1 s2 ϵs)) as (T1_s1_conv_T2_s2 & K). 
               destruct (LR_escape _ _ _ _ LR_S). apply H9 in ϵs as s1_conv_s2.
               apply validity_conv_left in s1_conv_s2 as s1_Wt. 
               apply validity_conv_right in s1_conv_s2 as s2_Wt.
               eapply type_conv in s2_Wt; eauto.
               eapply H7; eauto.
               eapply redd_whnf_to_conv in A2_red_pi as pi2.
               eapply validity_conv_right in pi2. 
               eapply type_inv_pi in pi2 as (S2_Wt & T2_Wt). 
                eapply redd_whnf_to_conv in A1_red_pi as pi1.
               eapply validity_conv_right in pi1. 
               eapply type_inv_pi in pi1 as (S1_Wt & T1_Wt).
               eapply aconv_app; eauto using validity_conv_left, refl_ty.
               eapply aconv_conv; eauto.
               eapply aconv_conv. 2: eauto using conv_aux, conv_sym.
               eapply aconv_app; eauto 7 using refl_ty, validity_conv_right, conv_ty_in_ctx_conv. 
               eapply aconv_conv; eauto. eapply conv_trans; eauto. eauto using conv_pi.
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
      assert (ϵS <~> ϵS') by eauto. rewrite R_eq. 
      intros. split. 
      intro.
      unfold ϵPi. rewrite H in H3. destruct H3. split; auto.
      intros. assert (forall s1 s2 ϵs, ϵT s1 s2 (proj2 (H2 s1 s2) ϵs) <~> ϵT' s1 s2 ϵs).
      intros. eapply H1. eauto. 
      apply H5.
      assert (ϵT s1 s2 (proj2 (H2 s1 s2) ϵs) (app i (ty k) S1 T1 t1 s1) (app i (ty k) S2 T2 t2 s2)).
      apply H4.
      destruct (LR_erasure _ _ _ _ (LR_T s1 s2 (proj2 (H2 s1 s2) ϵs))).
      apply LR_escape in LR_S' as temp. pose proof ϵs as s1_conv_s2. apply (proj2 temp) in s1_conv_s2. clear temp.
      eapply H8; eauto. 
      eapply aconv_app; eauto using refl_ty, validity_conv_left, aconv_refl.
      eapply aconv_conv. 2: eapply conv_aux. 2,3:eapply conv_sym. 2:eauto. 2: eapply T1_eq_T2.
      eapply aconv_app; eauto 8 using refl_ty, validity_conv_left, aconv_refl, conv_trans, conv_sym, validity_conv_right, type_conv, conv_ty_in_ctx_conv.
      admit.
      intro. rewrite H.
      unfold ϵPi. destruct H3. split; auto.
      intros. assert (forall s1 s2 ϵs, ϵT s1 s2 ϵs <~> ϵT' s1 s2 (proj1 (H2 s1 s2) ϵs)).
      intros. eapply H1. eauto. 
      apply H5.
      assert (ϵT' s1 s2 (proj1 (H2 s1 s2) ϵs) (app i (ty k) S1 T1 t1 s1) (app i (ty k) S2' T2' t2 s2)).
      apply H4.
      destruct (LR_erasure _ _ _ _ (LR_T' s1 s2 (proj1 (H2 s1 s2) ϵs))).
      eapply H8; eauto. admit. admit.
Admitted.


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


Lemma aux' l A B R :
    LR l A B R ->
    PER R /\
    LR l B A R /\ 
    (forall R' C, LR l B C R' -> LR l A C R' /\ R <~> R') /\
    (forall R' C, LR l C A R' -> LR l C B R' /\ R <~> R').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. split. 2:split. 3:split.
      + destruct p. split; intros; rewrite H0 in *; eauto using conv_sym, conv_trans.
      + rewrite LR_prop_eq. destruct p. split; eauto using conv_sym. intros. 
        rewrite (H0 t u). split; intros; eauto using conv_conv, conv_sym.
      + intros. rewrite LR_prop_eq in *. destruct H, p. split. split; eauto using conv_trans.
        intros. rewrite (H0 t u). split; intros; eauto using conv_conv, conv_sym.
        intros. rewrite (H2 t u). rewrite (H0 t u).  split; intros; eauto using conv_conv, conv_sym.
      + intros. rewrite LR_prop_eq in *. destruct H, p. split. split; eauto using conv_trans.
        intros. rewrite (H2 t u). rewrite (H0 t u).  split; intros; eauto using conv_conv, conv_sym.
    - intros. split. 2:split. 3:split.
      + split; intros; rewrite H in *. 
        destruct H0 as (k & H1 & H2). eexists. split; eauto.
        destruct H0 as (k & t_red & v_red). destruct H1 as (k' & v_red' & u_red).
        exists k. split. eauto. admit.
      + eapply LR_nat; eauto.
      + intros. unshelve eapply LR_inv in H0. shelve. eapply A2_red_nat. 
        destruct H0 as (_ & _ & C_red & R'_iff_nat). 
        split. eauto using LR_nat. intros. rewrite H. rewrite R'_iff_nat. split; auto.
      + intros. admit.
    - intros. split. 2:split. 3:split.
      + split; intros; rewrite H0 in *. destruct H1. destruct (H _ _ _ H1) as (_ & H' & _). eexists. eauto.
        destruct H1. destruct H2. destruct (H _ _ _ H1) as (_ & _  & H' & H'').
        destruct (H' _ _ H2). eexists. eauto.
      + eapply LR_U; eauto. 
      + intros. pose proof H1 as H1'. unshelve eapply LR_inv in H1. shelve. eauto. destruct H1 as (_ & _ & C_red & H').
        split. eapply LR_U; eauto.
        intros; split; rewrite H'; rewrite H0; intros; eauto.
      + admit.
    - intros. 
      destruct H0 as (PER_ϵS & LR_S_sym & LR_S_trans_left & LR_S_trans_right).
      pose proof PER_ϵS as PER_ϵS'.
      destruct PER_ϵS as (ϵS_sym & ϵS_trans). rename PER_ϵS' into PER_ϵS.
      assert (forall s1 s2 ϵs, 
        ϵT s1 s2 ϵs <~> ϵT s2 s1 (ϵS_sym _ _ ϵs) /\ ϵT s1 s2 ϵs <~> ϵT s2 s2 (PER_refl PER_ϵS (ϵS_sym _ _ ϵs))).
      { intros. pose (ϵs' := ϵS_sym _ _ ϵs). pose (ϵs'' := PER_refl PER_ϵS ϵs').
        pose (LR_T_s1_s2 := LR_T _ _ ϵs).
        pose (LR_T_s2_s1 := LR_T _ _ ϵs').
        pose (LR_T_s2_s2 := LR_T _ _ ϵs'').
        destruct (H1 _ _ ϵs) as (_ & LR_T_s1_s2' & _).
        destruct (H1 _ _ ϵs') as (_ & LR_T_s2_s1' & _).
        destruct (H1 _ _ ϵs'') as (_ & _ & LR_T_trans_left & LR_T_trans_right).
        eapply LR_T_trans_left in LR_T_s1_s2' as (_ & HA).
        eapply LR_T_trans_right in LR_T_s2_s1' as (_ & HB).
        unfold ϵs' in HB.
        split.
        + split; intros; rewrite <- HA in *; rewrite <- HB in *; eauto.
        + unfold ϵs'', ϵs' in *. symmetry. rewrite HA. split; intros; eauto. }
      split. 2:split. 3:split.
      + split; intros; rewrite H in *. 
        ++ destruct H2. split; eauto using conv_sym.
           intros. destruct (H1 _ _ ϵs) as ((ϵT_sym & ϵT_trans) & _). eapply ϵT_sym.
           eapply (proj1 (H0 _ _ _)). pose (H3' := H3 _ _ (ϵS_sym _ _ ϵs)). admit.
        ++ destruct H2, H3. split; eauto using conv_trans.
           intros. destruct (H1 _ _ ϵs) as ((ϵT_sym & ϵT_trans) & _). eapply ϵT_trans.
           eapply H4. eapply (proj2 (H0 _ _ _)). pose (H5' := H5 _ _ (PER_refl PER_ϵS (ϵS_sym s1 s2 ϵs))). admit.
      + eapply LR_pi; eauto using conv_sym, conv_ty_in_ctx_conv. intros.
        destruct (H1 _ _ (ϵS_sym _ _ ϵs)) as (_ & H3' & _).
        eapply LR_iff_rel. eapply (proj1 (H0 _ _ _)). eapply H3'.
        split; intros; rewrite H in *. destruct H2. split. admit.
        intros. pose (H3' := H3 _ _ (ϵS_sym s2 s1 (ϵS_sym s1 s2 ϵs))). admit.
        destruct H2. split. admit.
        intros. pose (H3' := H3 _ _ ϵs). admit.
      + intros. pose proof H2 as H2'. unshelve eapply LR_inv in H2. shelve. eauto. 
        destruct H2 as (S' & T' & ϵS' & ϵT' & _ & _ & C_red & S2_eq_S' & T2_eq_T' & LR_S' & LR_T' & R'_iff).
        pose proof (ϵS_iff_ϵS' := LR_irrel _ _ _ _ _ _ LR_S_sym LR_S').
        assert (forall s1 s2, ϵS' s1 s2 -> ϵS' s2 s1) as ϵS'_sym. intros. rewrite <- ϵS_iff_ϵS' in *. eauto.
        (* eassert (∀ (s1 s2 : term) (ϵs : ϵS' s1 s2), LR (ty k) (T1 <[ s1..]) (T' <[ s2..]) _).
        intros. *)

        (* apply ϵS_sym in ϵs as ϵs'. *)
        eassert (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T2 <[ s2..]) (T' <[ s1..]) (ϵT' s2 s1 _)). 
        intros. pose (ϵs' := proj1 (ϵS_iff_ϵS' _ _) (ϵS_sym _ _ ϵs)).  eapply (LR_T' _ _ ϵs').
        (* epose proof (ϵT_iff_ϵT' := fun s1 s2 (ϵs : ϵS s1 s2) => LR_irrel _ _ _ _ _ _ (proj1 (proj2 (H1 _ _ ϵs))) _. 
        shelve. shelve. eapply (LR_T'  _ _ (ϵ)
        assert (ϵS <~> ϵS'). split;  *)
        assert (forall s1 s2 ϵs, ϵT s1 s2 ϵs <~> ϵT' s1 s2 (proj1 (ϵS_iff_ϵS' _ _) ϵs)) as ϵT_iff_ϵT'.
        intros. destruct (H1 _ _ (ϵS_sym _ _ ϵs)) as (_ & K & _).
        pose (ϵs' := proj1 (ϵS_iff_ϵS' _ _) ϵs).
        pose (K' := LR_T' _ _ ϵs'). pose proof (L := LR_irrel _ _ _ _ _ _ K K').
        destruct (H0 _ _ ϵs) as (L' & _). rewrite L'. rewrite L. unfold ϵs'. split; eauto. 

        split.
        ++ eapply (LR_pi _ _ _ _ _ _ ϵS' _ _ ϵT'); eauto using conv_trans, conv_sym, conv_ty_in_ctx_conv. 
           eapply LR_S_trans_left in LR_S' as (S1_eq_S' & _). eauto. 
           intros. pose proof (ϵs' := proj2 (ϵS_iff_ϵS' s1 s2) ϵs).
           eapply ϵS_sym in ϵs' as ϵs''. 
           eapply PER_refl in ϵs''.
           rewrite ϵS_iff_ϵS' in ϵs''.
           pose (LR_T'' := LR_T' _ _ ϵs'').
           destruct (H1 _ _ ϵs') as (K & K1 & K2 & K3).
           unshelve eapply (proj1 (K2 _ _ _)). 2:eauto.
           eapply LR_iff_rel. 2: apply LR_T''. admit.
           intros; split; intros; rewrite R'_iff in *.
           destruct H3. split. admit. 
           intros. pose (H4' := H4 _ _ ϵs). admit.
           destruct H3. split. admit.
           intros. pose (H4' := H4 _ _ ϵs). admit.
        ++ intros; split; intro; rewrite H in *; rewrite R'_iff in *.
           destruct H3. split. admit.
           intros. pose (H4' := H4 _ _ (proj2 (ϵS_iff_ϵS' _ _) ϵs)). rewrite ϵT_iff_ϵT' in *. admit.
           destruct H3. split. admit.
           intros. pose (H4' := H4 _ _ (proj1 (ϵS_iff_ϵS' _ _) ϵs)). rewrite ϵT_iff_ϵT' in *. admit.
      + admit.
Admitted.
           

Definition TmLR l t u A := exists B R, LR l A B R /\ R t u.

Notation "⊩< l > t ≡ u : A" := (TmLR l t u A) (at level 50, t, u, A at next level).


Lemma LR_conv l A B t u R : 
    LR l A B R -> TmLR l t u A -> TmLR l t u B.
Proof.
    intros. destruct H0 as (B' & R' & LR & R'_t_u).
    eapply LR_irrel in R'_t_u as R_t_u. 2: apply H. 2:eauto.
    exists A. exists R. split; auto. admit.
Admitted.



(* --- OLD CODE FROM HERE ---





Inductive LRTy : forall (k : nat) (rec : forall j, j ◃ (ty k) -> LogRel), LogRel :=
| LRTy_nat A1 A2 rec : 
    ∙ ⊢< Ax (ty 0) > A1 ≡ Nat : Sort (ty 0) -> 
    ∙ ⊢< Ax (ty 0) > A2 ≡ Nat : Sort (ty 0) ->
    LRTy 0 rec A1 A2 ϵNat
| LRTy_pi i k rec A1 A2 S1 S2 ϵS T1 T2 ϵT : 
    ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) -> 
    ∙ ⊢< Ax (Ru i (ty k)) > A2 ≡ Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
    LR_leq (Ru i (ty k)) (LRTy (ru i k) rec) rec i leq_ru_left S1 S2 ϵS -> 
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LR_leq (Ru i (ty k)) (LRTy (ru i k) rec) rec (ty k) leq_ru_right T1 T2 (ϵT s1 s2 ϵs)) ->
    LRTy (ru i k) rec A1 A2 (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT)
| LRTy_U l A1 A2 rec : 
    ∙ ⊢< Ax (Ax l) > A1 ≡ Sort l : Sort (Ax l) -> 
    ∙ ⊢< Ax (Ax l) > A2 ≡ Sort l : Sort (Ax l) ->
    LRTy (ax l) rec A1 A2 (fun B1 B2 => exists R, rec l lt_ty_ax B1 B2 R).
(* 
Scheme LR_leq_mut := Induction for LR_leq Sort Prop
with LRTy_mut := Induction for LRTy Sort Prop.
Combined Scheme LR_ty_mutind from LR_leq_mut, LRTy_mut. *)


(* Scheme tree_ind' := Induction for LRTy Sort Prop.


Scheme list_ind' := Induction for LR_leq Sort Prop.
Scheme tree_list_ind := Minimality for LRTy Sort Prop
  with list_ind' := Minimality for LR_leq Sort Prop. *)

Definition LR' (l : level) : LogRel.
    refine (@well_founded_induction_type _ (fun i j => i ◃ j) _ (fun _ => LogRel) _ l).
    - apply wf_inverse_image. apply lt_wf.
    - intros. destruct x.
        + apply (LRTy n). apply X.
        + apply LRΩ.
Defined.
(* 
Definition LR (l : level) (p : Acc (λ i j : level, i ◃ j) l): LogRel.
    refine (@Fix_F _ (fun i j => i ◃ j) (fun _ => LogRel) _ l _).
    - intros. destruct x.
        + apply (LRTy n). apply X.
        + apply LRΩ.
    - exact p. 
    (* apply wf_inverse_image. apply lt_wf. *)
Defined. *)



Definition LR (l : level) : LogRel.
    refine (@Fix_F _ (fun i j => i ◃ j) (fun _ => LogRel) _ l _).
    - intros. destruct x.
        + apply (LRTy n). apply X.
        + apply LRΩ.
    - apply wf_inverse_image. apply lt_wf.
Defined.


Print LR.

Eval compute in (fun i => LR (ty i)).

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

(* Lemma lvl_to_nat_inj *)

Lemma LR_leqeq i j p A B R : LR_leq i (LR i) (fun j _ => LR j) j p A B R <-> LR j A B R.
Proof.
    split.
    - intro H. destruct H.
        + auto.
        + rewrite p. auto.
    - intro H. inversion p.
        + pose proof (f_equal nat_to_lvl H1). repeat rewrite lvl_to_nat_to_lvl in H0. 
          eapply LR_leq_eq. eapply proof_irrel. rewrite <- H0. auto. Unshelve. auto. 
        + assert (lvl_to_nat j < lvl_to_nat i) by lia.
          eapply LR_leq_lt. eapply proof_irrel. auto. Unshelve. auto.
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

Definition LR_nat A1 A2 : 
    ∙ ⊢< Ax (ty 0) > A1 ≡ Nat : Sort (ty 0) -> 
    ∙ ⊢< Ax (ty 0) > A2 ≡ Nat : Sort (ty 0) ->
    LR (ty 0) A1 A2 ϵNat.
Proof.
    intros. rewrite LR_ty_eq.
    constructor; eauto.
Qed.

Definition LR_U l A1 A2 : 
    ∙ ⊢< Ax (Ax l) > A1 ≡ Sort l : Sort (Ax l) -> 
    ∙ ⊢< Ax (Ax l) > A2 ≡ Sort l : Sort (Ax l) ->
    LR (Ax l) A1 A2 (fun B1 B2 => exists R, LR l B1 B2 R).
Proof.
    intros. unfold Ax. rewrite LR_ty_eq.
    constructor; eauto.
Qed.

Definition LR_pi i k A1 A2 S1 S2 ϵS T1 T2 ϵT : 
    ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) -> 
    ∙ ⊢< Ax (Ru i (ty k)) > A2 ≡ Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
    LR i S1 S2 ϵS -> 
    (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) T1 T2 (ϵT s1 s2 ϵs)) ->
    LR (Ru i (ty k)) A1 A2 (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT).
Proof.
    intros. unfold Ru. rewrite LR_ty_eq.
    constructor; eauto.
    - rewrite <- LR_ty_eq. rewrite LR_leqeq. auto.
    - rewrite <- LR_ty_eq. setoid_rewrite LR_leqeq. auto.
Qed.


Definition LR_ind 
    (P : forall l A B R, Prop)
    (p_prop : forall A B R (p : LRΩ A B R), P prop A B R) 
    (p_nat : forall A1 A2
        (A1_red_nat : ∙ ⊢< Ax (ty 0) > A1 ≡ Nat : Sort (ty 0))
        (A2_red_nat : ∙ ⊢< Ax (ty 0) > A2 ≡ Nat : Sort (ty 0)),
        P (ty 0) A1 A2 ϵNat)
    (p_U : forall l A1 A2
        (A1_red_U : ∙ ⊢< Ax (Ax l) > A1 ≡ Sort l : Sort (Ax l))
        (A2_red_U : ∙ ⊢< Ax (Ax l) > A2 ≡ Sort l : Sort (Ax l)),
        P (Ax l) A1 A2 (fun B1 B2 => exists R, LR l B1 B2 R))
    (p_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT
        (A1_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ Pi i (ty k) S1 T1 : Sort (Ru i (ty k)))
        (A2_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A2 ≡ Pi i (ty k) S2 T2 : Sort (Ru i (ty k)))
        (LR_S : LR i S1 S2 ϵS)
        (LR_T : forall s1 s2 (ϵs : ϵS s1 s2), 
                LR (ty k) T1 T2 (ϵT s1 s2 ϵs)),
        P i S1 S2 ϵS -> 
        (forall s1 s2 (ϵs : ϵS s1 s2), P (ty k) T1 T2 (ϵT s1 s2 ϵs)) ->
        P (Ru i (ty k)) A1 A2 (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT))
    (l : level) (A B : term) (R : TmRel) (x : LR l A B R) : P l A B R.
Proof.
    destruct l.
    - rewrite LR_ty_eq in x. 
      set (rec := (λ (l : level) (_ : l ◃ ty n), LR l)).
        assert (rec = (λ (l : level) (_ : l ◃ ty n), LR l)) by reflexivity.
        rewrite <- H in x.
        generalize n rec H A B R x.
        clear n rec H A B R x.
        fix IH 1. intros.
        destruct x.
        + apply p_nat; auto.
        + 
        (* pose proof H2 as H2'. pose proof H3 as H3'. *)
          (* rewrite H in H2, H3.
          rewrite <- LR_ty_eq in H2,H3.
          rewrite LR_leqeq in H2.
          setoid_rewrite LR_leqeq in H3. *)
          apply p_pi; auto.
          ++ rewrite H in H2. rewrite <- LR_ty_eq in H2. rewrite LR_leqeq in H2. auto.
          ++ rewrite H in H3. rewrite <- LR_ty_eq in H3. setoid_rewrite LR_leqeq in H3. auto.
          ++ destruct i. 
           +++ eapply IH; auto. reflexivity. destruct H2. 
           
           rewrite H in H2. rewrite <- LR_ty_eq in H2. rewrite LR_leqeq in H2. rewrite <- LR_ty_eq. auto.
           +++ rewrite H in H2. rewrite <- LR_ty_eq in H2. rewrite LR_leqeq in H2. apply p_prop. rewrite LR_prop_eq in H2. apply H2.
          ++ intros. eapply IH; eauto. reflexivity. 
             rewrite H in H3. rewrite <- LR_ty_eq in H3. setoid_rewrite LR_leqeq in H3. 
             rewrite <- LR_ty_eq. apply H3.
          (* ++ intros. apply LR_ind; auto. *)
        + rewrite H. apply p_U; auto.
    - rewrite LR_prop_eq in x. apply p_prop. auto.
Qed.

Lemma LR_ind 
    (P : forall l A B R, LR l A B R -> Prop)
    (p_prop : forall A B R p, P prop A B R p) 
    (p_nat : forall A1 A2
        (A1_red_nat : ∙ ⊢< Ax (ty 0) > A1 ≡ Nat : Sort (ty 0))
        (A2_red_nat : ∙ ⊢< Ax (ty 0) > A2 ≡ Nat : Sort (ty 0)),
        P _ _ _ _ (LR_nat A1 A2 A1_red_nat A2_red_nat))
    (p_U : forall l A1 A2
        (A1_red_U : ∙ ⊢< Ax (Ax l) > A1 ≡ Sort l : Sort (Ax l))
        (A2_red_U : ∙ ⊢< Ax (Ax l) > A2 ≡ Sort l : Sort (Ax l)),
        P _ _ _ _ (LR_U l A1 A2 A1_red_U A2_red_U))
    (p_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT
        (A1_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ Pi i (ty k) S1 T1 : Sort (Ru i (ty k)))
        (A2_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A2 ≡ Pi i (ty k) S2 T2 : Sort (Ru i (ty k)))
        (LR_S : LR i S1 S2 ϵS)
        (LR_T : forall s1 s2 (ϵs : ϵS s1 s2), 
                LR (ty k) T1 T2 (ϵT s1 s2 ϵs)),
        P _ _ _ _ LR_S -> 
        (forall s1 s2 (ϵs : ϵS s1 s2), P _ _ _ _ (LR_T s1 s2 ϵs)) ->
        P _ _ _ _ (LR_pi i k A1 A2 S1 S2 ϵS T1 T2 ϵT A1_red_pi A2_red_pi LR_S LR_T))
    (l : level) (A B : term) (R : TmRel) (x : LR l A B R) : P _ _ _ _ x.
Proof.
    destruct l.
    - pose proof x as x'. rewrite LR_ty_eq in x'. induction x'.
    + 
    - apply p_prop.

            
Lemma LR_irrel l A B R1 R2 : 
    LR l A B R1 -> 
    LR l A B R2 -> 
    forall t1 t2, R1 t1 t2 <-> R2 t1 t2.
Proof.
    intros LR1 LR2.
    induction l.
    - rewrite LR_ty_eq in *. 
        set (rec := (λ (l : level) (_ : l ◃ ty n), LR l)).
        assert (rec = (λ (l : level) (_ : l ◃ ty n), LR l)) by reflexivity.
        rewrite <- H in LR1, LR2.
    induction LR1. admit. 
    repeat rewrite H in H2. rewrite <- LR_ty_eq in H2. rewrite LR_leqeq in H2. 
    repeat rewrite H in H3. rewrite <- LR_ty_eq in H3.
    setoid_rewrite LR_leqeq in H3.
    induction LR2.
    admit.
    rewrite H in *. rewrite <- LR_ty_eq in *. rewrite LR_leqeq in *.
    setoid_rewrite LR_leqeq in H7.

        admit. admit. admit.
        rewrite <- LR_ty_eq  in H1.
        setoid_rewrite LR_leqeq in H1. 
        rewrite <- LR_ty_eq in H2.
        setoid_rewrite LR_leqeq in H2.
        
        admit.
        rewrite <- LR_ty_eq  in H1, H2.
        setoid_rewrite LR_leqeq in H1. 
        setoid_rewrite LR_leqeq in H2.    
        
        fold LR in *.  admit. all:admit.
    - rewrite LR_prop_eq in *. destruct LR1 as (_ & equiv1). destruct LR2 as (_ & equiv2).
        intros. split; setoid_rewrite equiv1; setoid_rewrite equiv2; auto.
Admitted.
 *)

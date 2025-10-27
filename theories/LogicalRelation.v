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

Inductive ϵNat : TmRel := 
| ϵzero t1 t2 : 
    ∙ ⊢< ty 0 > t1 -->>! zero : Nat ->
    ∙ ⊢< ty 0 > t2 -->>! zero : Nat -> 
    ϵNat t1 t2 
| ϵsucc t1 t2 t1' t2' :
    ∙ ⊢< ty 0 > t1 -->>! succ t1' : Nat ->
    ∙ ⊢< ty 0 > t2 -->>! succ t2' : Nat -> 
    ϵNat t1' t2' -> 
    ϵNat t1 t2.

Lemma ϵNat_escape t1 t2 : ϵNat t1 t2 -> ∙ ⊢< ty 0 > t1 ≡ t2 : Nat.
Proof.
    intros. induction H; eauto 7 using redd_whnf_to_conv, conv_sym, conv_trans, conv_succ.
Qed.

Lemma ϵNat_erasure t1 t2 t1' t2' : 
    ∙ ⊢< ty 0 > t1 ~ t1' : Nat -> 
    ∙ ⊢< ty 0 > t2 ~ t2' : Nat ->
    ϵNat t1 t2 ->
    ϵNat t1' t2'.
Proof.
    intros. generalize t1' t2' H H0. clear t1' t2' H H0.
    induction H1; intros u1 u2 t1_sim_u1 t2_sim_u2.
    - eapply sim_left_redd_whnf_val in H; simpl; eauto.
      eapply sim_left_redd_whnf_val in H0; simpl; eauto.
      eapply ϵzero; eauto.
    - eapply sim_left_redd_whnf_val in H; simpl; eauto.
      eapply sim_left_redd_whnf_val in H0; simpl; eauto.
      eapply ϵsucc; eauto.
Qed.

Lemma ϵNat_sym t1 t2 : 
    ϵNat t1 t2 -> 
    ϵNat t2 t1.
Proof.
    intros.
    induction H.
    - eapply ϵzero; eauto.
    - eapply ϵsucc; eauto.
Qed.

Lemma ϵNat_trans t1 t2 t3 :
    ϵNat t1 t2 ->
    ϵNat t2 t3 -> 
    ϵNat t1 t3.
Proof.
    intro. generalize t3. clear t3. induction H; intros.
    - dependent destruction H1.
        + eapply ϵzero; eauto.
        + eapply redd_whnf_det in H0; eauto. inversion H0.
    - dependent destruction H2. 
        + eapply redd_whnf_det in H0; eauto. inversion H0.
        + eapply redd_whnf_det in H0; eauto. 
          dependent destruction H0.
          eapply ϵsucc; eauto.
Qed.  

(*     
    fun t1 t2 => exists k, ∙ ⊢< ty 0 > t1 -->>! (mk_Nat k) : Nat /\ ∙ ⊢< ty 0 > t2 -->>! (mk_Nat k) : Nat. *)

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
      + intros. rewrite H in H0. 
        eauto using ϵNat_escape, redd_whnf_to_conv, conv_conv, conv_sym.
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


Lemma LR_irred l A B R : 
    LR l A B R -> 
    (forall A' B', 
        ∙ ⊢< Ax l > A' -->> A : Sort l ->
        ∙ ⊢< Ax l > B' -->> B : Sort l ->
        LR l A' B' R) 
    /\
    (forall t u t' u', 
        ∙ ⊢< l > t' -->> t : A -> 
        ∙ ⊢< l > u' -->> u : A -> 
        R t u -> 
        R t' u').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. split; intros.
      eapply LR_prop. 2:split;intros. all:try rewrite H0 in *.
      all: eauto 6 using redd_to_conv, conv_sym, conv_trans, conv_conv.
    - split; intros. eapply LR_nat; eauto using redd_comp_redd_whnf.
      rewrite H in *. destruct H2; 
      eauto 8 using ϵzero, ϵsucc, redd_comp_redd_whnf, redd_conv, redd_whnf_to_conv, conv_sym.
    - split; intros. eapply LR_U; eauto using redd_comp_redd_whnf.
      setoid_rewrite H0 in H3. setoid_rewrite H0. destruct H3 as (R' & lr). exists R'.
      eapply H in lr as (K1 & K2). eapply K1; eauto using redd_whnf_to_conv, redd_conv.
    - split; intros. eapply LR_pi; eauto using redd_comp_redd_whnf.
      rewrite H in *. destruct H4. split.
      eapply redd_to_conv in H2, H3. eapply redd_whnf_to_conv in A1_red_pi.
      eapply conv_conv in H2, H3; eauto. eauto using conv_sym, conv_trans.
      intros. eapply (proj2 (H1 _ _ ϵs)); eauto. 
      eauto 6 using redd_app, redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left. 
      eapply redd_conv. eapply redd_app; eauto 8 using redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left, validity_conv_right, type_conv.
      eapply redd_conv; eauto. eauto using conv_trans, conv_pi, redd_whnf_to_conv.
      eauto using LR_escape_tm, conv_aux, conv_sym.
Qed.

Lemma LR_irred_ty l A B A' B' R : 
    ∙ ⊢< Ax l > A' -->> A : Sort l ->
    ∙ ⊢< Ax l > B' -->> B : Sort l ->
    LR l A B R -> 
    LR l A' B' R.
Proof.
    intros. eapply LR_irred in H1 as (H1 & H2). eauto.
Qed.

Lemma LR_irred_tm l A B t u t' u' R : 
    LR l A B R -> 
    ∙ ⊢< l > t' -->> t : A ->
    ∙ ⊢< l > u' -->> u : A ->
    R t u ->
    R t' u'.
Proof.
    intros. eapply LR_irred in H as (H3 & H4). eauto.
Qed.


Lemma LR_redd l A B R : 
    LR l A B R -> 
    (forall A' B', 
        ∙ ⊢< Ax l > A -->> A' : Sort l ->
        ∙ ⊢< Ax l > B -->> B' : Sort l ->
        LR l A' B' R) 
    /\
    (forall t u t' u', 
        ∙ ⊢< l > t -->> t' : A -> 
        ∙ ⊢< l > u -->> u' : A -> 
        R t u -> 
        R t' u').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. split; intros.
      eapply LR_prop. 2:split;intros. all:try rewrite H0 in *.
      all: eauto 6 using redd_to_conv, conv_sym, conv_trans, conv_conv.
    - split; intros. eapply LR_nat; eauto using iredd_comp_redd_whnf.
      rewrite H in *. destruct H2; 
      eauto 8 using ϵzero, ϵsucc, iredd_comp_redd_whnf, redd_conv, redd_whnf_to_conv, conv_sym.
    - split; intros. eapply LR_U; eauto using iredd_comp_redd_whnf.
      setoid_rewrite H0 in H3. setoid_rewrite H0. destruct H3 as (R' & lr). exists R'.
      eapply H in lr as (K1 & K2). eapply K1; eauto using redd_whnf_to_conv, redd_conv.
    - split; intros. eapply LR_pi; eauto using iredd_comp_redd_whnf.
      rewrite H in *. destruct H4. split.
      eapply redd_to_conv in H2, H3. eapply redd_whnf_to_conv in A1_red_pi.
      eapply conv_conv in H2, H3; eauto. eauto using conv_sym, conv_trans.
      intros. eapply (proj2 (H1 _ _ ϵs)); eauto. 
      eauto 6 using redd_app, redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left. 
      eapply redd_conv. eapply redd_app; eauto 8 using redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left, validity_conv_right, type_conv.
      eapply redd_conv; eauto. eauto using conv_trans, conv_pi, redd_whnf_to_conv.
      eauto using LR_escape_tm, conv_aux, conv_sym.
Qed.

Lemma LR_redd_ty l A B A' B' R : 
    ∙ ⊢< Ax l > A -->> A' : Sort l ->
    ∙ ⊢< Ax l > B -->> B' : Sort l ->
    LR l A B R -> 
    LR l A' B' R.
Proof.
    intros. eapply LR_redd in H1 as (H1 & H2). eauto.
Qed.

Lemma LR_redd_tm l A B t u t' u' R : 
    LR l A B R -> 
    ∙ ⊢< l > t -->> t' : A ->
    ∙ ⊢< l > u -->> u' : A ->
    R t u ->
    R t' u'.
Proof.
    intros. eapply LR_redd in H as (H3 & H4). eauto.
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
        + rewrite H in *. eauto 7 using ϵNat_erasure, redd_whnf_to_conv, conv_sym, aconv_conv. 
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
      + setoid_rewrite H. intros. split; eauto using ϵNat_sym.
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
      + intros. rewrite H in *. rewrite H' in *. eauto using ϵNat_trans.
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

(* Lemma LR_prefundamental_pi Γ σ1 σ2 i A1 A2 j B1 B2 : 
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->        
    Γ ,, (i, A1) ⊨< Ax j > B1 ≡ B2 : Sort j -> 
    ⊩s σ1 ≡ σ2 : Γ -> 
    exists ϵA ϵB, 
        LR i (A1 <[ σ1]) (A2 <[ σ2]) ϵA /\
        (forall a1 a2 (ϵa : ϵA a1 a2), 
        LR j ((B1 <[ var 0 .: (σ1 >> ren_term S)]) <[a1 ..]) 
             ((B2 <[ var 0 .: (σ2 >> ren_term S)]) <[a2 ..]) 
             (ϵB a1 a2 ϵa)) /\ 
        LR 
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
Qed. *)


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


Lemma lift_subst2 σ1 σ2 i j B A Γ: 
    ⊢ Γ ,, (i, A) ,,(j, B) -> 
    ∙ ⊢s σ1 ≡ σ2 : Γ -> 
    ∙ ,, (i, A <[ σ1]) ,, (j, B<[var 0 .: σ1 >> ren_term S]) ⊢s ((var 0) .: (var 1 .: (σ1 >> ren_term (S >> S)))) ≡ ((var 0) .: (var 1 .: (σ2 >> ren_term (S >> S)))) : (Γ ,, (i, A)) ,,(j, B).
Proof.
    intros. eapply conv_scons. eapply conv_scons. ssimpl. admit.
    ssimpl. assert (A <[ σ1 >> ren_term (S >> S)] = (plus (S 1)) ⋅ A <[σ1]). ssimpl. reflexivity.
    rewrite H1. eapply conv_var. eauto. shelve.
    ssimpl. assert (B <[ var 1 .: σ1 >> ren_term (S >> S)] = (plus (S 0)) ⋅ B<[ var 0 .: σ1 >> ren_term S]). ssimpl. reflexivity.
    rewrite H1. eapply conv_var. eauto.
    dependent destruction H. eapply lift_subst in H; eauto.
    dependent destruction H. asimpl in H3. 
    econstructor. 
    eauto using validity_ty_ctx, validity_conv_left.
    eapply lift_subst in H1; eauto using validity_ty_ctx. eapply subst_ty'' in H1. 2:eauto using refl_ty. eauto using validity_conv_left.
Admitted.

Lemma prefundamental_pi Γ σ1 σ2 i A1 A2 k B1 B2 : 
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    ⊩s σ1 ≡ σ2 : Γ -> 
    exists ϵA ϵB, 
        let ϵpi := ϵPi i (ty k) (A1 <[ σ1]) (A2 <[ σ2]) ϵA
                (B1 <[ var 0 .: (σ1 >> ren_term S)]) (B2 <[ var 0 .: (σ2 >> ren_term S)]) ϵB in
        LR i (A1 <[ σ1]) (A2 <[ σ2]) ϵA /\
        (forall a1 a2 (ϵa : ϵA a1 a2), 
            LR (ty k) ((B1 <[ var 0 .: (σ1 >> ren_term S)]) <[a1 ..]) 
                ((B2 <[ var 0 .: (σ2 >> ren_term S)]) <[a2 ..]) 
                (ϵB a1 a2 ϵa)) /\
        LR (Ru i (ty k)) ((Pi i (ty k) A1 B1) <[ σ1]) ((Pi i (ty k) A2 B2) <[ σ2]) ϵpi.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 ϵσ12. 

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 by eauto using LRv_sym, LRv_trans.
    
    unfold LRv in LRv_A12. simpl in LRv_A12. setoid_rewrite <- helper_LR in LRv_A12.
    eapply LRv_A12 in ϵσ12 as LR_A12. destruct LR_A12 as (ϵA12 & LR_A12).

    unfold LRv in LRv_A11. simpl in LRv_A11. setoid_rewrite <- helper_LR in LRv_A11.
    eapply LRv_A11 in ϵσ12 as LR_A11. destruct LR_A11 as (ϵA11 & LR_A11).
    
    assert (ϵA11 <~> ϵA12) by eauto using LR_irrel.

    eapply LR_subst_escape in ϵσ12 as Wt_σ12. 
    eapply subst_ty'' in A1_conv_A2 as A1_conv_A2'; eauto.

    eapply lift_subst in Wt_σ12 as Wt_σ_lifted; eauto using validity_conv_left, validity_ty_ctx.
    eapply subst_ty'' in B1_conv_B2 as B1_conv_B2'; eauto.    
    

    pose (ϵB12 := eT (ty k) ϵA12 (B1 <[ (var 0) .: σ1 >> ren_term S]) (B2 <[ (var 0) .: σ2 >> ren_term S])).
    eassert (forall a1 a2 ϵa, LR (ty k) (B1 <[ a1 .: σ1 ]) (B2 <[ a2 .: σ2]) (ϵB12 a1 a2 ϵa)) as LR_B.
    {   intros.
        assert (⊩s (a1 .: σ1) ≡ (a2 .: σ2) : (Γ ,, (i, A1))) as ϵaσ by eauto using LR_subst, LR_iff_rel.
        unfold LRv in LRv_B12. simpl in LRv_B12. setoid_rewrite <- helper_LR in LRv_B12.
        eapply LRv_B12 in ϵaσ as (ϵB' & LR_B).
        eapply LR_iff_rel; eauto. 
        eapply ϵT_iff_eT; eauto. 
        ssimpl. eauto. }

    eexists ϵA12. eexists ϵB12.
    split; eauto. split; intros; ssimpl; eauto.

    eapply LR_pi; eauto.
    1,2: ssimpl; eauto using val_redd_to_whnf, conv_pi, validity_conv_left,
            validity_conv_right, conv_ty_in_ctx_conv.
    Unshelve. 3:exact ϵB12.
    intros; ssimpl; eauto. reflexivity.
Qed.

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
    
    eapply prefundamental_pi in ϵσ12 as temp; eauto.
    destruct temp as (ϵA & ϵB & LR_A & LR_B & LR_pi).
    eexists. eauto.
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

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 
        by eauto using LRv_sym, LRv_trans.
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11
        by eauto using LRv_sym, LRv_trans.

    eapply prefundamental_pi in ϵσ12 as temp. 
    3:exact LRv_A11.  4:exact LRv_B11.
    2,3:eauto using validity_conv_left, refl_ty.
    destruct temp as (ϵA & ϵB & LR_A & LR_B & LR_pi).
    eexists. split. eapply LR_pi. split; eauto.
    ssimpl. eapply conv_lam; eauto 7 using subst_ty'', subst, LR_subst_escape, lift_subst, validity_conv_left, validity_ty_ctx.
    intros.
    assert (⊩s (s1 .: σ1) ≡ (s2 .: σ2) : (Γ ,, (i, A1))) as ϵsσ by eauto using LR_subst, LR_iff_rel.
    eapply LRv_t12 in ϵsσ as temp. destruct temp as (ϵB' & LR_B' & ϵt12).
    pose (LR_B'' := LR_B _ _ ϵs).
    assert (forall B s σ, B <[ (var 0) .: σ >> ren_term S] <[ s..] = B <[ s .: σ]). intros. ssimpl. eauto.
    rewrite 2 H in LR_B''. 
    assert (ϵB s1 s2 ϵs <~> ϵB') by eauto using LR_irrel.
    rewrite <- H0 in ϵt12.
    eapply LR_irred_tm; eauto.

    (* from this point on, it's just technical manipulations to show that the beta redex reduces *)
    eapply redd_step; eauto using redd_refl.
    eapply red_conv. eapply red_beta; fold subst_term; ssimpl.
    all:eauto 9 using refl_ty, subst2, subst_ty, LR_subst_escape, 
        validity_subst_conv_left, validity_conv_left, lift_subst, validity_ty_ctx, LR_escape_tm.
    ssimpl. eauto 6 using LR_subst_escape, validity_subst_conv_left, validity_conv_left, refl_ty, subst_ty'.
    ssimpl. eapply redd_refl. eauto 6 using LR_subst_escape, validity_subst_conv_left, validity_conv_left, refl_ty, subst2.
    
    eapply redd_step; eauto using redd_refl.
    eapply red_conv. eapply red_beta; fold subst_term; ssimpl. 
    all:eauto 10 using refl_ty, subst2, subst_ty'', subst_ty, LR_subst_escape, LR_sym, lift_subst, validity_ty_ctx,
        validity_subst_conv_right, validity_conv_right, validity_subst_conv_left, validity_conv_left, LR_escape_tm, refl_subst.
    
    ssimpl. eauto 6 using subst_ty'', refl_ty, validity_conv_left, subst_conv_sym, LR_subst_escape.
    ssimpl. eapply redd_refl. eauto using validity_conv_right, subst, LR_subst_escape.
Qed.



Lemma fundamental_app Γ i k A1 B1 t1 u1 A2 B2 t2 u2 :
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊢< Ru i (ty k) > t1 ≡ t2 : Pi i (ty k) A1 B1 ->
    Γ ⊨< Ru i (ty k) > t1 ≡ t2 : Pi i (ty k) A1 B1 ->
    Γ ⊢< i > u1 ≡ u2 : A1 ->
    Γ ⊨< i > u1 ≡ u2 : A1 ->
    Γ ⊨< ty k > app i (ty k) A1 B1 t1 u1 ≡ app i (ty k) A2 B2 t2 u2 : B1 <[ u1..].
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12
        t1_conv_t2 LRv_t12 u1_conv_u2 LRv_u12 σ1 σ2 ϵσ.
    
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11 by eauto using LRv_sym, LRv_trans.
    eapply prefundamental_pi in LRv_B11 as temp; eauto using validity_conv_left, refl_ty.
    destruct temp as (ϵA & ϵB & LR_A12 & LR_B11 & LR_pi).
    
    assert (Γ ⊨< i > u1 ≡ u1 : A1) as LRv_u11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_u11 in ϵσ as temp. destruct temp as (ϵA' & LR_A11 & ϵu11).
    assert (ϵA <~> ϵA') as ϵA_iff_ϵA' by eauto using LR_irrel. rewrite <- ϵA_iff_ϵA' in ϵu11.


    eapply LRv_u12 in ϵσ as temp. destruct temp as (ϵA'' & LR_A12' & ϵu12).  
    assert (ϵA <~> ϵA'') by eauto using LR_irrel. rewrite <- H in ϵu12.
    clear ϵA'' LR_A12' H.

    assert (ϵB (u1 <[ σ1]) (u1 <[ σ2]) ϵu11 <~> ϵB (u1 <[ σ1]) (u2 <[ σ2]) ϵu12) 
        as ϵB11_iff_ϵB12 by eauto using LR_irrel.

    pose (LR_Bu12 := LR_B11 _ _ ϵu11). 
    
    eexists (ϵB (u1 <[ σ1 ]) (u1 <[ σ2]) ϵu11). split. 
        - ssimpl.
          assert (forall B σ u, (B <[ (var 0) .: σ >> ren_term S]) <[ u <[ σ] .: var] = B <[ u <[ σ] .: σ]). 
          intros. ssimpl. eauto.
          rewrite 2 H in LR_Bu12. eapply LR_Bu12.
        - eapply LRv_t12 in ϵσ as temp. destruct temp as (ϵpi' & LR_pi' & ϵt).
          eassert (ϵpi' <~> ϵPi _ _ _ _ _ _ _ _) by eauto using LR_irrel. 
          rewrite H in ϵt. destruct ϵt. ssimpl.
          rewrite ϵB11_iff_ϵB12.
          eapply LR_erasure. 4:eapply H1. eauto.
          + eapply aconv_refl. eapply type_app; 
            eauto 8 using subst_ty', LR_subst_escape, validity_conv_left, 
                validity_subst_conv_left, subst2, lift_subst, validity_ty_ctx.

        (* from this point on, it's just technical manipulations to show that the terms are equal up to annotation conversion *)
          + ssimpl. eapply aconv_conv.

            eapply aconv_app; eauto 10 using refl_ty, subst_ty'', LR_subst_escape, validity_conv_right, 
                subst2, validity_subst_conv_right, type_conv, lift_subst, conv_ty_in_ctx_conv.

            eapply subst_ty. eapply validity_subst_conv_right. 
            eapply lift_subst; eauto using validity_conv_right, validity_ty_ctx, ctx_typing, LR_subst_escape, 
                validity_subst_conv_right, refl_subst. 
            eauto using conv_ty_in_ctx_conv.

            eapply aconv_refl. eapply type_conv; eauto using LR_subst_escape, validity_conv_right, validity_subst_conv_right, subst2.
            eapply conv_pi; eauto 9 using LR_subst_escape, subst_ty'', lift_subst, validity_conv_left, validity_ty_ctx, refl_ty.

            ssimpl. eapply subst_ty''; eauto using validity_conv_left, refl_ty. 
            econstructor; ssimpl. eauto using subst_conv_sym, LR_subst_escape. 
            eauto using subst, subst_conv_sym, LR_subst_escape, LR_escape, conv_sym.
Qed.

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
    eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
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
    rewrite H2 in lr. 
    eapply ϵsucc; 
    eauto 6 using val_redd_to_whnf, typing, ctx_typing, 
        ϵNat_escape, validity_conv_left, validity_conv_right.
Qed.

Lemma fundamental_conv Γ l A B t1 t2 :
    Γ ⊢< l > t1 ≡ t2 : A ->
    Γ ⊨< l > t1 ≡ t2 : A ->
    Γ ⊢< Ax l > A ≡ B : Sort l ->
    Γ ⊨< Ax l > A ≡ B : Sort l ->
    Γ ⊨< l > t1 ≡ t2 : B.
Proof.
    intros t1_conv_t2 LRv_t12 A_conv_B LRv_AB. unfold LRv. intros σ1 σ2 ϵσ12.
    eapply LRv_t12 in ϵσ12 as temp.
    destruct temp as (ϵAA & LR_AA & lr).
    exists ϵAA. split; eauto.
    assert (Γ ⊨< Ax l > B ≡ B : Sort l) as LRv_BB by eauto using LRv_sym, LRv_trans.
    eapply LRv_BB in ϵσ12 as temp.
    rewrite <- helper_LR in temp.
    destruct temp as (ϵBB & LR_BB). 
    eapply LR_iff_rel; eauto.
    assert (⊩s σ2 ≡ σ2 : Γ) as ϵσ22 by eauto using LR_subst_sym, LR_subst_trans.
    eapply LRv_AB in ϵσ22 as temp.
    rewrite <- helper_LR in temp.
    destruct temp as (ϵAB & LR_AB).
    assert (ϵAA <~> ϵAB) by eauto using LR_sym, LR_irrel.
    assert (ϵBB <~> ϵAB) by eauto using LR_sym, LR_irrel.
    setoid_rewrite H0. symmetry. eauto.
Qed.

Lemma nth_error_succ {X: Type} (x:X) l n a :
    nth_error (cons x l) (S n) = Some a -> 
    nth_error l n = Some a.
Proof.
    intros. unfold nth_error in H. simpl in H. eauto.
Qed.

Lemma ϵzero' : ϵNat zero zero.
Proof.
    eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
Qed.

Lemma ϵsucc' {t u} : ϵNat t u -> ϵNat (succ t) (succ u).
Proof.
    intros. eapply ϵsucc; eauto 7 using val_redd_to_whnf, typing, ctx_typing, ϵNat_escape, validity_conv_left, validity_conv_right.
Qed.
    
Scheme ϵNat_dep_ind := Induction for ϵNat Sort Prop.


Lemma prefundamental_rec k P1 p_zero1 p_succ1 P2 p_zero2 p_succ2 ϵP:
    ∙ ,, (ty 0, Nat) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ∙  ⊢< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    (∙ ,, (ty 0, Nat)),, (ty k, P1) ⊢< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (forall n1 n2 (ϵn : ϵNat n1 n2), 
        LR (ty k) (P1 <[ n1..]) (P2 <[ n2..]) (ϵP n1 n2 ϵn)) -> 
    ϵP zero zero ϵzero' p_zero1 p_zero2 -> 
    (forall n1 n2 (ϵn : ϵNat n1 n2) t1 t2,
        ϵP n1 n2 ϵn t1 t2 -> 
        ϵP (succ n1) (succ n2) (ϵsucc' ϵn) (p_succ1 <[t1 .: n1 ..]) (p_succ2 <[t2 .: n2 ..])) -> 
    forall n1 n2 (ϵn : ϵNat n1 n2), ϵP n1 n2 ϵn (rec (ty k) P1 p_zero1 p_succ1 n1) (rec (ty k) P2 p_zero2 p_succ2 n2).
Proof.
    intros. generalize n1 n2 ϵn. clear n1 n2 ϵn. 
    apply ϵNat_dep_ind; intros.
    - pose (LR' := H4 _ _ ϵzero'). 
      pose (LR'' := H4 _ _ (ϵzero _ _ r r0)).
      assert (ϵNat t1 zero) as ϵt1zero. eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
      pose (LR''' := H4 _ _ ϵt1zero).
      assert (ϵP zero zero ϵzero' <~> ϵP t1 zero ϵt1zero) by eauto using LR_sym, LR_irrel.
      assert (ϵP t1 t2 (ϵzero t1 t2 r r0) <~> ϵP t1 zero ϵt1zero) by eauto using LR_sym, LR_irrel.
      rewrite H6. rewrite <- H5. 
      destruct r, r0.
      eapply LR_irred_tm; eauto.
      eapply redd_rec_zero; eauto using validity_conv_left.
      eapply redd_conv. eapply redd_rec_zero; 
      eauto 8 using validity_conv_right, subst_ty, aux_subst_1, type_zero, conv_sym, type_conv, ctx_typing, aux_subst_2, conv_ty_in_ctx_conv.
      eapply subst_ty''; eauto using conv_sym.
      econstructor; ssimpl; eauto using ConvSubst, conversion, ctx_typing.
      
    - rename ϵ into ϵn. 
      pose (LR' := H2 _ _ (ϵsucc' ϵn)).
      pose (LR'' := H2 _ _ (ϵsucc _ _ _ _ r r0 ϵn)).
      assert (ϵNat t1 (succ t2')) as ϵt1succt2'. eapply ϵsucc; eauto using val_redd_to_whnf, typing, redd_whnf_to_conv, validity_conv_right.
      pose (LR''' := H2 _ _ ϵt1succt2').
      assert (ϵP (succ t1') (succ t2') (ϵsucc' ϵn) <~> ϵP t1 (succ t2') ϵt1succt2') by eauto using LR_sym, LR_irrel.
      assert (ϵP t1 t2 (ϵsucc t1 t2 t1' t2' r r0 ϵn) <~> ϵP t1 (succ t2') ϵt1succt2') by eauto using LR_sym, LR_irrel.
      rewrite H7. rewrite <- H6.
      destruct r,r0.
      eapply LR_irred_tm; eauto.
      eapply redd_rec_succ; eauto using validity_conv_left.
      eapply redd_conv.
      eapply redd_rec_succ; eauto 8 using validity_conv_right, subst_ty, aux_subst_1, type_zero, conv_sym, type_conv, ctx_typing, aux_subst_2, conv_ty_in_ctx_conv.
      eapply subst_ty''; eauto using conv_sym. 
      econstructor; ssimpl; eauto using ConvSubst, redd_to_conv, conv_sym, conv_trans, LR_escape_tm, prefundamental_nat.
Qed.

Lemma fundamental_rec Γ k P1 p_zero1 p_succ1 t1 P2 p_zero2 p_succ2 t2 : 
    Γ,, (ty 0, Nat) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    Γ,, (ty 0, Nat) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    Γ ⊢< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    Γ ⊨< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    (Γ,, (ty 0, Nat)),, (ty k, P1) ⊢< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (Γ,, (ty 0, Nat)),, (ty k, P1) ⊨< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    Γ ⊢< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty k > rec (ty k) P1 p_zero1 p_succ1 t1 ≡ rec (ty k) P2 p_zero2 p_succ2 t2 : P1 <[ t1..].
Proof.
    intros P1_conv_P2 LRv_P12 pzero1_conv_pzero2 LRv_pzero12
        psucc1_conv_psucc2 LRv_psucc12 t1_conv_t2 LRv_t12.
    unfold LRv. intros σ1 σ2 ϵσ12.

    eapply LRv_t12 in ϵσ12 as temp. 
    simpl in temp. destruct temp as (ϵnat' & LR_nat & ϵt12).
    assert (ϵNat <~> ϵnat') by eauto using LR_irrel, prefundamental_nat. rewrite <- H in ϵt12.
    clear H ϵnat' LR_nat.

    assert (Γ ⊨< ty 0 > t1 ≡ t1 : Nat) as LRv_t11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_t11 in ϵσ12 as temp. 
    simpl in temp. destruct temp as (ϵnat' & LR_nat & ϵt11).
    assert (ϵNat <~> ϵnat') by eauto using LR_irrel, prefundamental_nat. rewrite <- H in ϵt11.
    clear H ϵnat' LR_nat.

    assert (⊩s (t1 <[σ1] .: σ1) ≡ (t1<[σ2] .: σ2) : (Γ ,, (ty 0, Nat))) as ϵtσ by eauto using LR_subst, prefundamental_nat.

    assert (Γ ,, (ty 0, Nat) ⊨< Ax (ty k) > P1 ≡ P1 : Sort (ty k)) as LRv_P11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_P11 in ϵtσ as temp. rewrite <- helper_LR in temp. destruct temp as (ϵP & LR_P).
    exists ϵP. split; ssimpl; eauto. 

    eapply LRv_pzero12 in ϵσ12 as temp.
    destruct temp as (ϵP' & LR_P' & ϵpzero).
    asimpl in LR_P'.


    assert (LR (ty k)  ((P1 <[ var 0 .: σ1 >> ren_term S]) <[t1<[σ1] ..]) ((P2 <[ var 0 .: σ2 >> ren_term S]) <[t2<[σ2] ..]) ϵP). ssimpl. 
    assert (⊩s (t1<[σ1] .: σ1) ≡ (t2<[σ2] .: σ2) : (Γ ,, (ty 0, Nat))) as ϵtσ' by eauto using LR_subst, prefundamental_nat. 
    eapply LRv_P12 in ϵtσ' as temp. rewrite <- helper_LR in temp. destruct temp as (ϵP'' & LR_P'').
    assert (ϵP'' <~> ϵP) by eauto using LR_irrel.
    assert (LR (ty k) (P1 <[ t1 <[ σ1] .: σ1]) (P2 <[ t2 <[ σ2] .: σ2]) ϵP) by eauto using LR_iff_rel.
    eauto.


    eapply (ϵT_iff_eT _ (ty k)). 2:eapply H. 1:eapply prefundamental_nat. Unshelve. 2:eauto.
    Opaque eT.
    eapply (prefundamental_rec _ _ _ _ _ _ _ (eT (ty k) ϵNat (P1 <[ var 0 .: σ1 >> ren_term S]) (P2 <[ var 0 .: σ2 >> ren_term S]))) ; eauto.
    - eapply subst_ty''. eapply (lift_subst _ _ _ Nat); eauto using LR_subst_escape, validity_conv_left, validity_ty_ctx. eauto.
    - ssimpl. assert (P1 <[zero.:σ1] = P1 <[zero .: var] <[σ1]). ssimpl. eauto. rewrite H0. eapply subst; eauto using LR_subst_escape.
    - ssimpl. assert (P1 <[ succ (var 1) .: σ1 >> subst_term (↑ >> (↑ >> var))] = P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] <[ var 0 .: ((↑ 0)__term .: σ1 >> ren_term (↑ >> ↑))]). ssimpl. setoid_rewrite rinstInst'_term_pointwise. ssimpl. reflexivity. rewrite H0. eapply subst. 2:eauto.
    eapply (lift_subst2 _ _ _ _ _ Nat); eauto using LR_subst_escape, validity_conv_left, validity_ty_ctx.
       
    - intros. ssimpl. 
      assert (⊩s (n1 .: σ1) ≡ (n2 .: σ2) : (Γ ,, (ty 0, Nat))) as ϵnσ by eauto using LR_subst, prefundamental_nat. 
      eapply LRv_P12 in ϵnσ as temp. rewrite <- helper_LR in temp. destruct temp as (ϵPn & LR_Pn).
      eapply LR_iff_rel; eauto. eapply ϵT_iff_eT; eauto using prefundamental_nat. ssimpl. eauto.
    - ssimpl. rewrite <- ϵT_iff_eT; eauto using prefundamental_nat. ssimpl. eauto.
      assert (⊩s (zero .: σ1) ≡ (zero .: σ2) : (Γ ,, (ty 0, Nat))) as ϵ0σ by eauto using LR_subst, prefundamental_nat, ϵzero'.
      eapply LRv_P12 in ϵ0σ as temp. rewrite <- helper_LR in temp. destruct temp as (ϵP0 & LR_P0). eapply LR_iff_rel; eauto using LR_irrel.
    - intros. ssimpl. 
      assert (⊩s (n1 .: σ1) ≡ (n2 .: σ2) : (Γ ,, (ty 0, Nat))) as ϵnσ by eauto using LR_subst, prefundamental_nat. 
      eapply LRv_P12 in ϵnσ as temp. rewrite <- helper_LR in temp. destruct temp as (ϵPn & LR_Pn).
      eapply LRv_P11 in ϵnσ as temp. rewrite <- helper_LR in temp. destruct temp as (ϵPn' & LR_Pn').
      assert (ϵPn <~> ϵPn') by eauto using LR_irrel. eapply LR_iff_rel in LR_Pn'. 2:symmetry; eauto.
      clear ϵPn' H1. 
      rewrite <- ϵT_iff_eT in H0; eauto using prefundamental_nat. Unshelve. 3:exact ϵPn. 2:ssimpl;eauto.
      assert (⊩s (t0 .: (n1 .: σ1)) ≡ (t3 .: (n2 .: σ2)) : (Γ ,, (ty 0, Nat)),, (ty k, P1)).
      eapply LR_scons.  eapply LR_scons. ssimpl. eauto.
      Unshelve. 7:exact ϵNat. ssimpl. eapply prefundamental_nat. ssimpl. eauto. 4:exact ϵPn. ssimpl. eauto.
      ssimpl. eauto. eapply LRv_psucc12 in H1 as temp.
      destruct temp as (ϵPsn & LR_Psn & ϵpsucc12). asimpl in LR_Psn.
      rewrite <- ϵT_iff_eT; eauto using prefundamental_nat. ssimpl.
      assert (⊩s ((succ n1) .: σ1) ≡ ((succ n2) .: σ2) : (Γ ,, (ty 0, Nat))) as ϵsnσ.
      eapply LR_scons. ssimpl. eauto. Unshelve. 4:exact ϵNat. ssimpl. eauto using prefundamental_nat.
      ssimpl.  eapply ϵsucc'. eauto.
      eapply LRv_P12 in ϵsnσ as temp. rewrite <- helper_LR in temp. destruct temp as (ϵPsn' & LR_P12').
      eapply LR_iff_rel; eauto using LR_irrel.
Qed.


Lemma fundamental_beta Γ i k A B t u :
    Γ ⊢< Ax i > A : Sort i ->
    Γ ⊨< Ax i > A ≡ A : Sort i ->
    Γ,, (i, A) ⊢< Ax (ty k) > B : Sort (ty k) ->
    Γ,, (i, A) ⊨< Ax (ty k) > B ≡ B : Sort (ty k) ->
    Γ,, (i, A) ⊢< ty k > t : B ->
    Γ,, (i, A) ⊨< ty k > t ≡ t : B ->
    Γ ⊢< i > u : A ->
    Γ ⊨< i > u ≡ u : A ->
    Γ ⊨< ty k > app i (ty k) A B (lam i (ty k) A B t) u ≡ t <[ u..] : B <[ u..].
Proof.
    intros WtA LR_A WtB LR_B Wtt LR_t Wtu LR_u.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply fundamental_lam in LR_t; eauto using refl_ty.
    eapply fundamental_app in LR_u; eauto using refl_ty, conv_lam.
    eapply LR_u in ϵσ as (ϵBu & LR_Bu & ϵbeta).
    exists ϵBu. split; eauto.
    eapply LR_redd_tm; eauto.
Admitted.

Lemma fundamental_rec_zero Γ k P p_zero p_succ :
    Γ,, (ty 0, Nat) ⊢< Ax (ty k) > P : Sort (ty k) ->
    Γ,, (ty 0, Nat) ⊨< Ax (ty k) > P ≡ P : Sort (ty k) ->
    Γ ⊢< ty k > p_zero : P <[ zero..] ->
    Γ ⊨< ty k > p_zero ≡ p_zero : P <[ zero..] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊢< ty k > p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊨< ty k > p_succ ≡ p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    Γ ⊨< ty k > rec (ty k) P p_zero p_succ zero ≡ p_zero : P <[ zero..].
Proof.
    intros WtP LR_P Wtpzero LR_pzero Wtpsucc LR_psucc.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply fundamental_rec in ϵσ as temp; eauto using refl_ty, fundamental_zero, conv_zero, validity_ty_ctx.
    destruct temp as (ϵPzero & LR_Pzero & ϵpzero). exists ϵPzero. split; eauto.
    eapply LR_redd_tm; eauto.
Admitted.


Lemma fundamental_rec_succ Γ k P p_zero p_succ t :
    Γ,, (ty 0, Nat) ⊢< Ax (ty k) > P : Sort (ty k) ->
    Γ,, (ty 0, Nat) ⊨< Ax (ty k) > P ≡ P : Sort (ty k) ->
    Γ ⊢< ty k > p_zero : P <[ zero..] ->
    Γ ⊨< ty k > p_zero ≡ p_zero : P <[ zero..] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊢< ty k > p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊨< ty k > p_succ ≡ p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    Γ ⊢< ty 0 > t : Nat ->
    Γ ⊨< ty 0 > t ≡ t : Nat ->
    Γ ⊨< ty k > rec (ty k) P p_zero p_succ (succ t) ≡ p_succ <[ rec (ty k) P p_zero p_succ t .: t..] : P <[ (succ t)..].
Proof.
    intros WtP LR_P Wtpzero LR_pzero Wtpsucc LR_psucc Wtt LR_t.
    unfold LRv. intros σ1 σ2 ϵσ.
    assert (Γ ⊨< ty 0 > succ t ≡ succ t : Nat) as LR_succt by eauto using fundamental_succ, refl_ty.
    eapply fundamental_rec in LR_succt as temp; eauto using refl_ty, conv_succ.
    eapply temp in ϵσ as temp2. clear temp.
    destruct temp2 as (ϵPSt & LR_PSt & ϵst).
    eexists. split; eauto.
    eapply LR_redd_tm; eauto.
Admitted.


Lemma choice A B R :
    (forall x : A, exists P : B x -> Prop, R x P) -> 
    (forall x P Q, R x P -> R x Q -> forall b, P b -> Q b) ->
    (forall x P Q, (forall b, P b -> Q b ) -> 
        R x P -> R x Q) ->
    exists P : forall x, B x -> Prop, forall x, R x (P x).
intros.
    exists (fun a b => forall P, R a P -> P b).
    intros. destruct (H x).
    eapply H1. 2:exact H2. 
    intros.
    eapply H0. exact H2. all:eauto.
Qed.




Lemma fundamental_var Γ x k A :
    nth_error Γ x = Some (ty k, A) ->
    ⊢ Γ ->
    Γ ⊨< ty k > var x ≡ var x : Init.Nat.add (S x) ⋅ A.
Proof.
    generalize Γ k A. clear Γ k A. induction x; unfold LRv; intros.
    - destruct Γ; dependent destruction H. dependent destruction H1.
      ssimpl. eauto.
    - destruct Γ; dependent destruction H. dependent destruction H1.
      eapply nth_error_succ in x. dependent destruction H0.
      eapply IHx in x; eauto. eapply x in H1 as (R' & LR & lr).
      exists R'. split. ssimpl.
      assert (forall σ, (Init.Nat.add (S x0) ⋅ A) <[ ↑ >> σ] = A <[ Init.Nat.add (S (S x0)) >> σ]). intros. ssimpl. eauto.
      rewrite 2 H1 in LR. eauto. ssimpl. eapply lr. 
Qed.

Lemma fundamental_prop_ty Γ A B : 
    Γ ⊢< Ax prop > A ≡ B : Sort prop -> 
    Γ ⊨< Ax prop > A ≡ B : Sort prop.
Proof.
    intros. unfold LRv. intros.
    rewrite <- helper_LR. 
    eexists (fun t u => ∙ ⊢< prop > t ≡ u : A <[ σ1]). eapply LR_prop.
    2: reflexivity.
    eapply LR_subst_escape in H0. eapply subst in H; eauto. 
Qed.

Lemma fundamental_prop Γ t u A : 
    Γ ⊢< prop > t ≡ u : A -> 
    Γ ⊨< prop > t ≡ u : A.
Proof.
    intros. unfold LRv. intros σ1 σ2 ϵσ12.
    exists (fun t u => ∙ ⊢< prop > t ≡ u : A <[ σ1]).
    split.
    2:eauto using subst, LR_subst_escape.
    eapply LR_prop. 
    2:reflexivity. 
    eauto 6 using subst_ty, validity_conv_left, validity_ty_ty, 
        refl_ty, subst_ty'', LR_subst_escape.    
Qed.


(* used to eliminate the condition l = ty k in the IHs in the proof of fundamental_ty *)
Lemma helper_fund' Γ l t u A :
    Γ ⊢< l > t ≡ u : A -> 
    (forall k, l = ty k -> Γ ⊨< l > t ≡ u : A) <-> Γ ⊨< l > t ≡ u : A.
Proof.
    intros. split. intros.
    destruct l; eauto using fundamental_prop.
    eauto.
Qed.

(* used to eliminate the condition 
        forall k, l = ty k -> Γ ⊢< l > t ≡ u : A -> ...
    from the IHs in the proof of fundamental_ty *)
Lemma helper_fund Γ l t u A :
    Γ ⊢< l > t ≡ u : A -> 
    (forall k, l = ty k -> Γ ⊢< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A) <-> Γ ⊨< l > t ≡ u : A.
Proof.
    intros. split. intros.
    destruct l; eauto using fundamental_prop.
    eauto.
Qed.




Theorem fundamental_ty : 
    (forall Γ l t A, Γ ⊢< l > t : A -> forall k (_temp : l = ty k), Γ ⊢< l > t ≡ t : A -> Γ ⊨< l > t ≡ t : A) /\ 
    (forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> forall k (_temp : l = ty k), Γ ⊢< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A).
Proof.
    apply typing_conversion_mutind; intros.
    all: dependent destruction _temp.
    all: try erewrite helper_fund in *; eauto using refl_ty.
    - eauto using fundamental_var.
    - eauto using fundamental_sort.
    - destruct j. eauto using fundamental_pi, refl_ty. eauto using fundamental_prop_ty.
    - destruct j; dependent destruction x. eauto using fundamental_lam, refl_ty.
    - eauto 6 using fundamental_app, refl_ty.
    - eauto using fundamental_nat.
    - eauto using fundamental_zero.
    - eauto using fundamental_succ, refl_ty.
    - eauto 6 using fundamental_rec, refl_ty.
    - eauto using fundamental_conv, refl_ty.
    - eauto using fundamental_var.
    - eauto using fundamental_sort.
    - destruct j. eauto using fundamental_pi. eauto using fundamental_prop_ty. 
    - destruct j; dependent destruction x. eauto using fundamental_lam.
    - eauto using fundamental_app.
    - eauto using fundamental_nat.
    - eauto using fundamental_zero.
    - eauto using fundamental_succ.
    - eauto 6 using fundamental_rec, refl_ty.
    - eauto using fundamental_conv.
    - eauto using fundamental_beta. 
    - eauto using fundamental_rec_zero.
    - eauto using fundamental_rec_succ.
    - unfold LRv. intros. eapply LR_subst_sym in H1. eapply H in H1 as (ϵA & LR_A & lr).
      eapply LR_sym in LR_A. eapply LR_sym_tm in lr; eauto.
    - unfold LRv. intros. assert (⊩s σ2 ≡ σ2 : Γ) by eauto using LR_subst_sym, LR_subst_trans.
      eapply H in H2 as (ϵA & LR_A & ϵtu). eapply H0 in H3 as (ϵA' & LR_A' & ϵuv).
      assert (ϵA <~> ϵA') by eauto using LR_sym, LR_irrel. rewrite <- H2 in ϵuv.
      eapply LR_trans_tm in ϵuv; eauto.
Qed.

Theorem fundamental Γ l t A : Γ ⊢< l > t : A -> Γ ⊨< l > t ≡ t : A.
Proof.
    intros. destruct l.
    eapply (proj1 fundamental_ty) in H; eauto using refl_ty. 
    eapply refl_ty in H. eapply fundamental_prop in H. eauto.
Qed. 

Lemma mk_nat_typed k : ∙ ⊢< ty 0 > (mk_Nat k) : Nat.
Proof.
    intros. induction k; eauto using typing, ctx_typing.
Qed.

Lemma canonicity_helper t u : ϵNat t u -> exists k, ϵNat t (mk_Nat k).
Proof.
    intros. induction H.
    - exists O. eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
    - destruct IHϵNat as (k & ih). exists (S k).
      eapply ϵsucc; eauto using val_redd_to_whnf, mk_nat_typed, typing.
Qed.


(* we use the predicate ϵNat t (mk_Nat k) to encode the fact that 
    t reduces in mutiple iterations to mk_Nat k *)
Corollary canonicity_red t : 
    ∙ ⊢< ty 0 > t : Nat -> exists k, ϵNat t (mk_Nat k).
Proof.
    intros. eapply fundamental in H; eauto. unfold LRv in H.
    destruct (H var var (LR_sempty _ _)) as (ϵnat' & LR_nat & ϵt).
    simpl in LR_nat. 
    assert (ϵnat' <~> ϵNat) by eauto using LR_irrel, prefundamental_nat.
    rewrite H0 in ϵt. assert (t<[ var ]= t) by (ssimpl; eauto).
    rewrite H1 in ϵt. eauto using canonicity_helper.
Qed.

Corollary canonicity_conv t : 
    ∙ ⊢< ty 0 > t : Nat -> exists k, ∙ ⊢< ty 0 > t ≡ (mk_Nat k) : Nat.
Proof.
    intros. eapply canonicity_red in H as (k & lr). 
    eauto using ϵNat_escape.
Qed.
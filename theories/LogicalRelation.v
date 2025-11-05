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

Definition ϵPi i j S1 S2 (ϵS : TmRel) T1 T2 (ϵT : term -> term -> TmRel) : TmRel 
    := fun f1 f2 => 
        ∙ ⊢< Ru i j > f1 ≡ f2 : Pi i j S1 T1 /\
        forall s1 s2 (ϵs : ϵS s1 s2), ϵT s1 s2 (app i j S1 T1 f1 s1) (app i j S2 T2 f2 s2).

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
    ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    rec i q S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LRTy k rec (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
    R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LRTy k rec A1 A2 R
| LRTy_pi2 k A1 A2 S1 S2 ϵS T1 T2 ϵT R
    (rec : forall j, j ◃ ty k -> LogRel) :
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A1 -->>! Pi (ty k) (ty k) S1 T1 : Sort (Ru (ty k) (ty k)) -> 
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A2 -->>! Pi (ty k) (ty k) S2 T2 : Sort (Ru (ty k) (ty k)) ->
    ∙ ,, (ty k, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LRTy k rec S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LRTy k rec (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
    R <~> (ϵPi (ty k) (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LRTy k rec A1 A2 R
| LRTy_pi3 n k A1 A2 S1 S2 ϵS T1 T2 ϵT R
    (rec : forall j, j ◃ ty n -> LogRel)
    (q : k < n) :
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A1 -->>! Pi (ty n) (ty k) S1 T1 : Sort (Ru (ty n) (ty k)) -> 
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A2 -->>! Pi (ty n) (ty k) S2 T2 : Sort (Ru (ty n) (ty k)) ->
    ∙ ,, (ty n, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LRTy n rec S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        rec (ty k) (ltac :(simpl; lia)) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
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
    ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LR i S1 S2 ϵS -> 
    (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
    R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    LR (Ru i (ty k)) A1 A2 R.
Proof.
    intros. unfold Ru. rewrite LR_ty_eq.
    assert (i ⊴ (ty k) \/ ty k ◃ i) by eauto using Nat.le_gt_cases.
    destruct H5. inversion H5.
    - pose proof (f_equal nat_to_lvl H7) as H'. rewrite lvl_to_nat_to_lvl in H'. rewrite H' in *. 
      simpl. assert (max k k = k) by lia. rewrite H6. eapply LRTy_pi2; eauto. 
      rewrite <- LR_ty_eq. auto.
      rewrite <- LR_ty_eq. auto.
    - assert (ru i k = k). unfold ru. destruct i. simpl in H7. lia. auto.
      rewrite H8. eapply LRTy_pi1; eauto. 
      simpl. lia.
      rewrite <- LR_ty_eq. auto.
    - destruct i. 2:inversion H5.
      simpl in H5. assert (ru (ty n) k = n). unfold ru. lia.
      rewrite H6. eapply LRTy_pi3; eauto. lia. 
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
        (T1_eq_T2 : ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k))
        (LR_S : LR i S1 S2 ϵS)
        (LR_T : forall s1 s2 (ϵs : ϵS s1 s2), 
                LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)),
        R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        P i S1 S2 ϵS -> 
        (forall s1 s2 (ϵs : ϵS s1 s2), P (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
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
        + rewrite H0 in H4. rewrite H0 in H5. 
          rewrite <- LR_ty_eq in H5.
          assert (k = ru i k). unfold ru. destruct i. simpl in q. lia. lia.
          rewrite H8 at 1. eapply p_pi; eauto.
        + rewrite H0 in H4. rewrite <- LR_ty_eq in H4.
          rewrite H0 in x. rewrite <- LR_ty_eq in x.
          assert (k = ru (ty k) k). simpl. lia.
          rewrite H7 at 1. eapply p_pi; eauto.
        + rewrite H0 in *. rewrite <- LR_ty_eq in x.
          assert (ty n = Ru (ty n) (ty k)). simpl. f_equal. lia. rewrite H6 at 1.
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
    - intros. destruct H0 as (H0 & H0'). split; auto.
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
    
Hint Unfold val.

Definition LR_pi' i k l S1 S2 ϵS T1 T2 ϵT R : 
    let A1 := Pi i (ty k) S1 T1 in 
    let A2 := Pi i (ty k) S2 T2 in
    ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    LR i S1 S2 ϵS -> 
    (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
    R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    l = Ru i (ty k) ->
    LR l A1 A2 R.
Proof.
    intros. subst.
    eapply LR_pi; eauto 9 using val_redd_to_whnf, LR_escape_ty, validity_conv_left, validity_conv_right, conv_ty_in_ctx_conv, type_pi.
Qed.


(* Lemma conv_aux {i j s1 s2 S1 T1 T2} : 
    ∙ ⊢< i > s1 ≡ s2 : S1 -> ∙,, (i, S1) ⊢< Ax j > T1 ≡ T2 : Sort j -> ∙ ⊢< Ax j > T1 <[ s1 ..] ≡ T2 <[ s2.. ] : Sort j.
Proof.
    intros. assert (Sort j = Sort j <[ s1 ..]). ssimpl; eauto.
    rewrite H1. eapply subst. eapply (conv_scons _ _ _ ∙  i S1). ssimpl. eapply refl_subst. eapply subst_id. eauto using ctx_typing.
    ssimpl. eauto. eauto.
Qed. *)


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
      eapply redd_conv. eapply redd_app; eauto 8 using redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left, validity_conv_right, type_conv, LR_escape_ty.
      eapply redd_conv; eauto. eauto using conv_trans, conv_pi, redd_whnf_to_conv, LR_escape_ty.
      eauto using LR_escape_tm, subst, aux_subst, conv_sym.
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
      eapply redd_conv. eapply redd_app; eauto 8 using redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left, validity_conv_right, type_conv, LR_escape_ty.
      eapply redd_conv; eauto. eauto using conv_trans, conv_pi, redd_whnf_to_conv, LR_escape_ty.
      eauto using LR_escape_tm, subst, aux_subst, conv_sym.
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
               +++ eapply aconv_app; eauto 7 using validity_conv_left, refl_ty, LR_escape_tm, redd_whnf_to_conv, aconv_conv, LR_escape_ty.
               +++ eapply aconv_conv; eauto using LR_escape_tm, subst, aux_subst, conv_sym.
                   eapply aconv_app; eauto 9 using validity_conv_right, refl_ty, conv_ty_in_ctx_ty, LR_escape_tm, LR_escape_ty, type_conv.
                   eauto using aconv_conv, redd_whnf_to_conv, conv_sym, conv_trans, conv_pi, LR_escape_ty.
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
        ∙ ,, (i, S1) ⊢< Ax (ty k) > T1 ≡ T2 : Sort (ty k) /\
        LR i S1 S2 ϵS /\
        (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) /\
        R <~> ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT
    | _, _ => False
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
      split; eauto. 
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
      destruct H2 as (S2' & T2' & ϵS' & ϵT' & l_eq & A1_red' & A2_red' & T_eq & LR_S' & LR_T' & R_eq).
      assert (ϵS <~> ϵS') by eauto. 
      rewrite R_eq, H. 
      split.
      + intros. destruct H3. split. eauto. intros.
        assert (forall s1 s2, ϵS' s1 s2 -> ϵT s1 s2 <~> ϵT' s1 s2).
            { intros. eapply H1. rewrite H2. eauto. eauto. }
        eapply H5; eauto. eapply H2 in ϵs.  eapply LR_erasure; eauto.  
        ++ eauto 6 using validity_conv_left, aconv_refl, LR_escape_tm.
        ++ eapply aconv_conv;  eauto using LR_escape_tm, subst, aux_subst, conv_sym.
           eapply sim_sym. eapply aconv_app; eauto using conv_trans, conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, LR_escape_ty, type_conv, validity_conv_right.
           eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi, conv_sym, conv_trans, conv_ty_in_ctx_conv, LR_escape_ty.
      + intros. destruct H3. split. eauto. intros.
        assert (forall s1 s2, ϵS s1 s2 -> ϵT' s1 s2 <~> ϵT s1 s2).
            { intros. symmetry. eapply H1. eauto. eapply LR_T'. rewrite <- H2. eauto. }
        eapply H5; eauto.  eapply H2 in ϵs.  eapply LR_erasure; eauto.
        ++ eauto 6 using validity_conv_left, aconv_refl, LR_escape_tm.
        ++ eapply aconv_conv; eauto using LR_escape_tm, subst, aux_subst, conv_sym.
           eapply aconv_app; eauto using conv_trans, conv_sym, conv_ty_in_ctx_conv, LR_escape_tm, LR_escape_ty, type_conv, validity_conv_right.
           eapply aconv_conv; eauto using aconv_refl, validity_conv_right, conv_pi, conv_sym, conv_trans, conv_ty_in_ctx_conv, LR_escape_ty.
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


Definition eT j T1 T2 := 
    fun s1 s2 a1 a2 => forall R, LR j (T1 <[ s1..]) (T2 <[ s2..]) R -> R a1 a2.
 
Lemma ϵT_iff_eT i j S1 S2 ϵS T1 T2 ϵT s1 s2 :
    LR i S1 S2 ϵS ->
    LR j (T1 <[ s1..]) (T2 <[ s2..]) ϵT-> 
    ϵT <~> eT j T1 T2 s1 s2.
Proof.
    intros; split; intros.
    - unfold eT. intros. assert (R <~> ϵT) by eauto using LR_irrel.
      rewrite H3. eauto.
    - eapply H1 in H0. eauto.
Qed.

Opaque eT.

(* TODO: maybe factorize the construction of eT through the following choice principle, 
    to enhance explainability of the construction? *)
Lemma choice A B R :
    (forall x : A, exists P : B x -> Prop, R x P) -> 
    (forall x P Q, R x P -> R x Q -> forall b, P b -> Q b) ->
    (forall x P Q, (forall b, P b -> Q b ) -> 
        R x P -> R x Q) ->
    @sig (forall x, B x -> Prop) (fun P => forall x, R x (P x)).
Proof.
    intros.
    unshelve econstructor. 
    exact (fun a b => forall P, R a P -> P b).
    intros. destruct (H x).
    eapply H1. 2:exact H2. 
    intros.
    eapply H0. exact H2. all:eauto.
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
      exists (ϵPi i (ty k) S2 S1 ϵS' T2 T1 (eT (ty k) T2 T1)).
      split.
      + eapply LR_pi; eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_ty. 
        intros. apply ϵS'_to_ϵS in ϵs as ϵs'.
        destruct (H1 _ _ ϵs') as (ϵT' & LR_T' & ϵT_iff_ϵT'). 
        eapply LR_iff_rel; eauto using ϵT_iff_eT.
        split; eauto.
      + intros; split; intros; rewrite H in *.
        ++  destruct H0. split; eauto using conv_pi, conv_sym, conv_conv, LR_escape_ty.
            intros.  apply ϵS'_to_ϵS in ϵs as ϵs'.
            destruct (H1 _ _ ϵs') as (ϵT' & LR_T' & ϵT_iff_ϵT').
            rewrite <- ϵT_iff_eT; eauto. rewrite <- ϵT_iff_ϵT'. eauto.
        ++  destruct H0. split; eauto 6 using conv_pi, conv_sym, conv_conv, LR_escape_ty.
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
      destruct H2 as (S' & T' & ϵS' & ϵT' & _ & _ & C_red & T2_eq_T' & LR_S' & LR_T' & R'_iff).
      pose proof LR_S' as temp. eapply H0 in temp as (ϵS'' & LR_S'' & ϵS_to). clear H0.
      
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
      assert (ϵSc <~> ϵS') by eauto using LR_irrel. setoid_rewrite H0 in ϵSc_to.
      eapply split_iff in ϵSc_to as (temp1 & temp2).
      assert (forall t u, ϵS t u -> ϵS u t) as ϵS_sym by eauto.
      clear ϵSc LR_Sc H0 temp1 temp2.

      exists (ϵPi i (ty k) S1 S' ϵS'' T1 T' (eT (ty k) T1 T')).
      split.
      + eapply LR_pi; eauto using conv_trans, conv_ty_in_ctx_conv, conv_sym, LR_escape_ty.
        intros. assert (ϵS s1 s2) as ϵs' by eauto. pose (LR_T_1 := LR_T _ _ ϵs').
        assert (ϵS' s2 s2) as ϵs'' by eauto. eapply LR_T' in ϵs'' as LR_T_2. 
        unshelve eapply H1 in LR_T_2. 3:eauto.
        destruct LR_T_2 as (ϵT'' & LR_T'' & ϵT_to).
        eapply LR_iff_rel. 2:eauto.
        eapply ϵT_iff_eT; eauto.
        split; eauto.
      + intros. rewrite H, R'_iff in *.
        destruct H0, H2.
        split; eauto 6 using conv_trans, conv_conv, conv_sym, conv_pi, conv_ty_in_ctx_conv, LR_escape_ty.
        intros.
        assert (ϵS s1 s2) as ϵs' by eauto. pose (LR_T_1 := LR_T _ _ ϵs').
        assert (ϵS' s2 s2) as ϵs'' by eauto. pose (LR_T_2 := LR_T' _ _ ϵs'').
        unshelve eapply H1 in LR_T_2. 3: eauto. 
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



Lemma lift_subst σ1 σ2 i A A' Γ: 
    ⊢ Γ ,, (i, A) -> 
    ∙ ⊢s σ1 ≡ σ2 : Γ -> 
    A' = A <[ σ1] ->
    ∙ ,, (i, A') ⊢s ((var 0) .: (σ1 >> ren_term S)) ≡ ((var 0) .: (σ2 >> ren_term S)) : (Γ ,, (i, A)).
Proof.
    intros. subst. eapply conv_scons.
    ssimpl.  admit. (* consequence of weakening *)
    ssimpl. assert (A <[ σ1 >> ren_term S] = (plus (S 0)) ⋅ (A <[ σ1])). simpl. ssimpl. eauto. 
    rewrite H1. 
    eapply conv_var. eauto. inversion H. 
    eapply validity_subst_conv_left in H0. 
    econstructor. econstructor.
    eauto using validity_conv_left, subst, refl_subst, refl_ty.
Admitted.


Lemma lift_subst2 σ1 σ2 i j B A _A _B Γ: 
    ⊢ Γ ,, (i, A) ,,(j, B) -> 
    ∙ ⊢s σ1 ≡ σ2 : Γ -> 
    _A = A <[ σ1] ->
    _B = B<[var 0 .: σ1 >> ren_term S] ->
    ∙ ,, (i, _A) ,, (j, _B) ⊢s ((var 0) .: (var 1 .: (σ1 >> ren_term (S >> S)))) ≡ ((var 0) .: (var 1 .: (σ2 >> ren_term (S >> S)))) : (Γ ,, (i, A)) ,,(j, B).
Proof.
    intros. subst. eapply conv_scons. eapply conv_scons. ssimpl. admit. (* consequence of weakening *)
    ssimpl. assert (A <[ σ1 >> ren_term (S >> S)] = (plus (S 1)) ⋅ A <[σ1]). ssimpl. reflexivity.
    rewrite H1. eapply conv_var. eauto. shelve.
    ssimpl. assert (B <[ var 1 .: σ1 >> ren_term (S >> S)] = (plus (S 0)) ⋅ B<[ var 0 .: σ1 >> ren_term S]). ssimpl. reflexivity.
    rewrite H1. eapply conv_var. eauto.
    dependent destruction H. eapply lift_subst in H; eauto.
    dependent destruction H. asimpl in H3. 
    econstructor. 
    eauto using validity_ty_ctx, validity_conv_left.
    eapply lift_subst in H1; eauto using validity_ty_ctx. 
    eauto using validity_conv_left, subst, refl_subst, refl_ty.
Admitted.



Lemma getLR_of_motive_aux {Γ i k A1 ϵA P1 P2 σ1 σ2} : 
    LR i (A1 <[σ1]) (A1 <[σ2]) ϵA ->
    Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) -> 
    ⊩s σ1 ≡ σ2 : Γ -> 
    let eP := eT (ty k) (P1 <[ (var 0) .: σ1 >> ren_term S]) (P2 <[ (var 0) .: σ2 >> ren_term S]) in
    ∀ (b1 b2 : term) (ϵb : ϵA b1 b2), 
        (LR (ty k) (P1 <[ b1 .: σ1 ]) (P1 <[ b2 .: σ2 ]) (eP b1 b2))
        /\ (LR (ty k) (P1 <[ b1 .: σ1 ]) (P2 <[ b2 .: σ2 ]) (eP b1 b2))
        /\ (forall b3 (ϵb' : ϵA b1 b3), LR (ty k) (P1 <[ b1 .: σ1 ]) (P1 <[ b3 .: σ2 ]) (eP b1 b2)).
Proof.
    intros.
    assert (⊩s (b1 .: σ1) ≡ (b2 .: σ2) : (Γ ,, (i, A1))) as ϵaσ. 
    unshelve econstructor. exact ϵA. ssimpl. eauto. ssimpl. eauto.
    ssimpl. eauto. 
    eapply H0 in ϵaσ as temp.  rewrite <- helper_LR in temp.
    destruct temp as (ϵPaσ & LR_Paσ). 
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P1 : Sort (ty k)) as LRv_P11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_P11 in ϵaσ as temp. rewrite <- helper_LR in temp.
    destruct temp as (ϵPaσ' & LR_Paσ').
    split. eapply LR_iff_rel; eauto. eapply ϵT_iff_eT; eauto. ssimpl. eauto using LR_iff_rel, LR_irrel.
    split. eapply LR_iff_rel; eauto. eapply ϵT_iff_eT; eauto. ssimpl. eauto.
    intros. 
    assert (⊩s (b1 .: σ1) ≡ (b3 .: σ2) : (Γ ,, (i, A1))) as ϵaσ'. 
    unshelve econstructor. exact ϵA. ssimpl. eauto. ssimpl. eauto.
    ssimpl. eauto.
    eapply LRv_P11 in ϵaσ' as temp.  rewrite <- helper_LR in temp.
    destruct temp as (ϵPaσ'' & LR_Paσ''). 
    eapply LR_iff_rel; eauto.  eapply ϵT_iff_eT; eauto.  ssimpl. eauto using LR_iff_rel, LR_irrel.
Qed.

Corollary getLR_of_motive {Γ i k A1 ϵA P1 P2 σ1 σ2} : 
    LR i (A1 <[σ1]) (A1 <[σ2]) ϵA ->
    Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) -> 
    ⊩s σ1 ≡ σ2 : Γ -> 
    exists eP, 
        eP = eT (ty k) (P1 <[ (var 0) .: σ1 >> ren_term S]) (P2 <[ (var 0) .: σ2 >> ren_term S]) /\
        (∀ (b1 b2 : term) (ϵb : ϵA b1 b2), (LR (ty k) (P1 <[ b1 .: σ1 ]) (P1 <[ b2 .: σ2 ]) (eP b1 b2))) /\
        (∀ (b1 b2 : term) (ϵb : ϵA b1 b2), (LR (ty k) (P1 <[ b1 .: σ1 ]) (P2 <[ b2 .: σ2 ]) (eP b1 b2))) /\
        (∀ (b1 b2 b3 : term) (ϵb : ϵA b1 b2) (ϵb' : ϵA b1 b3), (LR (ty k) (P1 <[ b1 .: σ1 ]) (P1 <[ b3 .: σ2 ]) (eP b1 b2))).
Proof.
    intros. eexists. split. reflexivity. 
    split. 2:split.
    all:intros; eapply getLR_of_motive_aux in ϵb as temp; eauto; destruct temp as (K1 & K2 & K3); eauto.
Qed.

Lemma LRv_to_LR_ty Γ A1 A2 i σ1 σ2 : 
    ⊩s σ1 ≡ σ2 : Γ -> 
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    exists ϵA, LR i (A1<[σ1]) (A2<[σ2]) ϵA.
Proof.
    intros ϵσ LRv_A12. 
    eapply LRv_A12 in ϵσ.
    rewrite <- helper_LR in ϵσ.
    eauto.
Qed.

Lemma LRv_to_LR_ty_copy Γ A1 A2 A1' A2' ϵA i σ1 σ2 : 
    ⊩s σ1 ≡ σ2 : Γ -> 
    A1' = A1<[ σ1] ->
    LR i A1' A2' ϵA ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    LR i (A1<[σ1]) (A2<[σ2]) ϵA.
Proof.
    intros ϵσ eq LR_A' LRv_A12. subst. 
    eapply LRv_A12 in ϵσ.
    rewrite <- helper_LR in ϵσ.
    destruct ϵσ as (ϵA' & LR_A).
    eapply LR_iff_rel; eauto. 
    eauto using LR_irrel.
Qed.

Lemma LRv_to_LR_tm Γ A1 A1' A2 ϵA i t1 t2 σ1 σ2 : 
    ⊩s σ1 ≡ σ2 : Γ -> 
    A1' = A1<[ σ1] ->
    LR i A1' A2 ϵA -> 
    Γ ⊨< i > t1 ≡ t2 : A1 ->
    ϵA (t1<[σ1]) (t2<[σ2]).
Proof.
    intros ϵσ eq LR_A LRv_t12.
    subst. 
    eapply LRv_t12 in ϵσ as temp.
    destruct temp as (ϵA' & LR_A' & ϵt).
    assert (ϵA <~> ϵA') as ϵA_iff_ϵA' by eauto using LR_irrel.
    rewrite ϵA_iff_ϵA'. eauto. 
Qed.

Lemma prefundamental_pi i A1 A2 k ϵA ϵB B1 B2 : 
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    LR i A1 A2 ϵA ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    (forall a1 a2 (ϵa : ϵA a1 a2), LR (ty k) (B1 <[ a1..]) (B2 <[ a2..]) (ϵB a1 a2)) -> 
    let ϵpi := ϵPi i (ty k) A1 A2 ϵA B1 B2 ϵB in 
    LR (Ru i (ty k)) (Pi i (ty k) A1 B1) (Pi i (ty k) A2 B2) ϵpi.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 ϵpi.
    eapply LR_pi'; eauto.
    split; eauto.
Qed.

Lemma fundamental_common_pi Γ σ1 σ2 i A1 A2 k B1 B2 : 
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    ⊩s σ1 ≡ σ2 : Γ -> 
    exists ϵA ϵB, 
        let ϵpi := ϵPi i (ty k) (A1 <[ σ1]) (A2 <[ σ2]) ϵA
                (B1 <[ var 0 .: (σ1 >> ren_term S)]) (B2 <[ var 0 .: (σ2 >> ren_term S)]) ϵB in
        LR i (A1 <[ σ1]) (A2 <[ σ2]) ϵA /\
        (forall a1 a2 (ϵa : ϵA a1 a2), LR (ty k) (B1 <[ a1 .: σ1]) (B2 <[ a2 .: σ2]) (ϵB a1 a2)) /\
        LR (Ru i (ty k)) ((Pi i (ty k) A1 B1) <[ σ1]) ((Pi i (ty k) A2 B2) <[ σ2]) ϵpi.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 ϵσ12. 

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_A12 as temp; eauto. destruct temp as (ϵA & LR_A12).
    eapply LRv_to_LR_ty_copy in LRv_A11 as LR_A11; eauto.

    eapply getLR_of_motive in LRv_B12 as temp; eauto.
    destruct temp as (eB & eB_eq & LR_B11 & LR_B12 & LR_B11').

    exists ϵA. exists eB. 
    split. eauto.
    split. eauto.
    unshelve eapply prefundamental_pi; eauto.
    - eauto using subst, LR_subst_escape.
    - eapply subst; eauto. eapply lift_subst; 
        eauto using validity_conv_left, validity_ty_ctx, LR_subst_escape.
    - intros. ssimpl. eauto.
Qed.

Lemma fundamental_pi B1 B2 {Γ i k A1 A2} : 
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊨< Ax (Ru i (ty k)) > Pi i (ty k) A1 B1 ≡ Pi i (ty k) A2 B2 : Sort (Ru i (ty k)).
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12.
    unfold LRv. intros σ1 σ2 ϵσ12.
    eapply fundamental_common_pi in ϵσ12 as temp; eauto.
    destruct temp as (ϵA & ϵB & _ & _ & LR_pi).
    eapply helper_LR.  eauto.
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

    eapply fundamental_common_pi in ϵσ12 as temp. 
    3:eapply LRv_A11. 4:eapply LRv_B11. 2,3: eauto using validity_conv_left, refl_ty.
    destruct temp as (ϵA & ϵB & LR_A & LR_B & LR_pi).
    eexists. split. eauto. split.
    - eapply conv_lam; eauto 7 using subst, subst, LR_subst_escape, lift_subst, validity_conv_left, validity_ty_ctx.
    - intros. 
      assert (⊩s (s1 .: σ1) ≡ (s2 .: σ2) : (Γ ,, (i, A1))) as ϵsσ by eauto using LR_subst, LR_iff_rel.
      eapply LRv_to_LR_tm in ϵsσ as ϵt'; eauto.
      eapply LR_irred_tm; eauto.
        (* from this point on, it's just technical manipulations to show that the beta redex reduces *)
      + eapply redd_step; eauto using redd_refl.
        eapply red_conv. eapply red_beta'; fold subst_term; eauto ; ssimpl.
        all:eauto 9 using refl_ty, subst, LR_subst_escape, 
            validity_subst_conv_left, validity_conv_left, lift_subst, validity_ty_ctx, LR_escape_tm.
        ssimpl. eauto 6 using LR_subst_escape, validity_subst_conv_left, validity_conv_left, refl_ty, subst.
        ssimpl. eapply redd_refl. eauto 6 using LR_subst_escape, validity_subst_conv_left, validity_conv_left, refl_ty, subst.
        
      + eapply redd_step; eauto using redd_refl.
        eapply red_conv. eapply red_beta; fold subst_term; ssimpl. 
        all:eauto 10 using refl_ty, subst, subst, LR_subst_escape, LR_sym, lift_subst, validity_ty_ctx,
            validity_subst_conv_right, validity_conv_right, validity_subst_conv_left, validity_conv_left, LR_escape_tm, refl_subst.
        
        ssimpl. eauto 6 using subst, refl_ty, validity_conv_left, subst_conv_sym, LR_subst_escape.
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
    
    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 
        by eauto using LRv_sym, LRv_trans.
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11
        by eauto using LRv_sym, LRv_trans.

    eapply fundamental_common_pi in LRv_B11 as temp. 3:exact LRv_A11. 2-4: eauto using validity_conv_left, refl_ty.
    destruct temp as (ϵA & ϵB & LR_A11 & LR_B11 & LR_pi).

    assert (Γ ⊨< i > u1 ≡ u1 : A1) as LRv_u11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_tm in LRv_u11 as ϵu11; eauto.
    eapply LRv_to_LR_tm in LRv_u12 as ϵu12; eauto.

    eexists. split. asimpl_unsafe. unshelve eapply LR_B11; eauto.

    eapply LRv_t12 in ϵσ as temp. destruct temp as (ϵpi' & LR_pi' & ϵt).
          eassert (ϵpi' <~> ϵPi _ _ _ _ _ _ _ _) by eauto using LR_irrel.
    rewrite H in ϵt. destruct ϵt. ssimpl.
    assert (ϵB (u1 <[ σ1]) (u1 <[ σ2]) <~> ϵB (u1 <[ σ1]) (u2 <[ σ2])) 
        as Hiff by eauto using LR_irrel.
    rewrite Hiff. eapply LR_erasure; eauto.
    (* from this point on, it's just technical manipulations to show that the terms are equal up to annotation conversion *)
    eapply aconv_refl. eapply type_app'; ssimpl;
            eauto 8 using LR_subst_escape, validity_conv_left, 
                validity_subst_conv_left, subst, refl_ty.
        
    ssimpl. eapply aconv_conv.        


    eapply aconv_app; eauto 8 using refl_ty, subst, LR_subst_escape, validity_conv_right, validity_ty_ctx,
        validity_subst_conv_right, type_conv, lift_subst, conv_ty_in_ctx_conv, refl_subst, lift_subst.

    eapply aconv_refl. eapply type_conv; eauto using LR_subst_escape, validity_conv_right, validity_subst_conv_right, subst.
    eapply conv_pi; eauto 9 using LR_subst_escape, subst, lift_subst, validity_conv_left, validity_ty_ctx, refl_ty.

    ssimpl. eapply subst; eauto using validity_conv_left, refl_ty. 
    econstructor; ssimpl. eauto using subst_conv_sym, LR_subst_escape. 
    eauto using subst, subst_conv_sym, LR_subst_escape, LR_escape, conv_sym.
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
    eauto using LR_escape_tm, validity_conv_left, redd_refl.
    eapply LR_escape_tm in ϵbeta; eauto.
    eapply validity_conv_right in ϵbeta.
    eapply type_inv_app' in ϵbeta as (_ & A_Wt & B_Wt & lam_Wt & u_Wt & _ & typeconv). fold subst_term in *.
    eapply type_inv_lam' in lam_Wt as (_ & _ & _ & t_Wt & _).
    eapply red_to_redd. ssimpl. asimpl in typeconv. eapply red_conv.
    2:eapply conv_sym;eauto.
    eapply red_beta'; eauto using refl_ty; ssimpl; reflexivity.
Qed.



Lemma fundamental_eta Γ i n A B t u :
    Γ ⊢< Ax i > A : Sort i ->
    Γ ⊨< Ax i > A ≡ A : Sort i ->
    Γ,, (i, A) ⊢< Ax (ty n) > B : Sort (ty n) ->
    Γ,, (i, A) ⊨< Ax (ty n) > B ≡ B : Sort (ty n) ->
    Γ ⊢< Ru i (ty n) > t : Pi i (ty n) A B ->
    Γ ⊨< Ru i (ty n) > t ≡ t : Pi i (ty n) A B ->
    Γ ⊢< Ru i (ty n) > u : Pi i (ty n) A B ->
    Γ ⊨< Ru i (ty n) > u ≡ u : Pi i (ty n) A B ->
    let t_app_x := app i (ty n) (S ⋅ A) (up_ren S ⋅ B) (S ⋅ t) (var 0) in
    let u_app_x := app i (ty n) (S ⋅ A) (up_ren S ⋅ B) (S ⋅ u) (var 0) in
    Γ,, (i, A) ⊢< ty n > t_app_x ≡ u_app_x : B ->
    Γ,, (i, A) ⊨< ty n > t_app_x ≡ u_app_x : B ->
    Γ ⊢< Ru i (ty n) > t ≡ u : Pi i (ty n) A B ->
    Γ ⊨< Ru i (ty n) > t ≡ u : Pi i (ty n) A B.
Proof.
    intros AWt LRv_A BWt LRv_B tWt LRv_t uWt LRv_u tx ux tx_conv_ux LRv_tx_ux t_conv_u.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply fundamental_common_pi in ϵσ as temp; eauto using refl_ty.
    destruct temp as (ϵA & ϵB & LR_A & LR_B & LR_pi).
    eexists. split;eauto.
    unfold ϵPi. split. 
    - eapply subst; eauto using LR_subst_escape.
    - intros. 
      assert (⊩s (s1 .: σ1) ≡ (s2 .: σ2) : (Γ ,, (i, A))) as ϵsσ by eauto using LR_subst.
      eapply LRv_to_LR_tm in LRv_tx_ux as ϵtx_ux; eauto.
      unfold tx, ux in ϵtx_ux. asimpl in ϵtx_ux.
      eapply ϵtx_ux.
Qed.


Lemma ϵzero' : ϵNat zero zero.
Proof.
    eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
Qed.

Lemma ϵsucc' {t u} : ϵNat t u -> ϵNat (succ t) (succ u).
Proof.
    intros. eapply ϵsucc; eauto 7 using val_redd_to_whnf, typing, ctx_typing, ϵNat_escape, validity_conv_left, validity_conv_right.
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
    intros. unfold LRv. intros.
    eexists. split. eauto using prefundamental_nat.
    eapply LRv_to_LR_tm in H0; eauto using prefundamental_nat, ϵsucc'.
Qed.

Lemma fundamental_conv Γ l A B t1 t2 :
    Γ ⊢< l > t1 ≡ t2 : A ->
    Γ ⊨< l > t1 ≡ t2 : A ->
    Γ ⊢< Ax l > A ≡ B : Sort l ->
    Γ ⊨< Ax l > A ≡ B : Sort l ->
    Γ ⊨< l > t1 ≡ t2 : B.
Proof.
    intros t1_conv_t2 LRv_t12 A_conv_B LRv_AB. unfold LRv. intros σ1 σ2 ϵσ12.
    assert (Γ ⊨< Ax l > B ≡ B : Sort l) as LRv_BB by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_AB as temp; eauto.
    destruct temp as (ϵAB & LR_AB).
    eapply LRv_to_LR_tm in LRv_t12 as LRv_t12; eauto.
    eapply LRv_to_LR_ty in LRv_BB as temp; eauto.
    destruct temp as (ϵBB & LR_BB).
    assert (ϵBB <~> ϵAB) as ϵBB_iff_ϵAB by eauto using LR_sym, LR_irrel.
    exists ϵBB. split; eauto.
    rewrite ϵBB_iff_ϵAB. eauto.
Qed.

Lemma nth_error_succ {X: Type} (x:X) l n a :
    nth_error (cons x l) (S n) = Some a -> 
    nth_error l n = Some a.
Proof.
    intros. unfold nth_error in H. simpl in H. eauto.
Qed.


    


Lemma prefundamental_rec k P1 p_zero1 p_succ1 P2 p_zero2 p_succ2 ϵP:
    ∙ ,, (ty 0, Nat) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ∙  ⊢< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    (∙ ,, (ty 0, Nat)),, (ty k, P1) ⊢< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (forall n1 n2 (ϵn : ϵNat n1 n2), 
        LR (ty k) (P1 <[ n1..]) (P2 <[ n2..]) (ϵP n1 n2)) -> 
    ϵP zero zero p_zero1 p_zero2 -> 
    (forall n1 n2 (ϵn : ϵNat n1 n2) t1 t2,
        ϵP n1 n2 t1 t2 -> 
        ϵP (succ n1) (succ n2) (p_succ1 <[t1 .: n1 ..]) (p_succ2 <[t2 .: n2 ..])) -> 
    forall n1 n2 (ϵn : ϵNat n1 n2), ϵP n1 n2 (rec (ty k) P1 p_zero1 p_succ1 n1) (rec (ty k) P2 p_zero2 p_succ2 n2).
Proof.
    intros. generalize n1 n2 ϵn. clear n1 n2 ϵn. 
    apply ϵNat_ind; intros.
    - pose (LR' := H2 _ _ ϵzero'). 
      pose (LR'' := H2 _ _ (ϵzero _ _ H5 H6)).
      assert (ϵNat t1 zero) as ϵt1zero. eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
      pose (LR''' := H4 _ _ ϵt1zero).
      assert (ϵP zero zero <~> ϵP t1 zero) by eauto using LR_sym, LR_irrel.
      assert (ϵP t1 t2 <~> ϵP t1 zero) by eauto using LR_sym, LR_irrel.
      rewrite H8. rewrite <- H7. 
      destruct H5, H6.
      eapply LR_irred_tm; eauto.
      eapply redd_rec_zero; eauto using validity_conv_left.
      eapply redd_conv. eapply redd_rec_zero; 
      eauto 8 using validity_conv_right, subst, aux_subst, type_zero, conv_sym, type_conv, ctx_typing, aux_subst_2, conv_ty_in_ctx_conv, refl_subst, refl_ty.
      eapply subst; eauto using conv_sym, aux_subst, LR_escape_tm, prefundamental_nat, ϵzero'.

    - pose (LR' := H2 _ _ (ϵsucc' H7)).
      pose (LR'' := H2 _ _ (ϵsucc _ _ _ _ H5 H6 H7)).
      assert (ϵNat t1 (succ t2')) as ϵt1succt2'. eapply ϵsucc; eauto using val_redd_to_whnf, typing, redd_whnf_to_conv, validity_conv_right.
      pose (LR''' := H2 _ _ ϵt1succt2').
      assert (ϵP (succ t1') (succ t2') <~> ϵP t1 (succ t2')) by eauto using LR_sym, LR_irrel.
      assert (ϵP t1 t2 <~> ϵP t1 (succ t2')) by eauto using LR_sym, LR_irrel.
      rewrite H10. rewrite <- H9.
      destruct H5, H6.
      eapply LR_irred_tm; eauto.
      eapply redd_rec_succ; eauto using validity_conv_left.
      eapply redd_conv.
      eapply redd_rec_succ; eauto 8 using validity_conv_right, subst, aux_subst, type_zero, conv_sym, type_conv, ctx_typing, aux_subst_2, conv_ty_in_ctx_conv, refl_subst, refl_ty.
      eapply subst; eauto using conv_sym, aux_subst, ϵsucc', prefundamental_nat, LR_escape_tm.
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

    assert (Γ ⊨< ty 0 > t1 ≡ t1 : Nat) as LRv_t11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_tm in LRv_t12 as ϵt12; eauto using prefundamental_nat.
    eapply LRv_to_LR_tm in LRv_t11 as ϵt11; eauto using prefundamental_nat.

    eapply getLR_of_motive in ϵσ12 as temp; eauto. 2: simpl;eauto using prefundamental_nat.  
    destruct temp as (eP & eP_eq & LR_P11 & LR_P12 & LR_P11').
    
    exists (eP (t1 <[ σ1]) (t2 <[ σ2])). 
    (* exists eP. *)
    split; asimpl. eauto.

    eapply prefundamental_rec; eauto.
    - eapply subst; eauto using lift_subst, LR_subst_escape, validity_ty_ctx, validity_conv_left.
    - eapply subst; eauto using LR_subst_escape. ssimpl. reflexivity.
    - eapply subst; eauto using lift_subst2, LR_subst_escape, validity_ty_ctx, validity_conv_left. substify. ssimpl. reflexivity.
    - intros. ssimpl. eapply LR_P12. eauto.
    - pose (LR_Pzero := LR_P11 _ _ ϵzero'). eapply LRv_to_LR_tm in LRv_pzero12 as LR_pzero; eauto. asimpl_unsafe. eauto.
    - intros. ssimpl. 
      pose (LR_Psucc := LR_P11 _ _ ϵn).
      assert (⊩s (t0 .: (n1 .: σ1)) ≡ (t3 .: (n2 .: σ2)) : (Γ ,, (ty 0, Nat)),, (ty k, P1)) 
        as ϵtnσ by eauto using LR_subst, prefundamental_nat.
      eapply LRv_to_LR_tm in LRv_psucc12; eauto. simpl. asimpl_unsafe. eauto using ϵsucc'.
Qed.


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
    eauto using LR_escape_tm, validity_conv_left, redd_refl.
    eapply LR_escape_tm in ϵpzero; eauto. eapply validity_conv_right in ϵpzero.
    asimpl in ϵpzero. eapply type_inv_rec' in ϵpzero as (_ & PWt & pzeroWt & psuccWt & _ & _ & typeconv).
    eapply red_to_redd.
    eapply red_conv. 2:eapply conv_sym; eauto.
    eapply red_rec_zero; eauto using refl_ty.
Qed.

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
    eauto using LR_escape_tm, validity_conv_left, redd_refl.
    eapply LR_escape_tm in ϵst;eauto.
    eapply validity_conv_right in ϵst. asimpl in ϵst.
    eapply type_inv_rec' in ϵst as (_ & PWt & pzeroWt & psuccWt & tWt & _ & typeconv).
    eapply red_to_redd. eapply red_conv. 2:eapply conv_sym;eauto.
    eapply type_inv_succ in tWt.
    assert (p_succ <[rec (ty k) (P <[ var 0 .: σ2 >> ren_term ↑]) (p_zero <[ σ2])(p_succ <[ var 0 .: ((↑ 0)__term .: σ2 >> ren_term (↑ >> ↑))]) (t <[ σ2])
.: (t <[ σ2] .: σ2)] = p_succ <[ var 0 .: ((↑ 0)__term .: σ2 >> ren_term (↑ >> ↑))] <[(rec (ty k) (P <[ var 0 .: σ2 >> ren_term ↑]) (p_zero <[ σ2])
(p_succ <[ var 0 .: ((↑ 0)__term .: σ2 >> ren_term (↑ >> ↑))])
(t <[ σ2])).: t<[σ2]..]). ssimpl. reflexivity.
rewrite H. eapply red_rec_succ; eauto using refl_ty.
Qed.

Lemma aux_subst_3 Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  Γ ⊢s t .. ≡ u .. : (Γ ,, (l, A)).
Proof.
  intros.
  econstructor; ssimpl; eauto using refl_subst, subst_id, validity_ty_ctx, validity_conv_left.
Qed.

Lemma aux_subst_4 Γ l l' t t' u u' A B :
  Γ ⊢< l > t ≡ u : A ->
  Γ ⊢< l' > t' ≡ u' : B ->
  Γ ⊢s (t' .: t ..) ≡ (u' .: u ..) : (Γ ,, (l, A) ,, (l', S ⋅ B)).
Proof.
  intros.
  econstructor; ssimpl; eauto.
  econstructor; ssimpl; eauto using subst_id, refl_subst, validity_conv_left, validity_ty_ctx.
Qed.


Lemma subst_id_reduce1 : pointwise_relation _ eq (var 0 .: (S >> var)) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a; reflexivity.
Qed.

Lemma subst_id_reduce2 : pointwise_relation _ eq (var 0 .: (var 1 .: (S >> (S >> var)))) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a. reflexivity. destruct a. reflexivity. reflexivity.
Qed.

Definition meta R t u := ∃ p, ∙ ⊢< prop > p : R <[u .: t ..].

Axiom ob_to_meta : forall t i A R a, ∙ ⊢< prop > t : acc i A R a -> Acc (meta R) a.

(* Lemma wk1_conv Γ i l t u B B' A σ: 
    Γ ⊢< l > t ≡ u : B -> 
    t <[σ] = S ⋅ t -> 
    u <[σ] = S ⋅ u -> 
    B' = S ⋅ B -> 
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢< l > t <[σ] ≡ u <[σ] : B'.
Proof.
    intros. rewrite H0, H1. subst.
    substify. eapply subst. admit. eauto.
Admitted.

Lemma wk1_type Γ i l t B B' A σ: 
    Γ ⊢< l > t : B -> 
    t <[σ] = S ⋅ t -> 
    B' = S ⋅ B -> 
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢< l > t <[σ] : B'.
Proof.
    intros. eapply validity_conv_left. eauto using wk1_conv, refl_ty.
Qed. *)

Lemma wk1_conv Γ i l t t' u u' B B' A : 
    Γ ⊢< l > t ≡ u : B -> 
    t' = S ⋅ t -> 
    u' = S ⋅ u -> 
    B' = S ⋅ B -> 
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢< l > t' ≡ u' : B'.
Proof.
    intros. subst.
    substify. eapply subst. admit. eauto.
Admitted.

Lemma wk1_type Γ i l t t' B B' A : 
    Γ ⊢< l > t : B -> 
    t' = S ⋅ t -> 
    B' = S ⋅ B -> 
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢< l > t' : B'.
Proof.
    intros. eapply validity_conv_left. eauto using wk1_conv, refl_ty.
Qed.

Lemma aaux A' R' P' Γ i k A R a q P p r b X Y l: 
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop -> 
    Γ ,, (i, A) ⊢< Ax l > P ≡ P' : Sort l ->
    Γ ,, (i, A) ⊢< Ax (ty k) > P : Sort (ty k) ->
    let R_ := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P_ := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
    Γ ⊢< i > a : A ->
    Γ ⊢< i > b : A ->
    Γ ⊢< prop > q : acc i A R a -> 
    Γ ⊢< prop > r : R <[a .: b ..] ->
    let Awk := (S >> S) ⋅ A in 
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in 
    let Pwk := (up_ren (S >> S)) ⋅ P in 
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv i Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel i (ty k) Awk Rwk Pwk pwk (var 1) t0 in 
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in 
    let t3 := lam prop (ty k) t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i (ty k) A t4 t3 in
    let t2' := R'<[S ⋅ a .: (var 0 .: S >> var)] in 
    let t4' := Pi prop l t2' (P' <[var 1.: (S >> (S >> var))]) in
    let t6 := app i (ty k) A' t4' t5 b in 
    let t7 := app prop (ty k) (R'<[a .: b ..]) (S ⋅ (P' <[ b ..])) t6 r in 
    X = t7 ->
    Y = P <[b..] ->
    l = ty k ->
    Γ ⊢< l > X -->> accel i (ty k) A R P p b (accinv i A R a q b r) : Y.
Proof.
    intros. subst.
    eapply redd_conv.
    eapply redd_step.

    eapply red_app'; eauto 7 using conv_sym, aux_subst_4, refl_ty, subst, type_conv.
    3:ssimpl; eauto using subst, aux_subst_3, refl_ty, conv_sym.
    eapply red_beta'; eauto using conv_sym, type_conv.
    3:unfold t4', t2';ssimpl; reflexivity.
    1-2:admit.
    eapply red_to_redd.
    unfold t3, t2, P''; ssimpl. eapply red_beta' ; ssimpl ; eauto 7 using conv_sym, aux_subst_4, refl_ty, subst, type_conv.
    3:{ unfold t1, t0, Awk, Rwk, Pwk, pwk. ssimpl. 
        rewrite accinv_subst. ssimpl. setoid_rewrite subst_id_reduce2. 
        setoid_rewrite subst_id_reduce1. ssimpl. reflexivity. }
    eapply wk1_conv; eauto using conv_sym, subst, aux_subst_3, refl_ty; ssimpl; eauto.
    eauto  7 using conv_sym, aux_subst_4, refl_ty, subst, type_conv, validity_conv_right.
    admit.
Admitted.


Lemma conv_ty_in_ctx_conv2 Γ l A A' l' t u B : 
  Γ ,, (l , A) ,, (l, S ⋅ A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A') ,, (l, S ⋅ A') ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  econstructor. econstructor. eauto using validity_conv_left, validity_ty_ctx, refl_ctx.
  eauto. eapply wk1_conv; eauto using validity_conv_left.
Qed.



Lemma conv_ty_in_ctx_conv2' Γ l1 l2 l3 A A' t u B B' C : 
  Γ ,, (l1 , A) ,, (l2, B) ⊢< l3 > t ≡ u : C ->
  Γ ⊢< Ax l1 > A ≡ A' : Sort l1 -> 
  Γ ,, (l1 , A) ⊢< Ax l2 > B ≡ B' : Sort l2 -> 
  Γ ,, (l1 , A') ,, (l2, B') ⊢< l3 > t ≡ u : C.
Proof.
  intros t_eq_u A_eq_A' B_eq_B'.
  eapply conv_in_ctx_conv; eauto.
  econstructor; eauto. econstructor; eauto. 
  eauto using validity_conv_left, validity_ty_ctx, refl_ctx.
Qed.

Lemma fundamental_accel_aux2 i k C1' C2' A1 A2 R1 R2 P1 P2 a1 a2 l :
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i -> 
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    let R1' := R1 <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P1' := P1 <[var 1 .: (S >> S >> S >> var)] in
    let C1 := Pi prop (ty k) R1' P1' in 
    let B1 := Pi i (ty k) (S ⋅ A1) C1 in
    let R2' := R2 <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P2' := P2 <[var 1 .: (S >> S >> S >> var)] in
    let C2 := Pi prop (ty k) R2' P2' in 
    let B2 := Pi i (ty k) (S ⋅ A2) C2 in
    ∙ ⊢< i > a1 ≡ a2 : A1 -> 
    C1' = C1 <[ up_term_term a1..] -> 
    C2' = C2 <[ up_term_term a2..] ->
    l = Ax (ty k) ->
    ∙,, (i, A1) ⊢< l > C1' ≡ C2' : Sort (ty k).
Proof.
    intros. subst.
    assert (∙,, (i, A1) ⊢< Ax prop > 
        R1 <[ ↑ ⋅ a1 .: (var 0 .: ↑ >> var)]
      ≡ R2 <[ ↑ ⋅ a2 .: (var 0 .: ↑ >> var)] : Sort prop).
    { eapply subst; eauto. econstructor. econstructor. econstructor.
      ssimpl. eapply conv_var'; eauto using validity_conv_left, validity_ty_ctx. reflexivity. substify. reflexivity. ssimpl.  eapply conv_ren; eauto. 2:substify; eauto. unfold rtyping; intros. destruct x; dependent destruction H3. }
    unfold C1, C2, R1', R2', P1', P2'.
    ssimpl. eapply conv_pi'; eauto.
    eapply subst; eauto. econstructor. econstructor. ssimpl.
    eapply conv_var'.
    reflexivity. econstructor; eauto using validity_conv_left, validity_ty_ctx.
    substify. reflexivity.
Qed.



Lemma prefundamental_accel A3 R3 P3 i k A1 A2 ϵA R1 R2 a1 a2 q1 q2 P1 P2 ϵP p1 p2 :
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i -> 
    ∙ ⊢< Ax i > A1 ≡ A3 : Sort i ->
    LR i A1 A2 ϵA ->
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R3 : Sort prop ->    
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P3 : Sort (ty k) ->
    (forall a1 a2 (ϵa : ϵA a1 a2), LR (ty k) (P1<[a1..]) (P2<[a2..]) (ϵP a1 a2)) ->
    let ϵB a1 a2 f1 f2 := forall b1 b2 (ϵb : ϵA b1 b2) r1 r2 (r_Wt : ∙ ⊢< prop > r1 ≡ r2 : R1 <[a1 .:b1 ..]) t1 t2,
        t1 = app prop (ty k) (R1<[a1 .: b1 ..]) (S ⋅ (P1 <[b1..])) 
                (app i (ty k) A1 (Pi prop (ty k) (R1<[(S ⋅ a1) .: (var 0 .: (S >> var))]) (P1 <[var 1 .: (S >> S >> var)])) f1 b1) 
            r1 ->
        t2 = app prop (ty k) (R3<[a2 .: b2 ..]) (S ⋅ (P3 <[b2..])) 
                (app i (ty k) A3 (Pi prop (ty k) (R3<[(S ⋅ a2) .: (var 0 .: (S >> var))]) (P3 <[var 1 .: (S >> S >> var)])) f2 b2) 
            r2 ->
            ϵP b1 b2 t1 t2 in
    let R' := R1 <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P1 <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i (ty k) (S ⋅ A1) (Pi prop (ty k) R' P') in
    (forall a1 a2 (ϵa : ϵA a1 a2) f1 f2 (ϵf : ϵB a1 a2 f1 f2), 
        ∙ ⊢< Ru i (ty k)> f1 ≡ f2 : B <[a1..] ->
        ϵP a1 a2 (p1 <[f1.: a1 ..]) (p2<[f2 .: a2 ..])) ->
    (∙ ,, (i, A1)),, (Ru i (ty k), B) ⊢< ty k > p1 ≡ p2 : P1 <[var 1.: (S >> (S >> var))] ->
    ∙ ⊢< i > a1 ≡ a2 : A1 ->
    forall (ϵa : ϵA a1 a2),
    ∙ ⊢< prop > q1 ≡ q2 : acc i A1 R1 a1 -> 
    ϵP a1 a2 (accel i (ty k) A1 R1 P1 p1 a1 q1) (accel i (ty k) A2 R2 P2 p2 a2 q2).
Proof.
    intros. 
    assert (Acc (meta R1) a1) by eauto using validity_conv_left, ob_to_meta.

    generalize q1 q2 a2 ϵa H9 H10. clear q1 q2 a2 ϵa H9 H10. 
    induction H11. rename x into a1. intros.

    assert (∙ ⊢< ty k> accel i (ty k) A2 R2 P2 p2 a2 q2 : P1 <[ a1..]) as temp
        by eauto using conv_accel, validity_conv_right.
    eapply type_inv_accel' in temp as (_ & _ & R2Wt & _ & p2Wt & _).

    eapply LR_irred_tm; eauto. 3:eapply H7; eauto. all:clear H7.
    - eauto 6 using red_to_redd, red_accel', validity_conv_left.
    - eapply red_to_redd; eapply red_conv; eauto 7 using red_accel', validity_conv_right, conv_ty_in_ctx_ty, conv_sym, type_conv, conv_acc, subst, conv_sym, aux_subst.
    - unfold ϵB. all:clear ϵB. intros; subst.
      eapply LR_irred_tm; eauto.
      1,2:shelve.
      unshelve eapply H10; clear H10.
      eapply (accinv i A1 R1 a1 q1 b1 r1). 
      eapply (accinv i A2 R2 a2 q2 b2 r2).
      unfold meta; eexists; eauto using validity_conv_right.
      eauto.
      eauto using LR_escape_tm.
      { eapply conv_irrel.
        - eauto 8 using type_accinv', LR_escape_tm, validity_conv_left.
        - eapply type_conv. eapply type_accinv'; eauto 8 using type_conv, conv_acc, conv_sym, validity_conv_right, LR_escape_tm, aux_subst_4, subst.
        eauto using conv_acc, conv_sym, conv_ty_in_ctx_conv, conv_ty_in_ctx_conv2, LR_escape_tm. }
      Unshelve.
      + ssimpl. eapply (aaux A1 R1 P1); eauto using validity_conv_left, LR_escape_tm, refl_ty. substify. ssimpl. reflexivity.

      + ssimpl. eapply redd_conv.
        eapply (aaux A3 R3 P3); eauto 6 using validity_subst_conv_left, validity_conv_right, conv_sym, conv_trans, refl_ty, LR_escape_tm, conv_ty_in_ctx_conv, conv_ty_in_ctx_conv2, type_conv, conv_acc, aux_subst_4, subst.
        substify; ssimpl; reflexivity.
        eauto using aux_subst_3, subst, conv_sym, LR_escape_tm.
    -  clear ϵB H10 p2Wt. 
    eapply conv_lam'; eauto.
    + clear H3 H5. eapply fundamental_accel_aux2; eauto. 1,2:ssimpl;reflexivity.
    + eapply conv_lam'; eauto. 
      1,2:admit.
      admit.
    + unfold B, R', P'. simpl. f_equal. ssimpl. reflexivity. f_equal. ssimpl. reflexivity. ssimpl. reflexivity.
Admitted.



Lemma fundamental_accel_aux1 i k C1' C2' A1 A2 R1 R2 P1 P2 f1 f2 s1 s2 a1 a2 T l :
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i -> 
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    let R1' := R1 <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P1' := P1 <[var 1 .: (S >> S >> S >> var)] in
    let C1 := Pi prop (ty k) R1' P1' in 
    let B1 := Pi i (ty k) (S ⋅ A1) C1 in
    let R2' := R2 <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P2' := P2 <[var 1 .: (S >> S >> S >> var)] in
    let C2 := Pi prop (ty k) R2' P2' in 
    let B2 := Pi i (ty k) (S ⋅ A2) C2 in
    ∙ ⊢< Ru i (ty k) > f1 ≡ f2 : B1 <[a1..] -> 
    ∙ ⊢< i > s1 ≡ s2 : A1 -> 
    ∙ ⊢< i > a1 ≡ a2 : A1 -> 
    T = C1 <[s1 .: a1 ..] ->
    (* T = Pi prop (ty k) (R1 <[ a0 .: (s1 .: σ1)])  *)
        (* (P1 <[ ↑ ⋅ s1 .: σ1 >> subst_term (↑ >> var)]) -> *)
    C1' = C1 <[up_term_term (a1 ..)] ->
    C2' = C2 <[up_term_term (a2 ..)] ->
    l = Ru prop (ty k) ->
    ∙ ⊢< l > app i (ty k) A1 C1' f1 s1 
        ≡ app i (ty k) A2 C2' f2 s2 : T.
Proof.
    intros. subst.
    eapply conv_app'; eauto.
    2: unfold B1, C1, R1', P1' in *; asimpl in H2; eauto.
    2:ssimpl; reflexivity.
    eauto using fundamental_accel_aux2.
Qed.


Lemma fundamental_accel Γ i k A1 A2 R1 R2 a1 a2 q1 q2 P1 P2 p1 p2 :
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    (Γ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    (Γ,, (i, A1)),, (i, S ⋅ A1) ⊨< Ax prop > R1 ≡ R2 : Sort prop ->
    Γ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    let R' := R1 <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P1 <[var 1 .: (S >> S >> S >> var)] in
    let C := Pi prop (ty k) R' P' in
    let B := Pi i (ty k) (S ⋅ A1) C in
    let P'' := P1 <[var 1.: (S >> (S >> var))] in
    (Γ,, (i, A1)),, (Ru i (ty k), B) ⊢< ty k > p1 ≡ p2 : P'' ->
    (Γ,, (i, A1)),, (Ru i (ty k), B) ⊨< ty k > p1 ≡ p2 : P'' ->
    Γ ⊢< i > a1 ≡ a2 : A1 ->
    Γ ⊨< i > a1 ≡ a2 : A1 ->
    Γ ⊢< prop > q1 ≡ q2 : acc i A1 R1 a1 ->
    Γ ⊨< prop > q1 ≡ q2 : acc i A1 R1 a1 ->
    Γ ⊨< ty k > accel i (ty k) A1 R1 P1 p1 a1 q1 ≡ accel i (ty k) A2 R2 P2 p2 a2 q2 : P1 <[ a1..].
Proof.
    intros A1_conv_A1 LRv_A12 R1_conv_R2 LRv_R12 P1_conv_P2 LRv_P12 R' P' C B P'' p1_conv_p2 LRv_p12 a1_conv_a2 LRv_a12 q1_conv_q2 LRv_q12.
    unfold LRv. intros σ1 σ2 ϵσ12.

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_A11 as temp; eauto. destruct temp as (ϵA & LR_A11).
    eapply LRv_to_LR_ty_copy in LRv_A12 as LR_A12; eauto.

    assert (Γ ⊨< i > a1 ≡ a1 : A1) as LRv_a11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_tm in LRv_a11 as ϵa11; eauto.
    eapply LRv_to_LR_tm in LRv_a12 as ϵa12; eauto.

    eapply getLR_of_motive in ϵσ12 as temp; eauto. 
    destruct temp as (eP & eP_eq & LR_P11 & LR_P12 & LR_P11').
    clear LRv_P12 LRv_a12 LRv_a11 LRv_A11 LRv_A12 LRv_R12 LRv_P12 LRv_q12.

    assert ((∙,, (i, A1 <[ σ1])),, (i, S ⋅ A1 <[ σ1]) 
        ⊢< Ax prop > R1 <[ var 0 .: (var 1 .: σ1 >> ren_term (↑ >> ↑))] 
                ≡    R1 <[ var 0 .: (var 1 .: σ2 >> ren_term (↑ >> ↑))] : Sort prop)
        as R1σ_conv_R2σ.
    { eapply validity_conv_left, refl_ty in R1_conv_R2. eapply subst; eauto using refl_ty. eapply lift_subst2; eauto using validity_conv_left, validity_ty_ctx, LR_subst_escape. ssimpl. reflexivity. }

    assert (∙,, (i, A1 <[ σ1]) ⊢< Ax (ty k) > 
        P1 <[ var 0 .: σ1 >> ren_term ↑] ≡ 
        P1 <[ var 0 .: σ2 >> ren_term ↑] : Sort (ty k)) as P1σ_conv_P2σ
    by eauto 8 using validity_conv_left, refl_ty, subst, lift_subst, validity_ty_ctx, LR_subst_escape.
    

    
    exists (eP (a1 <[ σ1]) (a2 <[ σ2])). 
    split; ssimpl. eauto.
    eapply (prefundamental_accel (A1 <[σ2]) (R1 <[ var 0 .: (var 1 .: σ2 >> ren_term (↑ >> ↑))]) (P1 <[ var 0 .: σ2 >> ren_term ↑])); 
    eauto 9 using subst, LR_subst_escape, validity_conv_left, refl_ty, lift_subst, aux_subst, validity_conv_left, validity_ty_ctx, lift_subst2.
    1:eapply subst; eauto using validity_conv_left, refl_ty; eapply lift_subst2; eauto using LR_subst_escape, validity_conv_left, validity_ty_ctx; ssimpl; reflexivity.
    intros; ssimpl; eauto.
    3:eapply subst; eauto using LR_subst_escape; ssimpl; reflexivity.
    2:{eapply subst; eauto. 2: unfold P''; ssimpl; substify; reflexivity. 
      eapply lift_subst2; eauto using LR_subst_escape, validity_conv_left, validity_ty_ctx.
      simpl. f_equal. ssimpl. reflexivity. f_equal. unfold R'. ssimpl. substify. eauto. unfold P'. ssimpl. substify. reflexivity. } 

    intros.


    pose (ϵC s1 s2 := 
        ϵPi prop (ty k) (R1 <[ a0 .: (s1 .: σ1)]) (R1 <[ a3 .: (s2 .: σ2)]) 
            (λ t0 u0, ∙ ⊢< prop > t0 ≡ u0 : R1 <[ a0 .: (s1 .: σ1)]) 
            (P1 <[ ↑ ⋅ s1 .: σ1 >> subst_term (↑ >> var)]) 
            (P1 <[ ↑ ⋅ s2 .: σ2 >> subst_term (↑ >> var)])
            (λ x x0, eP s1 s2)).

    pose (ϵB := ϵPi i (ty k) (A1 <[ σ1]) (A1 <[ σ2]) ϵA 
                    (C <[up_term_term (a0 .:σ1)]) (C <[up_term_term (a3 .:σ2)]) ϵC).

    assert (ϵB f1 f2).
    {
        unfold ϵB. unfold ϵPi.
        split. 
        - asimpl in H. unfold C, P', R'. asimpl. setoid_rewrite rinstInst'_term_pointwise.  eapply H. 
        - intros. unfold ϵC. unfold ϵPi. split.
          + eapply fundamental_accel_aux1; eauto using LR_escape_tm, LR_escape_ty.
            all: unfold C, R', P'; ssimpl; substify; reflexivity.
          + intros. ssimpl. eapply (ϵf s1 s2 ϵs s0 s3).
            ssimpl. eauto.
            all: unfold C, P', R'; ssimpl; substify; reflexivity. }

    clear ϵf H. (* removes clutter *)
    assert (LR (Ru i (ty k)) (B <[a0 .: σ1]) (B <[ a3 .: σ2]) ϵB).
    {
        unfold B. simpl. unshelve eapply LR_pi'. 
        exact ϵA. exact ϵC.
        - ssimpl; eapply fundamental_accel_aux2; 
          eauto using LR_escape_tm, LR_escape_ty; 
          unfold P', R'; ssimpl; substify; reflexivity.
        - ssimpl. eauto.
        - intros. ssimpl. 
          assert (∙ ⊢< Ax (ty k) > P1 <[ s1.: σ1] ≡ P1 <[ s2.: σ2 ] : Sort (ty k))
            by eauto 7 using subst, refl_ty, validity_conv_left, ConvSubst, LR_escape_tm, LR_subst_escape. 

          assert (∙ ⊢< Ax prop > R' <[ s1 .: (a0 .: σ1)] ≡ R' <[ s2 .: (a3 .: σ2)] : Sort prop).
          { unfold R'. ssimpl. eapply subst; eauto using validity_conv_left, refl_ty.
            econstructor. econstructor. eauto using LR_subst_escape. eauto using LR_escape_tm. ssimpl. eauto using LR_escape_tm. } 
          unshelve eapply LR_pi'. 
          exact (fun t u => ∙ ⊢< prop > t ≡ u : R1 <[ a0 .: (s1 .: σ1)]).
          intros; exact (eP s1 s2).
          + eapply wk1_conv. eapply H.
            1,2:unfold P'; ssimpl; substify; reflexivity.
            all : eauto using validity_conv_left.
          + eapply LR_prop; eauto.
            unfold R'; eauto using validity_conv_right. split; unfold R'; ssimpl; eauto.
          + intros. simpl. unfold P'. ssimpl. eauto.
          + unfold ϵC, ϵB, P', R', ϵPi. ssimpl. reflexivity.
          + reflexivity.
        - unfold ϵC, ϵB, C, P', R', ϵPi. ssimpl. reflexivity.
        - reflexivity. }

    assert (⊩s (f1 .: (a0 .: σ1)) ≡ (f2 .: (a3 .: σ2)) : (Γ,, (i, A1)),, (Ru i (ty k), B))
        by eauto using LR_subst.

    eapply LRv_to_LR_tm in LRv_p12 as ϵp; eauto.
    2:unfold P''; asimpl_unsafe; eauto.
    ssimpl. eapply ϵp.
Qed.

Lemma fundamental_accel_accin Γ i k A R a q P p :
    Γ ⊢< Ax i > A : Sort i ->
    Γ ⊨< Ax i > A ≡ A : Sort i ->
    (Γ,, (i, A)),, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    (Γ,, (i, A)),, (i, S ⋅ A) ⊨< Ax prop > R ≡ R : Sort prop ->
    Γ,, (i, A) ⊢< Ax (ty k) > P : Sort (ty k) ->
    Γ,, (i, A) ⊨< Ax (ty k) > P ≡ P : Sort (ty k) ->
    let R' := R <[ var 1 .: (var 0 .: (S >> S) >> var)] in
    let P' := P <[ var 1 .: ((S >> S) >> S) >> var] in
    let B := Pi i (ty k) (S ⋅ A) (Pi prop (ty k) R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    (Γ,, (i, A)),, (Ru i (ty k), B) ⊢< ty k > p : P'' ->
    (Γ,, (i, A)),, (Ru i (ty k), B) ⊨< ty k > p ≡ p : P'' ->
    Γ ⊢< i > a : A ->
    Γ ⊨< i > a ≡ a : A ->
    Γ ⊢< prop > q : acc i A R a ->
    Γ ⊨< prop > q ≡ q : acc i A R a ->
    let Awk := Init.Nat.add 2 ⋅ A in
    let Rwk := up_ren (up_ren (Init.Nat.add 2)) ⋅ R in
    let Pwk := up_ren (Init.Nat.add 2) ⋅ P in
    let pwk := up_ren (up_ren (Init.Nat.add 2)) ⋅ p in
    let t5 := accinv i Awk Rwk (Init.Nat.add 2 ⋅ a) (Init.Nat.add 2 ⋅ q) (var 1) (var 0) in
    let t6 := accel i (ty k) Awk Rwk Pwk pwk (var 1) t5 in
    let t7 := R <[ S ⋅ a .: (var 0 .: S >> var)] in
    let t8 := lam prop (ty k) t7 P'' t6 in
    let t9 := Pi prop (ty k) t7 P'' in
    let t10 := lam i (ty k) A t9 t8 in
    Γ ⊨< ty k > accel i (ty k) A R P p a q ≡ p <[ t10 .: a..] : P <[ a..].
Proof.
    intros. unfold LRv. intros σ1 σ2 ϵσ.
    eapply H8 in ϵσ as temp.
    destruct temp as (ϵA & LR_A & ϵa).
    assert (⊩s (a<[σ1] .: σ1) ≡ (a<[σ2] .: σ2) : Γ,, (i, A)).
    unshelve econstructor. exact ϵA. ssimpl. eauto. ssimpl. eauto. ssimpl. eauto. 
    eapply H4 in H11 as temp. rewrite <- helper_LR in temp.
    destruct temp as (ϵP & LR_P).

    eapply fundamental_accel in ϵσ as temp; eauto using refl_ty.
    destruct temp as (ϵP' & LR_P' & ϵaccel).
    asimpl in LR_P'.
    assert (ϵP <~> ϵP') by eauto using LR_irrel.
    rewrite <- H12 in ϵaccel.
    clear ϵP' LR_P' H12.

    (exists ϵP). split; ssimpl; eauto.
    eapply LR_redd_tm; eauto.
    - ssimpl. eapply redd_refl.
      eapply LR_escape_tm in ϵaccel; eauto.  asimpl in ϵaccel.
      eapply validity_conv_left. eauto. 
    - eapply LR_escape_tm in ϵaccel; eauto. eapply validity_conv_right in ϵaccel.
      simpl in ϵaccel.
      eapply type_inv_accel' in ϵaccel as (_ & AWt & RWt & PWt & pWt & aWt & qWt & l_eq & conv).  
      eapply redd_conv; eauto using conv_sym.
      eapply red_to_redd. simpl. eapply red_accel'; eauto.
      ssimpl. f_equal. unfold t10, t9, t8, t7, t6, t5, pwk, Pwk, Rwk, Awk, P''. ssimpl. f_equal. f_equal.
        f_equal. ssimpl. substify. reflexivity. substify. reflexivity. f_equal. ssimpl. substify. reflexivity.
        substify. reflexivity. f_equal. rewrite accinv_subst. f_equal; ssimpl; reflexivity.
Qed.

Lemma LR_to_red k A B R : LR (ty k) A B R -> exists A', ∙ ⊢< Ax (ty k) > A -->>! A' : Sort (ty k).
Proof.
    intro. assert (exists l, l = ty k /\ LR l A B R) by eauto.
    clear H. destruct H0 as (l & eq & lr).
    generalize l A B R lr k eq. clear l A B R lr k eq.
    refine (LR_ind _ _ _ _ _); intros; dependent destruction eq; eauto.
Qed.

Axiom nat_neq_sort : forall e, ∙ ⊢< prop > e : obseq (ty 1) (Sort (ty 0)) Nat (Sort prop) -> False.
Axiom nat_neq_pi  : forall i j A B e, ∙ ⊢< prop > e : obseq (ty 1) (Sort (ty 0)) Nat (Pi i j A B) -> False.
Axiom sort_neq_pi  : forall l i j A B e, ∙ ⊢< prop > e : obseq (Ax (Ax l)) (Sort (Ax l)) (Sort l) (Pi i j A B) -> False.

Lemma nat_neq_sort_red l l' A B e : 
    ∙ ⊢< Ax l' > A -->>! Nat : Sort l' ->
    ∙ ⊢< Ax l' > B -->>! Sort l : Sort l' ->
    ∙ ⊢< prop > e : obseq (Ax l') (Sort l') A B -> 
    False.
Proof.
    intros A_red_nat B_red_sort A_eq_B.
    eapply redd_whnf_to_conv in B_red_sort as temp.
    eapply validity_conv_right, type_inv_sort' in temp as (_ & eq & _).
    eapply Ax_inj in eq. subst.
    eapply redd_whnf_to_conv in A_red_nat as temp.
    eapply validity_conv_right, type_inv_nat' in temp as (_ & eq & _).
    destruct l. inversion eq. clear eq.
    eapply nat_neq_sort. eapply type_conv. eapply A_eq_B.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.

Lemma nat_neq_pi_red l' A B i j S T e : 
    ∙ ⊢< Ax l' > A -->>! Nat : Sort l' ->
    ∙ ⊢< Ax l' > B -->>! Pi i j S T : Sort l' ->
    ∙ ⊢< prop > e : obseq (Ax l') (Sort l') A B -> 
    False.
Proof.
    intros A_red_nat B_red_pi A_eq_B.
    eapply redd_whnf_to_conv in A_red_nat as temp.
    eapply validity_conv_right, type_inv_nat' in temp as (_ & eq' & _).
    destruct l'. 2:inversion eq'. dependent destruction eq'.
    eapply nat_neq_pi. eapply type_conv. eapply A_eq_B.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.


Lemma sort_neq_pi_red l l' A B i j S T e : 
    ∙ ⊢< Ax l' > A -->>! Sort l : Sort l' ->
    ∙ ⊢< Ax l' > B -->>! Pi i j S T : Sort l' ->
    ∙ ⊢< prop > e : obseq (Ax l') (Sort l') A B -> 
    False.
Proof.
    intros A_red_sort B_red_pi A_eq_B.
    eapply redd_whnf_to_conv in A_red_sort as temp.
    eapply validity_conv_right, type_inv_sort' in temp as (_ & eq & _).
    eapply Ax_inj in eq. subst.
    eapply sort_neq_pi. 
    eapply type_conv; eauto.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.




Axiom obseq_sym : level -> term -> term -> term -> term -> term.
Axiom type_obseq_sym : forall Γ l A a b e, 
    Γ ⊢< prop > e : obseq l A a b -> 
    Γ ⊢< prop > obseq_sym l A a b e : obseq l A b a.
    


Axiom pi_sort_inj : forall i j i' j' A A' B B' e,
    Ru i j = Ru i' j' ->
    ∙ ⊢< prop > e : obseq (Ax (Ru i j)) (Sort (Ru i j)) (Pi i j A B) (Pi i' j' A' B') -> 
    i = i' /\ j = j'.


Lemma pi_sort_inj_red l i j i' j' A A' B B' T T' e :
    ∙ ⊢< Ax l > T -->>! Pi i j A B : Sort l ->
    ∙ ⊢< Ax l > T' -->>! Pi i' j' A' B' : Sort l ->
    ∙ ⊢< prop > e : obseq (Ax l) (Sort l) T T' -> 
    i = i' /\ j = j'.
Proof.
    intros T_red T'_red eWt.
    eapply redd_whnf_to_conv in T_red as temp.
    eapply validity_conv_right, type_inv_pi' in temp as (_ & _ & _ & eq & _).
    eapply Ax_inj in eq. subst.
    eapply redd_whnf_to_conv in T'_red as temp.
    eapply validity_conv_right, type_inv_pi' in temp as (_ & _ & _ & eq & _).
    eapply Ax_inj in eq.
    eapply pi_sort_inj; eauto.
    eapply type_conv; eauto.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.

    
Lemma redd_cast1 Γ i A A' B e a :
    Γ ⊢< Ax i > A -->> A' : Sort i ->
    Γ ⊢< Ax i > B : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< i > cast i A B e a -->> cast i A' B e a : B.
Proof.
    intros A_redd_A' BWt eWt aWt. 
    dependent induction A_redd_A'.
    - eapply redd_refl; eauto using type_cast.
    - eapply redd_step. eapply red_cast1; eauto.
      eapply IHA_redd_A'; 
      eauto 7 using type_conv, red_to_conv, refl_ty, 
      conv_obseq, conv_sym, conv_sort, validity_ty_ctx.
Qed.

Lemma redd_cast2 Γ i A B B' e a :
    Γ ⊢< Ax i > A : Sort i ->
    val A ->
    Γ ⊢< Ax i > B -->> B' : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< i > cast i A B e a -->> cast i A B' e a : B.
Proof.
    intros AWt val_A B_redd_B' eWt aWt. 
    dependent induction B_redd_B'.
    - eapply redd_refl; eauto using type_cast.
    - eapply redd_step. eapply red_cast2; eauto.
      eapply redd_conv; eauto using red_to_conv, conv_sym.
      eapply IHB_redd_B'; 
      eauto 7 using type_conv, red_to_conv, refl_ty, 
      conv_obseq, conv_sym, conv_sort, validity_ty_ctx.
Qed.

Lemma redd_cast_nat_nat Γ A B e a:
    Γ ⊢< Ax (ty 0) > A -->> Nat : Sort (ty 0) ->
    Γ ⊢< Ax (ty 0) > B -->> Nat : Sort (ty 0) -> 
    Γ ⊢< prop > e : obseq (Ax (ty 0)) (Sort (ty 0)) A B ->
    Γ ⊢< ty 0 > a : A -> 
    Γ ⊢< ty 0 > cast (ty 0) A B e a -->> a : B.
Proof.
    intros A_red B_red eWt aWt.
    eapply redd_trans.
    eapply redd_cast1; 
    eauto using redd_to_conv, validity_conv_left.
    eapply redd_trans.
    eapply redd_cast2; 
    eauto 9 using type_conv, redd_to_conv, conv_obseq, validity_ty_ctx, 
    conv_sort, refl_ty, validity_conv_left, type_nat.
    eapply red_to_redd. eapply red_conv; eauto using redd_to_conv, conv_sym. 
    eapply red_cast_nat; 
    eauto 7 using type_conv, redd_to_conv, obseq_sym, 
    conv_sort', validity_ty_ctx, conv_obseq.
Qed.

Lemma redd_cast_sort_sort Γ l A B e a:
    Γ ⊢< Ax (Ax l) > A -->> Sort l : Sort (Ax l) ->
    Γ ⊢< Ax (Ax l) > B -->> Sort l : Sort (Ax l) -> 
    Γ ⊢< prop > e : obseq (Ax (Ax l)) (Sort (Ax l)) A B ->
    Γ ⊢< Ax l > a : A -> 
    Γ ⊢< Ax l > cast (Ax l) A B e a -->> a : B.
Proof.
    intros A_red B_red eWt aWt.
    eapply redd_trans.
    eapply redd_cast1; 
    eauto using redd_to_conv, validity_conv_left.
    eapply redd_trans.
    eapply redd_cast2; 
    eauto 9 using type_conv, redd_to_conv, conv_obseq, validity_ty_ctx, 
    conv_sort, refl_ty, validity_conv_left, type_nat.
    eapply red_to_redd. eapply red_conv; eauto using redd_to_conv, conv_sym. 
    eapply red_cast_sort; 
    eauto 7 using type_conv, redd_to_conv, obseq_sym, 
    conv_sort', validity_ty_ctx, conv_obseq.
Qed.


Opaque LR. 
Lemma prefundamental_cast l A1 A2 ϵA B1 B2 ϵB : 
    LR l A1 A2 ϵA -> 
    LR l B1 B2 ϵB ->
    (forall a1 a2 e1 e2, 
        ϵA a1 a2 -> 
        ∙ ⊢< l > a1 ≡ a2 : A1 -> 
        ∙ ⊢< prop > e1 ≡ e2 : obseq (Ax l) (Sort l) A1 B1 ->
        ϵB (cast l A1 B1 e1 a1) (cast l A2 B2 e2 a2)) /\ 
    (forall b1 b2 e1 e2, 
        ϵB b1 b2 -> 
        ∙ ⊢< l > b1 ≡ b2 : B1 -> 
        ∙ ⊢< prop > e1 ≡ e2 : obseq (Ax l) (Sort l) B1 A1 ->
        ϵA (cast l B1 A1 e1 b1) (cast l B2 A2 e2 b2)).
Proof.
    intros LR_A12 LR_B12. 
    pose proof (LR_A12' := LR_A12). pose proof (LR_B12' := LR_B12).
    generalize l A1 A2 ϵA LR_A12 LR_A12' B1 B2 ϵB LR_B12 LR_B12'.
    clear l A1 A2 ϵA LR_A12 LR_A12' B1 B2 ϵB LR_B12 LR_B12'.
    refine (LR_ind _ _ _ _ _); intros.
    - rewrite LR_prop_eq in LR_B12. destruct LR_B12.
      destruct p.
      split; intros; try rewrite H0 in *; try rewrite H2 in *; eapply conv_cast; eauto.
    - eapply LR_to_red in LR_B12 as temp. destruct temp as (B1' & B1_red).
      unshelve eapply LR_inv in LR_B12 ; eauto.
      simpl in LR_B12. destruct B1'.
      1,4,5,7-16:inversion LR_B12.
      + split; intros; eapply nat_neq_sort_red in A1_red_nat; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_nat.
      + split; intros; eapply nat_neq_pi_red in A1_red_nat; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_nat.
      + destruct LR_B12 as (eq' & _ & B2_red & ϵB_iff_ϵNat).
        split; intros; try rewrite H in *; try rewrite ϵB_iff_ϵNat in *.
        ++ eapply LR_irred_tm; eauto. eapply LR_nat; eauto.  
           reflexivity.
           1,2:destruct A1_red_nat, A2_red_nat, B1_red, B2_red.
           eauto 6 using redd_conv, redd_cast_nat_nat, validity_conv_left, LR_escape_ty.
           eauto 11 using redd_cast_nat_nat, validity_conv_right, type_conv, LR_escape_ty,
               conv_obseq, ctx_typing, conv_sort'.
        ++ eapply LR_irred_tm; eauto. eapply LR_nat; eauto.  
           reflexivity.
           1,2:destruct A1_red_nat, A2_red_nat, B1_red, B2_red.
           eapply redd_conv. eapply redd_cast_nat_nat; eauto using validity_conv_left.
           eauto using redd_to_conv, conv_trans, conv_sym.
           eapply redd_conv. eapply redd_cast_nat_nat; 
           eauto 8 using validity_conv_right, LR_escape_ty, type_conv, conv_obseq, ctx_typing, conv_sort'.
           eauto using redd_to_conv, conv_trans, conv_sym.

    - eapply LR_to_red in LR_B12 as temp. destruct temp as (B1' & B1_red).
      unshelve eapply LR_inv in LR_B12 ; eauto.
      simpl in LR_B12. destruct B1'.
      1,4,5,7-16:inversion LR_B12.
      + destruct LR_B12 as (eq' & _ & B2_red & ϵB_iff_ϵsort).
        eapply Ax_inj in eq'. subst.
        split; intros; try rewrite H0 in * ; try rewrite ϵB_iff_ϵsort in *.
        ++ destruct H1. eexists. eapply LR_irred_ty; eauto. 
           1,2:destruct B1_red, B2_red, A1_red_U, A2_red_U.
           eapply redd_conv. eapply redd_cast_sort_sort; eauto using validity_conv_left.
           eauto using redd_to_conv.
           eapply redd_conv. eapply redd_cast_sort_sort; 
           eauto 7 using validity_conv_right, LR_escape_ty, type_conv, conv_obseq, ctx_typing, conv_sort'.
           eauto using redd_to_conv.
        ++ destruct H1. eexists. eapply LR_irred_ty; eauto.
           1,2:destruct B1_red, B2_red, A1_red_U, A2_red_U.
           eapply redd_conv. eapply redd_cast_sort_sort; eauto using validity_conv_left.
           eauto using redd_to_conv.
           eapply redd_conv. eapply redd_cast_sort_sort; 
           eauto 7 using validity_conv_right, LR_escape_ty, type_conv, conv_obseq, ctx_typing, conv_sort'.
           eauto using redd_to_conv.
      + split; intros; eapply sort_neq_pi_red in A1_red_U; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_U.
      + split; intros; eapply nat_neq_sort_red in A1_red_U; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_U.
    - eapply LR_to_red in LR_B12 as temp. destruct temp as (B1' & B1_red).
      unshelve eapply LR_inv in LR_B12 ; eauto.
      simpl in LR_B12. destruct B1'.
      1,4,5,7-16:inversion LR_B12.
      + split; intros; eapply sort_neq_pi_red in A1_red_pi; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_pi.
      + destruct l0. 2:inversion LR_B12.
        rename B1'1 into S1'. rename B1'2 into T1'.
        destruct LR_B12 as (S2' & T2' & ϵS' & ϵT' & eq' & _ & B2_red & T1'_eq_T2' & LR_S12' & LR_T12' & ϵB_iff).
        split; intros; try rewrite ϵB_iff in *; try rewrite H in *.
        ++ eapply pi_sort_inj_red in A1_red_pi as temp; eauto using validity_conv_left, type_obseq_sym.
           destruct temp as (eq1 & eq2). dependent destruction eq2.
           unfold ϵPi. intros. split. 
           eapply conv_conv; eauto using conv_cast, LR_escape_ty, redd_whnf_to_conv.
           clear LR_A12' LR_B12'.
           intros s1 s2 ϵs.
           eapply H0 in LR_S12' as temp; eauto.
           destruct temp as (_ & K2).
           eapply K2 in ϵs as temp; eauto using LR_escape_tm. 
           2:{ eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            destruct H2.
            eapply H5 in temp as temp'.
            eapply H1 in temp. 2:eapply LR_T; eauto. 2,3:eauto using LR_T12'.
            destruct temp as (K1 & _). eapply LR_irred_tm; eauto. 3:eapply K1; eauto. all:clear K1 K2.
            4:{ eapply conv_injpi2 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            3:{ eapply conv_app'; eauto using LR_escape_ty. eapply conv_cast; eauto using LR_escape_ty, LR_escape_tm.
                eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
                eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            1,2:admit.
        ++ eapply pi_sort_inj_red in A1_red_pi as temp; eauto using validity_conv_left, type_obseq_sym.
           destruct temp as (eq1 & eq2). dependent destruction eq2.
           unfold ϵPi. intros. split. 
           eapply conv_conv; eauto using conv_cast, LR_escape_ty, redd_whnf_to_conv.
           intros s1 s2 ϵs.
           eapply H0 in LR_S12' as temp; eauto.
           destruct temp as (K2 & _).
           eapply K2 in ϵs as temp; eauto using LR_escape_tm. 
           2:{ eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            destruct H2.
            eapply H5 in temp as temp'.
            eapply H1 in ϵs as _temp. 2:eapply LR_T; eauto.  2,3:eauto using LR_T12'.
            destruct _temp as (_ & K1). eapply LR_irred_tm; eauto. 3:eapply K1; eauto. all:clear K1 K2.
            4:{ eapply conv_injpi2 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            3:{ eapply conv_app'; eauto using LR_escape_ty. eapply conv_cast; eauto using LR_escape_ty, LR_escape_tm.
                eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
                eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            1,2:admit.
      + split; intros; eapply nat_neq_pi_red in A1_red_pi; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_pi.
Admitted.


Lemma fundamental_cast Γ k A1 A2 B1 B2 e1 e2 a1 a2 :
    Γ ⊢< Ax (ty k) > A1 ≡ A2 : Sort (ty k) ->
    Γ ⊨< Ax (ty k) > A1 ≡ A2 : Sort (ty k) ->
    Γ ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊢< prop > e1 ≡ e2 : obseq (Ax (ty k)) (Sort (ty k)) A1 B1 ->
    Γ ⊨< prop > e1 ≡ e2 : obseq (Ax (ty k)) (Sort (ty k)) A1 B1 ->
    Γ ⊢< ty k > a1 ≡ a2 : A1 ->
    Γ ⊨< ty k > a1 ≡ a2 : A1 ->
    Γ ⊨< ty k > cast (ty k) A1 B1 e1 a1 ≡ cast (ty k) A2 B2 e2 a2 : B1.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 e1_conv_e2 _ a1_conv_a2 LRv_a12.
    unfold LRv. intros σ1 σ2 ϵσ.
    assert (Γ ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_A12 as temp; eauto. destruct temp as (ϵA & LR_A12).
    eapply LRv_to_LR_ty in LRv_B12 as temp; eauto. destruct temp as (ϵB & LR_B12).
    eapply LRv_to_LR_ty_copy in LRv_B11 as LR_B11; eauto.
    eapply LRv_to_LR_tm in LRv_a12 as LR_a12; eauto.
    clear LRv_A12 LRv_B11 LRv_B12 LRv_a12.
    eexists. split; eauto. ssimpl.
    eapply prefundamental_cast; eauto using subst, LR_subst_escape.
Qed.

Lemma prefundamental_cast_refl l A B ϵA e a1 a2 : 
    LR l A B ϵA -> 
    ϵA a1 a2 ->
    ∙ ⊢< prop > e : obseq (Ax l) (Sort l) A B ->
    ϵA (cast l A B e a1) a2.
Proof.
    intros LR_AB ϵa eWt.
    generalize l A B ϵA LR_AB e a1 a2 ϵa eWt.
    clear l A B ϵA LR_AB e a1 a2 ϵa eWt.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. rewrite H0 in *. 
      eapply conv_trans; eauto using conv_sym.
      eapply conv_conv; eauto using conv_sym.
      eapply conv_cast_refl; eauto using validity_conv_left.  
    - rewrite H in *. eapply LR_irred_tm; eauto using prefundamental_nat.
      2:eapply redd_refl; eauto using LR_escape_tm, prefundamental_nat, validity_conv_right.
      destruct A1_red_nat, A2_red_nat.
      eapply redd_conv. eapply redd_cast_nat_nat; 
      eauto 6 using LR_escape_tm, prefundamental_nat, type_conv, 
        redd_to_conv, conv_sym, validity_conv_left.
      eauto using redd_to_conv.
    - rewrite H0 in *. destruct ϵa as (R' & lr). exists R'. 
      eapply LR_irred_ty; eauto. 
      2:eapply redd_refl; eauto using LR_escape_ty, validity_conv_right. 
      destruct A1_red_U, A2_red_U.
      eapply redd_conv. eapply redd_cast_sort_sort; 
      eauto 6 using LR_escape_ty, type_conv, 
        redd_to_conv, conv_sym, validity_conv_left.
      eauto using redd_to_conv.
    - rewrite H in *. unfold ϵPi. split.
      admit.
      intros s1 s2 ϵs.
      eapply H0 in ϵs as ϵs'.
      2:{ eapply type_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty, validity_conv_right, conv_ty_in_ctx_conv.
          eapply type_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. 1,2:admit. }
      destruct ϵa.
      eapply H3 in ϵs' as temp.
      eapply H1 in temp; eauto.
      2:{ eapply type_conv. eapply type_injpi2 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply type_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. admit.
            eapply conv_obseq; eauto using ctx_typing, conversion. 1,2:admit. }
      assert (ϵT (cast i S1 S2 (injpi1 i (ty k) S2 S1 T2 T2 e) s1) s2 <~> ϵT s1 s2) by eauto 7 using LR_irrel, LR_sym.
      rewrite H4 in temp. clear H4.
      eapply LR_irred_tm; eauto.
Admitted.

Lemma fundamental_cast_refl Γ k A B e a :
    Γ ⊢< Ax (ty k) > A ≡ B : Sort (ty k) ->
    Γ ⊨< Ax (ty k) > A ≡ B : Sort (ty k) ->
    Γ ⊢< prop > e : obseq (Ax (ty k)) (Sort (ty k)) A B ->
    Γ ⊨< prop > e ≡ e : obseq (Ax (ty k)) (Sort (ty k)) A B ->
    Γ ⊢< ty k > a : A ->
    Γ ⊨< ty k > a ≡ a : A ->
    Γ ⊨< ty k > cast (ty k) A B e a ≡ a : B.
Proof.
    intros A_conv_B LRv_AB eWt LRv_e aWt LRv_a.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply LRv_to_LR_ty in LRv_AB as temp; eauto. destruct temp as (ϵA & LR_AB).
    eapply LRv_to_LR_tm in LRv_a as LR_a; eauto.
    assert (⊩s σ1 ≡ σ1 : Γ) as ϵσ11 by eauto using LR_subst_sym, LR_subst_trans.
    eapply LRv_to_LR_ty_copy in ϵσ11 as LR_AB'; eauto. clear ϵσ11.
    assert (Γ ⊨< Ax (ty k) > B ≡ B : Sort (ty k)) as LRv_BB by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_BB as temp; eauto. destruct temp as (ϵB & LR_B).
    assert (ϵB <~> ϵA) by eauto using LR_irrel, LR_sym. eapply LR_iff_rel in LR_B; eauto.
    clear ϵB H LRv_AB LRv_BB LRv_a.
    eexists. split; eauto.
    ssimpl. eapply prefundamental_cast_refl; eauto.
    eapply validity_conv_left, subst; eauto using refl_ty, LR_subst_escape.
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
    eauto 6 using subst, validity_conv_left, validity_ty_ty, 
        refl_ty, LR_subst_escape.    
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
    - eauto using fundamental_prop_ty.
    - eauto 9 using fundamental_accel, refl_ty.
    - eauto using fundamental_prop_ty. 
    - eauto 6 using fundamental_cast, refl_ty.
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
    - eauto using fundamental_prop_ty.
    - eauto using fundamental_accel.
    - eauto using fundamental_prop_ty.
    - eauto using fundamental_cast.
    - eauto using fundamental_cast_refl. 
    - admit. 
    - eauto using fundamental_conv.
    - eauto using fundamental_beta.
    - destruct j. eauto using fundamental_eta. eauto using fundamental_prop. 
    - eauto using fundamental_rec_zero.
    - eauto using fundamental_rec_succ.
    - eauto using fundamental_accel_accin.
    - unfold LRv. intros. eapply LR_subst_sym in H1. eapply H in H1 as (ϵA & LR_A & lr).
      eapply LR_sym in LR_A. eapply LR_sym_tm in lr; eauto.
    - unfold LRv. intros. assert (⊩s σ2 ≡ σ2 : Γ) by eauto using LR_subst_sym, LR_subst_trans.
      eapply H in H2 as (ϵA & LR_A & ϵtu). eapply H0 in H3 as (ϵA' & LR_A' & ϵuv).
      assert (ϵA <~> ϵA') by eauto using LR_sym, LR_irrel. rewrite <- H2 in ϵuv.
      eapply LR_trans_tm in ϵuv; eauto.
Admitted.

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
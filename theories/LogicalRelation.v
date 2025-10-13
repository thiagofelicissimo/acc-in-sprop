(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory. (*  Env Inst. *)
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
    fun t1 t2 => exists k, ∙ ⊢< ty 0 > t1 ≡ (mk_Nat k) : Nat /\ ∙ ⊢< ty 0 > t2 ≡ (mk_Nat k) : Nat.

Definition ϵPi i j S1 S2 (ϵS : TmRel) T1 T2 (ϵT : forall s1 s2, ϵS s1 s2 -> TmRel) : TmRel 
    := fun f1 f2 => 
        ∙ ⊢< Ru i j > f1 ≡ f2 : Pi i j S1 T1 /\
        forall s1 s2 (ϵs : ϵS s1 s2), ϵT s1 s2 ϵs (app i j S1 T1 f1 s1) (app i j S2 T2 f2 s2).

(* TODO replace conv by reduction *)
Inductive LRTy : forall (k : nat) (rec : forall j, j ◃ (ty k) -> LogRel), LogRel :=
| LRTy_nat A1 A2 rec : 
    ∙ ⊢< Ax (ty 0) > A1 ≡ Nat : Sort (ty 0) -> 
    ∙ ⊢< Ax (ty 0) > A2 ≡ Nat : Sort (ty 0) ->
    LRTy 0 rec A1 A2 ϵNat
| LRTy_pi1 i k A1 A2 S1 S2 ϵS T1 T2 ϵT
    (rec : forall j, j ◃ ty k -> LogRel)
    (q : i ◃ ty k) :
    ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) -> 
    ∙ ⊢< Ax (Ru i (ty k)) > A2 ≡ Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
    ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ A2 : Sort (Ru i (ty k)) ->
    rec i q S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LRTy k rec T1 T2 (ϵT s1 s2 ϵs)) ->
    LRTy k rec A1 A2 (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT)
| LRTy_pi2 k A1 A2 S1 S2 ϵS T1 T2 ϵT
    (rec : forall j, j ◃ ty k -> LogRel) :
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A1 ≡ Pi (ty k) (ty k) S1 T1 : Sort (Ru (ty k) (ty k)) -> 
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A2 ≡ Pi (ty k) (ty k) S2 T2 : Sort (Ru (ty k) (ty k)) ->
    ∙ ⊢< Ax (Ru (ty k) (ty k)) > A1 ≡ A2 : Sort (Ru (ty k) (ty k)) ->
    LRTy k rec S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        LRTy k rec T1 T2 (ϵT s1 s2 ϵs)) ->
    LRTy k rec A1 A2 (ϵPi (ty k) (ty k) S1 S2 ϵS T1 T2 ϵT)
| LRTy_pi3 n k A1 A2 S1 S2 ϵS T1 T2 ϵT
    (rec : forall j, j ◃ ty n -> LogRel)
    (q : k < n) :
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A1 ≡ Pi (ty n) (ty k) S1 T1 : Sort (Ru (ty n) (ty k)) -> 
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A2 ≡ Pi (ty n) (ty k) S2 T2 : Sort (Ru (ty n) (ty k)) ->
    ∙ ⊢< Ax (Ru (ty n) (ty k)) > A1 ≡ A2 : Sort (Ru (ty n) (ty k)) ->
    LRTy n rec S1 S2 ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), 
        rec (ty k) (ltac :(simpl; lia)) T1 T2 (ϵT s1 s2 ϵs)) ->
    LRTy n rec A1 A2 (ϵPi (ty n) (ty k) S1 S2 ϵS T1 T2 ϵT)
| LRTy_U l A1 A2 rec : 
    ∙ ⊢< Ax (Ax l) > A1 ≡ Sort l : Sort (Ax l) -> 
    ∙ ⊢< Ax (Ax l) > A2 ≡ Sort l : Sort (Ax l) ->
    LRTy (ax l) rec A1 A2 (fun B1 B2 => exists R, rec l lt_ty_ax B1 B2 R).


Definition LR (l : level) : LogRel.
    refine (@Fix_F _ (fun i j => i ◃ j) (fun _ => LogRel) _ l _).
    - intros. destruct x.
        + apply (LRTy n). apply X.
        + apply LRΩ.
    - apply wf_inverse_image. apply lt_wf.
Defined.

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
    ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ A2 : Sort (Ru i (ty k)) ->
    LR i S1 S2 ϵS -> 
    (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) T1 T2 (ϵT s1 s2 ϵs)) ->
    LR (Ru i (ty k)) A1 A2 (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT).
Proof.
    intros. unfold Ru. rewrite LR_ty_eq.
    assert (i ⊴ (ty k) \/ ty k ◃ i) by eauto using Nat.le_gt_cases.
    destruct H4. inversion H4.
    - pose proof (f_equal nat_to_lvl H6) as H'. rewrite lvl_to_nat_to_lvl in H'. rewrite H' in *. 
      simpl. assert (max k k = k) by lia. rewrite H5. apply LRTy_pi2; eauto. 
      rewrite <- LR_ty_eq. auto.
      rewrite <- LR_ty_eq. auto.
    - assert (ru i k = k). unfold ru. destruct i. simpl in H6. lia. auto.
      rewrite H7. apply LRTy_pi1; auto. 
      simpl. lia.
      rewrite <- LR_ty_eq. auto.
    - destruct i. 2:inversion H4.
      simpl in H4. assert (ru (ty n) k = n). unfold ru. lia.
      rewrite H5. apply LRTy_pi3; auto. lia. 
      rewrite <- LR_ty_eq. auto.
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
        (forall B1 B2 R, LR l B1 B2 R -> P l B1 B2 R) ->
        P (Ax l) A1 A2 (fun B1 B2 => exists R, LR l B1 B2 R))
    (p_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT
        (A1_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ Pi i (ty k) S1 T1 : Sort (Ru i (ty k)))
        (A2_red_pi : ∙ ⊢< Ax (Ru i (ty k)) > A2 ≡ Pi i (ty k) S2 T2 : Sort (Ru i (ty k)))
        (A1_eq_A2 : ∙ ⊢< Ax (Ru i (ty k)) > A1 ≡ A2 : Sort (Ru i (ty k)))      
        (LR_S : LR i S1 S2 ϵS)
        (LR_T : forall s1 s2 (ϵs : ϵS s1 s2), 
                LR (ty k) T1 T2 (ϵT s1 s2 ϵs)),
        P i S1 S2 ϵS -> 
        (forall s1 s2 (ϵs : ϵS s1 s2), P (ty k) T1 T2 (ϵT s1 s2 ϵs)) ->
        P (Ru i (ty k)) A1 A2 (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT))
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
        + rewrite H0 in H4. rewrite H0 in H5. rewrite <- LR_ty_eq in H5.
          assert (k = ru i k). unfold ru. destruct i. simpl in q. lia. lia.
          rewrite H7 at 1. apply p_pi; auto.
        + rewrite H0 in H4. rewrite <- LR_ty_eq in H4.
          rewrite H0 in x. rewrite <- LR_ty_eq in x.
          assert (k = ru (ty k) k). simpl. lia.
          rewrite H6 at 1. apply p_pi; auto.
        + rewrite H0 in *. rewrite <- LR_ty_eq in x.
          assert (ty n = Ru (ty n) (ty k)). simpl. f_equal. lia. rewrite H5 at 1.
          apply p_pi; auto. 
          intros. apply H. simpl. lia. auto.
        + rewrite H0. apply p_U; auto.
    - rewrite LR_prop_eq in x. apply p_prop. auto.
Qed.

Lemma LR_escape l A B R : 
    LR l A B R -> ∙ ⊢< Ax l > A ≡ B : Sort l /\ forall t u, R t u -> ∙ ⊢< l > t ≡ u : A.
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. split.
      + destruct p. auto.
      + destruct p. intros. destruct (H0 t u). auto.
    - intros. split.
      + eauto using conv_trans, conv_sym.
      + intros. unfold ϵNat in H. destruct H as (k & H1 & H2). eauto using conv_trans, conv_sym, conv_conv.
    - intros. split.
      + eauto using conv_trans, conv_sym.
      + intros. destruct H0 as (R & lr). apply H in lr as (t_eq_u & _). eauto using conv_trans, conv_sym, conv_conv.
    - intros. split; auto.
      intros. destruct H1 as (H' & _). eauto using conv_conv, conv_sym.
Qed.

Lemma LR_sym l A B R : 
    LR l A B R -> 
    LR l B A R /\ (forall t u, R t u -> R u t).
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. destruct p. split.
        + rewrite LR_prop_eq. constructor. auto using conv_sym. intros. 
          split; intro; destruct (H0 t u); eauto using conv_conv, conv_sym.
        + intros. destruct (H0 u t). destruct (H0 t u). eauto using conv_conv, conv_sym.
    - intros. split.
        + apply LR_nat; auto.
        + intros. destruct H as (k & H1 & H2). exists k. auto.
    - intros. split.
        + apply LR_U; auto.
        + intros B1 B2 H0. destruct H0 as (R & lr). exists R. 
          destruct (H B1 B2 R lr) as (H1 & H2). auto.
    - intros. split.
        + apply LR_pi; eauto using conv_sym, conv_trans.
        + intros f1 f2 ϵf. split.
            ++ destruct ϵf; eauto using conv_sym.
            ++ intros. destruct ϵf.
               destruct H as (LR_S' & sym_ϵS).
               destruct (H0 s1 s2 ϵs) as (LR_T' & sym_ϵT).
               admit. (* we need to be able to exchange converitble annotations *)
Admitted.

           
Lemma LR_irrel l A B1 B2 R1 R2 : 
    LR l A B1 R1 -> 
    LR l A B2 R2 -> 
    forall t1 t2, R1 t1 t2 <-> R2 t1 t2.
Proof.
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

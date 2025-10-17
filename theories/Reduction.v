(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.


(* I first tried to defined ⊢ t -->>! u by |t| -->>! |u| and ⊢ t ≡ u.
   The problem is that if ⊢ A -->>! Pi S T and ⊢ A -->>! A', then we know that
   A' = Pi S' T' with |S| = |S'| and |T| = |T'| and ⊢ Pi S T ≡ Pi S' T',
   but we cannot conclude that S ≡ S' and T ≡ T'. This poses problems
   when showing irrelevance of the logical relation, because we can only
   exchange types which are convertible and equal wrt |-| *)


Reserved Notation "Γ ⊢< l > t --> u : T" (at level 50, l, t, u, T at next level).
    

Inductive red  : ctx -> level -> term -> term -> term -> Prop :=
| red_app Γ t t' u i j A B :
    Γ ⊢< Ax i > A : Sort i -> 
    Γ ,, (i, A) ⊢< Ax j > B : Sort j -> 
    Γ ⊢< Ru i j > t --> t' : Pi i j A B -> 
    Γ ⊢< i > u : A ->
    Γ ⊢< j > app i j A B t u --> app i j A B t' u : B <[ u..]

| red_beta Γ t u i j A B A' B' : 
    Γ ⊢< Ax i > A ≡ A' : Sort i -> 
    Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j -> 
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< i > u : A →
    Γ ⊢< j > app i j A B (lam i j A' B' t) u --> t <[ u.. ] : B <[ u..]

| red_rec Γ l P p_zero p_succ n n' :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->    
    Γ ⊢< ty 0 > n --> n' : Nat -> 
    Γ ⊢< l > rec l P p_zero p_succ n --> rec l P p_zero p_succ n' : P <[ n.. ]

| red_rec_zero Γ l P p_zero p_succ :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< l > rec l P p_zero p_succ zero --> p_zero : P <[ zero .. ]

| red_rec_succ Γ l P p_zero p_succ n :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< ty 0 > n : Nat ->
    Γ ⊢< l > rec l P p_zero p_succ (succ n) --> p_succ <[  (rec l P p_zero p_succ n) .: n ..] : P <[ (succ n) .. ]

| red_conv Γ l t u A B :
    Γ ⊢< l > t --> u : A ->
    Γ ⊢< Ax l > A ≡ B : Sort l -> 
    Γ ⊢< l > t --> u : B
where "Γ ⊢< l > t --> u : T" := (red Γ l t u T).


Reserved Notation "Γ ⊢< l > t ~ u : T" (at level 50, l, t, u, T at next level).

Lemma red_to_conv Γ l t u A :
    Γ ⊢< l > t --> u : A -> Γ ⊢< l > t ≡ u : A.
Proof.
    intros. induction H; eauto using conversion, refl_ty.
    eapply conv_trans. eapply conv_app. 
    1,2:(eapply refl_ty; eauto using validity_conv_left).
    2: eauto using refl_ty.
    eapply conv_conv. eapply conv_lam; eauto using refl_ty, conv_sym, conv_ty_in_ctx_conv, type_conv.
    eapply conv_pi; eauto using conv_ty_in_ctx_conv, conv_sym.
    eauto using conv_beta, validity_conv_left.
Qed.


Inductive ann_conv : ctx -> level -> term -> term -> term -> Prop :=

| aconv_refl :
    ∀ Γ l t A,
      Γ ⊢< l > t : A -> 
      Γ ⊢< l > t ~ t : A
(* 
| aconv_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< Ru i j > lam i j A B t ~ lam i j A' B' t : Pi i j A B *)

| aconv_app :
    ∀ Γ i j A B t u A' B' t',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ~ t' : Pi i j A B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B t u ~ app i j A' B' t' u : B <[ u .. ] 


(* | aconv_succ : 
    ∀ Γ t t', 
      Γ ⊢< ty 0 > t ~ t' : Nat ->
      Γ ⊢< ty 0 > succ t ~ succ t' : Nat

| aconv_rec : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ~ P' : Sort l ->
      Γ ⊢< l > p_zero ~ p_zero' : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ~ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ~ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ~ rec l P' p_zero' p_succ' t' : P <[ t .. ] *)
  
| aconv_conv : 
    ∀ Γ l A B t t',
      Γ ⊢< l > t ~ t' : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ~ t' : B

(* | aconv_irrel : 
    ∀ Γ A t t',
      Γ ⊢< prop > t : A -> 
      Γ ⊢< prop > t' : A ->
      Γ ⊢< prop > t ~ t' : A *)

where "Γ ⊢< l > t ~ u : A" := (ann_conv Γ l t u A).

Lemma sim_to_conv Γ l t u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t ≡ u : A.
Proof.
    intros. induction H; eauto using conversion, refl_ty.
Qed.

Lemma sim_sym Γ l t u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > u ~ t : A.
Proof.
    intros. induction H; eauto using ann_conv.
    eapply aconv_conv.
    eapply aconv_app; eauto using conv_ty_in_ctx_conv, conv_sym, type_conv.
    eapply aconv_conv; eauto. 
    eauto using conv_pi.
    eauto using subst_ty, aux_subst_1, conv_sym.
Qed.


Definition aconv_inv_type Γ t v :=
    match t with 
    | app i j A B t u => 
        exists A' B' t', 
            v = app i j A' B' t' u /\
            Γ ⊢< Ax i > A ≡ A' : Sort i /\
            Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j /\
            Γ ⊢< Ru i j > t ~ t' : Pi i j A B 
    | _ => v = t 
    end.
    
Lemma aconv_inv Γ l t v T : 
    Γ ⊢< l > t ~ v : T -> aconv_inv_type Γ t v.
Proof.
    intro H.
    destruct t.
    1,2,3,4,6,7,8,9,10 : (dependent induction H; unfold aconv_inv_type in *; eauto).
    unfold aconv_inv_type.
    dependent induction H; eauto.
    - exists t1. exists t2. exists t3. apply type_inv_app' in H as (_ & AWt & BWt & tWT & _). repeat split; eauto using refl_ty, ann_conv.
    - exists A'. exists B'. exists t'. repeat split; eauto.
Qed.

(* Lemma aconv_inv Γ i j A B t u v l T :
    Γ ⊢< l > app i j A B t u ~ v : T ->
    exists A' B' t', 
        v = app i j A' B' t' u /\
        Γ ⊢< Ax i > A ≡ A' : Sort i /\
        Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j /\
        Γ ⊢< Ru i j > t ~ t' : Pi i j A B.
Proof.
  intro H.
  dependent induction H; eauto.
  - exists A. exists B. exists t. apply type_inv_app' in H as (_ & AWt & BWt & tWT & _). repeat split; eauto using refl_ty, ann_conv.
  - exists A'. exists B'. exists t'. repeat split; eauto.
Qed.

Lemma aconv_inv Γ i j A B t v l T :
    Γ ⊢< l > lam i j A B t ~ v : T ->
    v = lam i j A B t.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.
  
Lemma aconv_inv Γ i P p_zero p_succ n v l T :
    Γ ⊢< l > rec i P p_zero p_succ n ~ v : T ->
    v = rec i P p_zero p_succ n.
Proof.
  intro H.
  dependent induction H; eauto.
Qed. *)
  

Lemma sim_left_red Γ l t t' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t --> t' : A ->
    exists u', Γ ⊢< l > u --> u' : A 
    /\ Γ ⊢< l > t' ~ u' : A.
Proof.
    intros. generalize u H. clear u H. induction H0; intros.
    - apply aconv_inv in H3 as (A' & B' & v & u0_eq & A_conv_A' & B_conv_B' & t_sim_v). subst.
      eapply IHred in t_sim_v as (v' & v_red_v' & t'_sim_v').
      exists (app i j A' B' v' u). split.
      eapply red_conv. apply red_app; eauto using validity_conv_right, conv_ty_in_ctx_ty, conv_sym, type_conv.
      eapply red_conv; eauto.
      eapply conv_pi; eauto.
      eauto using subst_ty, aux_subst_1, conv_sym.
      eauto using ann_conv.
    - apply aconv_inv in H3 as (A'' & B'' & v & u0_eq & A_conv_A'' & B_conv_B'' & t_sim_v). subst.
      apply aconv_inv in t_sim_v. simpl in t_sim_v. subst.
      exists (t <[ u.. ]). split.
      eapply red_conv. eapply red_beta; eauto using conv_sym, conv_trans, conv_ty_in_ctx_conv, type_conv, conv_ty_in_ctx_ty.
      eauto using subst_ty, conv_sym, aux_subst_1.
      apply aconv_refl.
      eauto using subst2, aux_subst_1.
    - eapply aconv_inv in H3. simpl in H3. subst. 
      exists (rec l P p_zero p_succ n').
      split. eauto using red. 
      eapply aconv_conv. eapply aconv_refl. eauto using type_rec, red_to_conv, validity_conv_right.
      assert (Sort l = Sort l <[ n'.. ]) by (ssimpl; eauto). rewrite H3. eapply subst.
      eapply (conv_scons _ _ _ Γ (ty 0) Nat). eapply refl_subst. eapply subst_id. eauto using validity_ty_ctx.
      ssimpl. eauto using red_to_conv, conv_sym. eauto using refl_ty.
    - eapply aconv_inv in H2. simpl in H2. subst. exists p_zero. split; eauto using red, ann_conv. 
    - eapply aconv_inv in H3. simpl in H3. subst. exists (p_succ <[ rec l P p_zero p_succ n .: n..]).
      split. eauto using red. eapply aconv_refl. eapply validity_conv_right.
      eapply conv_rec_succ; eauto.
    - eapply aconv_conv in H1; eauto using conv_sym. eapply IHred in H1 as (u' & H' & H'').
      exists u'. split; eauto using red, ann_conv, conv_sym.
Qed.

Lemma sim_trans Γ l t u v A : 
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > u ~ v : A ->
    Γ ⊢< l > t ~ v : A.
Proof.
    intros. generalize v H0. clear v H0.
    induction H; intros.
    - eauto.
    - eapply aconv_inv in H3 as (A'' & B'' & t'' & v_eq & A'_conv_A'' & B'_conv_B'' & t'_sim_t''). subst.
      eapply aconv_app; eauto using conv_trans, conv_ty_in_ctx_conv, conv_sym. 
      eapply IHann_conv. eapply aconv_conv; eauto. eauto using conv_pi, conv_sym, conv_ty_in_ctx_conv.
    - eapply aconv_conv; eauto. eapply IHann_conv. eauto using aconv_conv, conv_sym.
Qed.

Reserved Notation "Γ ⊢< l > t -->> u : T" (at level 50, l, t, u, T at next level).

Inductive redd : ctx -> level -> term -> term -> term -> Prop := 
  | redd_refl Γ l t A : Γ ⊢< l > t : A -> Γ ⊢< l > t -->> t : A 
  | redd_step Γ l t u v A : Γ ⊢< l > t --> v : A -> Γ ⊢< l > v -->> u : A -> Γ ⊢< l > t -->>u : A 
where "Γ ⊢< l > t -->> t' : A " := (redd Γ l t t' A).




Lemma sim_left_redd Γ l t t' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->> t' : A ->
    exists u', Γ ⊢< l > u -->> u' : A 
    /\ Γ ⊢< l > t' ~ u' : A.
Proof.
    intros. generalize u H. clear u H. induction H0; intros.
    - exists u. split; eauto using redd, sim_to_conv, validity_conv_right.
    - pose proof H1 as t_sim_u0. eapply sim_left_red in H1 as (u' & u0_red_U' & v_sim_u'); eauto.
      eapply IHredd in v_sim_u' as (u'' & u'_redd & u_sim).
      exists u''. split; eauto using redd.
Qed.

Definition whnf Γ l t A := forall u, Γ ⊢< l > t --> u : A -> False.


Definition redd_whnf Γ l t t' A := redd Γ l t t' A /\ whnf Γ l t' A.

Notation "Γ ⊢< l > t -->>! u : T" := (redd_whnf Γ l t u T) (at level 50, l, t, u, T at next level).

Lemma redd_to_conv Γ l t u A :
    Γ ⊢< l > t -->> u : A -> Γ ⊢< l > t ≡ u : A.
Proof.
    intros. induction H; eauto using refl_ty, conv_trans, red_to_conv.
Qed.

Lemma redd_whnf_to_conv Γ l t u A :
    Γ ⊢< l > t -->>! u : A -> Γ ⊢< l > t ≡ u : A.
Proof.
    intros. destruct H.  eauto using redd_to_conv. 
Qed.


Lemma sim_left_redd_whnf Γ l t t' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->>! t' : A ->
    exists u', Γ ⊢< l > u -->>! u' : A 
    /\ Γ ⊢< l > t' ~ u' : A.
Proof.
    intros.
    destruct H0.
    eapply sim_left_redd in H0 as (u' & u_redd_u' & t'_sim_u'); eauto.
    exists u'. split; eauto.
    split; eauto.
    unfold whnf. intros. apply sim_sym in t'_sim_u'.
    eapply sim_left_red in H0 as (t'' & t'_red & _); eauto.
Qed.


Lemma red_det Γ l t u v A : 
    Γ ⊢< l > t --> u : A -> 
    Γ ⊢< l > t --> v : A ->
    u = v.
Proof.
Admitted.

Lemma redd_whnf_det Γ l t u v A : 
    Γ ⊢< l > t -->>! u : A -> 
    Γ ⊢< l > t -->>! v : A ->
    u = v.
Proof.
    intros. destruct H. generalize v H0. clear v H0. induction H; intros.
    - destruct H0. dependent destruction H0.
        + eauto.
        + eapply H1 in H0. inversion H0.
    - destruct H2. dependent destruction H2.
        + apply H3 in H. inversion H.
        + eapply red_det in H; eauto. subst.
          apply IHredd; eauto. split; eauto.
Qed.





(* 
Lemma app_redd_conv Γ l i j A B A' B' t u v :
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j ->
    Γ ⊢< l > app i j A B t u -->> v : A -> 
    Γ ⊢< l > app i j A' B' t u -->> v : A.
Proof.
    intros.
    destruct H1.
    split; auto.
    apply validity_conv_left in H2 as app_Wt.
    apply type_inv_app' in app_Wt as (_ & _ & _ & t_Wt & u_Wt & l_eq & T_conv).
    eapply conv_trans; eauto using conv_sym.
    rewrite l_eq in *.
    eapply conv_conv; eauto using conv_sym.
    eauto using conv_app, conv_trans, conv_sym, refl_ty.
Qed.
    
 *)

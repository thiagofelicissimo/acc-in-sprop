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

| red_accel Γ i l A R a q P p : 
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop -> 
    Γ ,, (i, A) ⊢< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< prop > q : acc i A R a -> 
    let Awk := (plus 2) ⋅ A in 
    let Rwk := (up_ren (up_ren (plus 2))) ⋅ R in 
    let Pwk := (up_ren (plus 2)) ⋅ P in 
    let pwk := (up_ren (up_ren (plus 2))) ⋅ p in
    let t0 := accinv i Awk Rwk ((plus 2) ⋅ a) ((plus 2) ⋅ q) (var 1) (var 0) in
    let t1 := accel i l Awk Rwk Pwk pwk (var 1) t0 in 
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in 
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i l A t4 t3 in
    Γ ⊢< l > accel i l A R P p a q --> p <[ t5 .: a ..] : P <[a ..]

| red_conv Γ l t u A B :
    Γ ⊢< l > t --> u : A ->
    Γ ⊢< Ax l > A ≡ B : Sort l -> 
    Γ ⊢< l > t --> u : B
where "Γ ⊢< l > t --> u : T" := (red Γ l t u T).


Reserved Notation "Γ ⊢< l > t ~ u : T" (at level 50, l, t, u, T at next level).

Lemma red_accel' Γ i l A R a q P p X Y : 
    Γ ,, (i, A) ⊢< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
    Γ ⊢< prop > q : acc i A R a -> 
    let Awk := (plus 2) ⋅ A in 
    let Rwk := (up_ren (up_ren (plus 2))) ⋅ R in 
    let Pwk := (up_ren (plus 2)) ⋅ P in 
    let pwk := (up_ren (up_ren (plus 2))) ⋅ p in
    let t0 := accinv i Awk Rwk ((plus 2) ⋅ a) ((plus 2) ⋅ q) (var 1) (var 0) in
    let t1 := accel i l Awk Rwk Pwk pwk (var 1) t0 in 
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in 
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i l A t4 t3 in
    X = p <[ t5 .: a ..] ->
    Y = P <[a ..] ->
    Γ ⊢< l > accel i l A R P p a q --> X : Y.
Proof.
    intros. subst. 
    eapply validity_ty_ty in H1 as temp. 
    eapply type_inv_acc' in temp as (_ & AWt & RWt & aWt & _).
    eauto using red_accel.
Qed.




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

Lemma red_app' Γ t t' u i j A B X Y :
    Γ ⊢< Ru i j > t --> t' : Pi i j A B -> 
    Γ ⊢< i > u : A ->
    X = app i j A B t' u -> 
    Y = B <[ u..] ->
    Γ ⊢< j > app i j A B t u --> X : Y.
Proof.
    intros. subst.
    eapply red_to_conv in H as temp.  eapply validity_conv_left in temp. eapply validity_ty_ty in temp.
    eapply type_inv_pi' in temp as (_ & Awt & BWt & _).
    eapply red_app; eauto.
Qed.

Lemma red_beta' Γ t u i j A B A' B' X Y : 
    Γ ⊢< Ax i > A ≡ A' : Sort i -> 
    Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j -> 
    Γ ,, (i , A) ⊢< j > t : B →
    Γ ⊢< i > u : A →
    X = t <[ u.. ] ->
    Y = B <[ u..] ->
    Γ ⊢< j > app i j A B (lam i j A' B' t) u --> X : Y.
Proof.
    intros. subst. eapply red_beta; eauto.
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
  
| aconv_conv : 
    ∀ Γ l A B t t',
      Γ ⊢< l > t ~ t' : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ~ t' : B

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
    1,2,3,4,6,7,8,9,10,11,12,13 : (dependent induction H; unfold aconv_inv_type in *; eauto).
    unfold aconv_inv_type.
    dependent induction H; eauto.
    - exists t1. exists t2. exists t3. apply type_inv_app' in H as (_ & AWt & BWt & tWT & _). repeat split; eauto using refl_ty, ann_conv.
    - exists A'. exists B'. exists t'. repeat split; eauto.
Qed.
  

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
    - eapply aconv_inv in H5. simpl in H5. subst. eexists. split; eauto using red. eauto using conversion, validity_conv_right, aconv_refl.
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

Lemma redd_trans Γ l t u v A :
    Γ ⊢< l > t -->> v : A -> 
    Γ ⊢< l > v -->> u : A ->
    Γ ⊢< l > t -->> u : A.
Proof.
    intros. induction H; eauto.
    eapply redd_step; eauto.
Qed.

Lemma redd_comp_redd_whnf Γ l t u v A :
    Γ ⊢< l > t -->> v : A -> 
    Γ ⊢< l > v -->>! u : A ->
    Γ ⊢< l > t -->>! u : A.
Proof.
    intros. destruct H0. 
    split; eauto using redd_trans.
Qed.

Lemma redd_app Γ i j A B t t' u :
    Γ ⊢< Ru i j > t -->> t' : Pi i j A B -> 
    Γ ⊢< i > u : A ->
    Γ ⊢< j > app i j A B t u -->> app i j A B t' u : B <[ u.. ].
Proof.
    intros. eapply redd_to_conv in H as H'. 
    eapply validity_conv_left in H'. eapply validity_ty_ty in H'.
    eapply type_inv_pi in H' as (AWt & BWt).
    dependent induction H.
    - eapply redd_refl. eauto using type_app.
    - eapply redd_step; eauto using red_app.
Qed.

Lemma red_to_redd Γ l t u A :
    Γ ⊢< l > t --> u : A -> 
    Γ ⊢< l > t -->> u : A.
Proof.
    intros. eapply red_to_conv in H as temp.
    eapply validity_conv_right in temp.
    eapply redd_step; eauto.
    eapply redd_refl. eauto.
Qed.

Lemma redd_conv Γ l t u B A :
    Γ ⊢< l > t -->> u : A -> 
    Γ ⊢< Ax l > A ≡ B : Sort l -> 
    Γ ⊢< l > t -->> u : B.
Proof.
    intros. induction H.
    - eapply redd_refl; eauto using type_conv.
    - eapply redd_step; eauto. eauto using red_conv.
Qed.



Lemma redd_rec Γ l P p_zero p_succ n n' :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->    
    Γ ⊢< ty 0 > n -->> n' : Nat -> 
    Γ ⊢< l > rec l P p_zero p_succ n -->> rec l P p_zero p_succ n' : P <[ n.. ].
Proof.
    intros. dependent induction H2.
    - eapply redd_refl. eauto using type_rec.
    - eapply redd_step; eauto using red_rec. 
      eapply redd_conv. eapply IHredd; eauto.
      eauto using subst_ty'', refl_ty, red_to_conv.
      eapply subst_ty''; eauto using refl_ty. 
      eapply conv_scons; ssimpl; 
      eauto using refl_subst, subst_id, validity_ty_ctx, red_to_conv, conv_sym.
Qed.


Lemma redd_rec_zero  Γ l P p_zero p_succ t : 
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< ty 0 > t -->> zero : Nat ->
    Γ ⊢< l > rec l P p_zero p_succ t -->> p_zero : P <[ zero .. ].
Proof.
    intros.
    dependent induction H2.
    - eapply red_to_redd. eapply red_rec_zero; eauto.
    - eapply redd_step. eapply red_conv. eapply red_rec; eauto. eapply subst_ty''. 2:eauto using refl_ty. 
      eapply conv_scons. ssimpl. eauto using refl_subst, subst_id, validity_ty_ctx. ssimpl. 
      eauto using red_to_conv, redd_to_conv, conv_sym, conv_trans.
      eapply IHredd; eauto.
Qed.

Lemma redd_rec_succ  Γ l P p_zero p_succ t n : 
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< ty 0 > t -->> succ n : Nat ->
    Γ ⊢< l > rec l P p_zero p_succ t -->> p_succ <[  (rec l P p_zero p_succ n) .: n ..] : P <[ (succ n) .. ].
Proof.
    intros.
    dependent induction H2.
    - eapply red_to_redd. eapply type_inv_succ' in H2 as (_ & nWt & _). eapply red_rec_succ; eauto.
    - eapply redd_step. eapply red_conv. eapply red_rec; eauto. eapply subst_ty''. 2:eauto using refl_ty. 
      eapply conv_scons. ssimpl. eauto using refl_subst, subst_id, validity_ty_ctx. ssimpl. 
      eauto using red_to_conv, redd_to_conv, conv_sym, conv_trans.
      eapply IHredd; eauto.
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


Definition red_inv_type Γ t v :=
    match t with 
    | app i j A B (lam i' j' A' B' t) u => 
        i = i' /\ 
        j = j' /\
        v = t <[ u.. ] /\ 
        Γ ⊢< Ax i > A ≡ A' : Sort i /\
        Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j /\
        Γ ,, (i , A) ⊢< j > t : B /\ 
        Γ ⊢< i > u : A 
    | app i j A B t u =>
        exists t', 
            v = app i j A B t' u /\
            Γ ⊢< Ax i > A : Sort i /\ 
            Γ ,, (i, A) ⊢< Ax j > B : Sort j /\
            Γ ⊢< Ru i j > t --> t' : Pi i j A B /\
            Γ ⊢< i > u : A
    | rec l P p_zero p_succ zero => 
        v = p_zero /\ 
        Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
        Γ ⊢< l > p_zero : P <[ zero .. ] /\
        Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]
    | rec l P p_zero p_succ (succ n) => 
        v = p_succ <[  (rec l P p_zero p_succ n) .: n ..] /\
        Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
        Γ ⊢< l > p_zero : P <[ zero .. ] /\
        Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
        Γ ⊢< ty 0 > n : Nat
    | rec l P p_zero p_succ n => 
        exists n',
            v = rec l P p_zero p_succ n' /\
            Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
            Γ ⊢< l > p_zero : P <[ zero .. ] /\
            Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
            Γ ⊢< ty 0 > n --> n' : Nat
    | accel i l A R P p a q =>  
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    let Awk := (plus 2) ⋅ A in 
    let Rwk := (up_ren (up_ren (plus 2))) ⋅ R in 
    let Pwk := (up_ren (plus 2)) ⋅ P in 
    let pwk := (up_ren (up_ren (plus 2))) ⋅ p in
    let t0 := accinv i Awk Rwk ((plus 2) ⋅ a) ((plus 2) ⋅ q) (var 1) (var 0) in
    let t1 := accel i l Awk Rwk Pwk pwk (var 1) t0 in 
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in 
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i l A t4 t3 in
        v = p <[ t5 .: a ..] /\ 
        Γ ⊢< Ax i > A : Sort i /\
        Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop /\ 
        Γ ,, (i, A) ⊢< Ax l > P : Sort l /\
        Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' /\
        Γ ⊢< i > a : A /\ 
        Γ ⊢< prop > q : acc i A R a
    | _ => False
    end.

Fixpoint size (t : term) : nat := 
  match t with 
  | var _ => 0
  | Sort _ => 0
  | Pi _ _ A B => 1 + size A + size B
  | lam _ _ A B t => 1 + size A + size B + size t
  | app _ _ A B t u => 1 + size A + size B + size t + size u
  | Nat => 0
  | zero => 0
  | succ t => 1 + size t
  | rec _ P p0 ps t => 1 + size P + size p0 + size ps + size t
  | accel _ _ A R a q P p => 1 + size A + size R + size a + size q + size P + size p 
  | acc _ A R a => 1 + size A + size R + size a 
  | accin _ A R a p => 1 + size A + size R + size a + size p
  | box => 0
end.


Lemma red_inv Γ l t u T : Γ ⊢< l > t --> u : T -> red_inv_type Γ t u.
Proof.
    generalize t Γ l u T. clear t Γ l u T.
    refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _). 
    eauto using wf_inverse_image, lt_wf.
    intros. induction H0.
    - destruct t.
      4: (unshelve eapply (H _ _) in H2; simpl). 4: lia. 4: inversion H2.
      all: simpl.
      all: eexists; eauto. 
    - simpl. split; eauto. split; eauto.
    - destruct n.
      7,8 :(unshelve eapply (H _ _) in H3; simpl). 7,8: lia. 7,8: inversion H3.
      all: simpl.
      all: eexists; eauto.
    - simpl. split; eauto. 
    - simpl. split; eauto.
    - simpl. split; eauto. split; eauto.
    - eapply IHred. eauto.
Qed.


Lemma red_det Γ l t u v A : 
    Γ ⊢< l > t --> u : A -> 
    Γ ⊢< l > t --> v : A ->
    u = v.
Proof.
    intros. 
    generalize v H0. clear v H0. induction H; intros.
    - apply red_inv in H3. destruct t. 
      4: (apply red_inv in H1; inversion H1).
      all: destruct H3 as (t'' & eq & _ & _ & red & _). all: eapply IHred in red. all: subst. all: eauto.
    - apply red_inv in H3 as (_ & _ & eq & _). eauto.
    - apply red_inv in H3. destruct n.
      7,8 : (apply red_inv in H2; inversion H2).
      all: destruct H3 as (n'' & eq & _ & _ & _ & red). all: eapply IHred in red. all: subst. all: eauto.
    - apply red_inv in H2 as (eq & _). eauto.
    - apply red_inv in H3 as (eq & _). eauto.
    - apply red_inv in H5 as (eq & _). eauto.
    - eapply IHred. eapply red_conv; eauto using conv_sym.
Qed.

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

Definition val t := 
    match t with 
    | app i j A B t u => False
    | rec i P pzero psucc n => False 
    | accel _ _ A R a q P p => False
    | _ => True 
    end.

Lemma val_redd_to_whnf Γ l t A : Γ ⊢< l > t : A -> val t -> Γ ⊢< l > t -->>! t : A.
Proof.
    intros.
    split; eauto using redd_refl.
    unfold whnf. intros.
    destruct t.
    1-4,6-8, 10, 11, 13: eapply red_inv in H1; inversion H1. 
    1, 2, 3: inversion H0.
Qed.

Lemma sim_left_redd_whnf_val Γ l t t' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->>! t' : A ->
    val t' ->
    Γ ⊢< l > u -->>! t' : A.
Proof.
    intros.
    eapply sim_left_redd_whnf in H0 as (u' & u_redd_u' & t'_sim_u'); eauto.
    destruct t'.
    5,9: inversion H1.
    all: eapply aconv_inv in t'_sim_u'; simpl in t'_sim_u'; subst; eauto.
Qed.

Lemma iredd_comp_redd_whnf Γ l t u v A :
    Γ ⊢< l > v -->> t : A -> 
    Γ ⊢< l > v -->>! u : A ->
    Γ ⊢< l > t -->>! u : A.
Proof.
    intros. destruct H0.
    split; eauto.
    generalize u H0 H1. clear u H0 H1.
    dependent induction H.
    - intros. eauto.
    - intros. dependent destruction H1.
      + eapply H2 in H. inversion H.
      + eapply red_det in H; eauto. subst. 
        eapply IHredd; eauto.
Qed.
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Contexts Typing TypingP BasicMetaTheory BasicMetaTheoryP TypeUniquenessP Fundamental CHeqProps CDecoration.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.
(* New notations for source derivations *)

Notation "Γ ∋< l >× x : T" :=
  (Typing.varty Γ x l T) (at level 50, l, x, T at next level).

Notation "Γ ⊢< l >× t : A" :=
  (Typing.typing Γ l t A) (at level 50, l, t, A at next level).

Notation "Γ ⊢< l >× t ≡ u : T" :=
 (Typing.conversion Γ l t u T) (at level 50, l, t, u, T at next level).

Notation "⊢× Γ" :=
  (Typing.ctx_typing Γ) (at level 50).

Notation "⊢× Γ ≡ Δ"  :=
  (Typing.ConvCtx Γ Δ) (at level 50, Δ at next level).



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


(* Definition eqtrans Γ' l u v A u' A' v' e :=
  match l with
  | prop => True
  | ty i =>
    A ⊏ A' ∧
    u ⊏ u' ∧
    v ⊏ v' ∧
    Γ' ⊢< ty i > u' : A' /\
    Γ' ⊢< ty i > v' : A' /\
    Γ' ⊢< prop > e : heq (ty i) A' A' u' v'
  end. *)

Definition eqtrans Γ' l u v A u' A' v' A'' e :=
  match l with
  | prop => A ⊏ A' 
  | ty i =>
    A ⊏ A' ∧
    (* A ⊏ A'' ∧ *)
    u ⊏ u' ∧
    v ⊏ v' ∧
    Γ' ⊢< ty i > u' : A' /\
    Γ' ⊢< ty i > v' : A'' /\
    Γ' ⊢< prop > e : heq (ty i) A' A'' u' v'
  end.

Lemma decombine_subst_aux Γ i A1 A2 e :
  Γ ⊢< Ax i > A1 : Sort i ->
  Γ ⊢< Ax i > A2 : Sort i ->
  Γ ⊢< prop > e : obseq (Ax i) (Sort i) A1 A2 ->
  Γ ,, (i, A1) ⊢< i > cast i (S ⋅ A1) (S ⋅ A2) (S ⋅ e) (var 0) : S ⋅ A2.
Proof.
  intros.
  econstructor; eauto. 
  (* 4:econstructor;eauto. *)
  1,2,3:eapply type_ren; eauto using ctx_typing, WellRen_S, validity_ty_ctx.
  econstructor. 2:econstructor. econstructor; eauto using validity_ty_ctx.
Qed.

(* Lemma decombine_subst_aux2 Γ i A1 A2 e :
  Γ ⊢< Ax i > A1 : Sort i ->
  Γ ⊢< Ax i > A2 : Sort i ->
  Γ ⊢< prop > e : heq (Ax i) (Sort i) (Sort i) A1 A2 ->
  Γ ,, (i, A1) ⊢< i > cast i (S ⋅ A1) (S ⋅ A2) e'' (var 0) : S ⋅ A2 ->
  Γ ,, (i, A1) ⊢
  exists e'', Γ ,, (i, A1) ⊢< i > cast i (S ⋅ A1) (S ⋅ A2) e'' (var 0) : S ⋅ A2.
Proof.
  intros. *)
Lemma cast_subst Γ i A1 A2 e :
  Γ ⊢< Ax i > A1 : Sort i ->
  Γ ⊢< Ax i > A2 : Sort i ->
  Γ ⊢< prop > e : obseq (Ax i) (Sort i) A1 A2 ->
  Γ ,, (i, A1) ⊢s (cast i (S ⋅ A1) (S ⋅ A2) (S ⋅ e) (var 0).: (S >> var)) : Γ ,, (i, A2).
Proof.
  intros.
  econstructor;ssimpl.
  2:rasimpl ; econstructor.
  2-4:eapply type_ren; eauto using ctx_typing, WellRen_S, validity_ty_ctx.
  2:econstructor. 3:econstructor. 2:eauto using ctx_typing, validity_ty_ctx.
  admit.
Admitted.

Lemma cast_subst_refines t u i A B e : 
  t ⊏ u ->
  t ⊏ u <[ (cast i A B e (var 0)) .: (S >> var)].
Proof.
  intros. 
  replace t with (t <[ (var 0) .: (S >> var)]).
  2:setoid_rewrite subst_id_reduce1; rasimpl; reflexivity.
  eapply substs_decs. 2:eauto.
  unfold dec_subst. intros.
  destruct x.
  - simpl. econstructor. econstructor.
  - simpl. unfold ">>". econstructor.
Qed.



Lemma decombine_subst Γ i A1 A2 e :
  Γ ⊢< Ax i > A1 : Sort i ->
  Γ ⊢< Ax i > A2 : Sort i ->
  Γ ⊢< prop > e : obseq (Ax i) (Sort i) A1 A2 ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in    
  exists e',
  Γ ,, (i, A1) ⊢s (e' .: ((cast i (S ⋅ A1) (S ⋅ A2) (S ⋅ e) (var 0)) .: var)) : Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq).
Proof.
  intros.
  eapply decombine_subst_aux in H1 as h1; eauto.
  eexists. 
  econstructor. 1:econstructor.
  2,3:unfold ">>"; simpl; rasimpl.
  2:eauto.
  (* 2:econstructor. 3:econstructor. 2:eauto using validity_ty_ctx,ctx_typing. *)
  2:unfold Aeq. 2:rewrite heq_subst. 2:rasimpl.
  2:eapply type_heq_cast; eauto using type_ren, ctx_typing, WellRen_S, validity_ty_ctx.
  2:econstructor. 3:econstructor. 2:econstructor;eauto using validity_ty_ctx.
  ssimpl. eapply subst_id; eauto using ctx_typing, validity_ty_ctx.
Qed. 

(* 
Lemma decombine_subst Γ i A1 A2 e :
  Γ ⊢< Ax i > A1 : Sort i ->
  Γ ⊢< Ax i > A2 : Sort i ->
  Γ ⊢< prop > e : heq (Ax i) (Sort i) (Sort i) A1 A2 ->
  let Aeq := heq i ((S >> S >> S) ⋅ A1) ((S >> S >> S) ⋅ A2) (var 1) (var 0) in    
  exists e' e'',
  Γ ,, (i, A1) ⊢s (e' .: ((cast i (S ⋅ A1) (S ⋅ A2) e'' (var 0)) .: ((var 0) .: (S >> var)))) : Γ ,, (i, S ⋅ A1) ,, (i, (S >> S) ⋅ A2) ,, (prop, Aeq).
Proof.
  intros.
  eapply decombine_subst_aux in H1 as h1; eauto.
  destruct h1. destruct H2.
  eexists. exists x.
  econstructor. 1:econstructor. 1:econstructor.
  2,3,4:unfold ">>"; simpl; rasimpl.
  3:eauto.
  2:econstructor. 3:econstructor. 2:eauto using validity_ty_ctx,ctx_typing.
  2:unfold Aeq. 2:rewrite heq_subst. 2:rasimpl.
  2:eapply type_heq_cast; eauto using type_ren, ctx_typing, WellRen_S, validity_ty_ctx.
  2:econstructor. 3:econstructor. 2:econstructor;eauto using validity_ty_ctx.
  ssimpl. *)

  

Notation "D ⊨⟨ l ⟩ t ≃ u : A" := (* heterogeneous A *)
  (exists t' u' A' A'' e, A ⊏ A'' /\ eqtrans D l t u A t' A' u' A'' e)
  (at level 50, t, u, A at next level).


Notation "D ⊨⟨ l ⟩ t = u : A" := (* homogeneous A *)
  (exists t' u' A' e, eqtrans D l t u A t' A' u' A' e)
  (at level 50, t, u, A at next level).

Notation "D ⊨⟨ l ⟩ t ≃ u : A ↦ A' = A''" :=
  (exists t' u' e, eqtrans D l t u A t' A' u' A'' e)
  (at level 50, t, u, A, A', A'' at next level).  


Notation "D ⊨⟨ l ⟩ t = u : A ↦ A'" :=
  (exists t' u' e, eqtrans D l t u A t' A' u' A' e)
  (at level 50, t, u, A, A' at next level).


Lemma eqtrans_hetero_to_homo Γ' l t u A : 
  Γ' ⊨⟨ l ⟩ t ≃ u : A ->
  Γ' ⊨⟨ l ⟩ t = u : A.
Proof.
  intros. destruct H as (t' & u' & A' & A'' & e & h).
  destruct l. 
  2:{ exists A'', Nat, A'', Nat. cbn. destruct h; eauto. }
  destruct h as (h1 & h2 & h3 & h4 & h5 & h6 & h7).
  assert (A' ~ A'') by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H; eauto using validity_ty_ty.
  destruct H.
  eapply type_hetero_to_homo in H; eauto using validity_ty_ty.
  eapply type_obseq_sym in H.
  eapply type_heq_cast in h6 as H'; eauto. 2,3:eauto using validity_ty_ty.
  eapply type_heq_trans in H'. 5:eapply h7. all:eauto using type_cast, validity_ty_ty.
  eexists _, _,_,_.
  split. 2:split. 3:split. 4:split. 5:split.
  6:eapply H'.
  all:eauto using decoration, type_cast, validity_ty_ty.
Qed.


Lemma eqtrans_homo_to_hetero Γ' l t u A :
  Γ' ⊨⟨ l ⟩ t = u : A ->
  Γ' ⊨⟨ l ⟩ t ≃ u : A.
Proof.
  intros.
  destruct H as (t' & u' & A' & e & h).
  destruct l.
  - eexists _, _, _, _, _.
    split; [|eassumption]. now destruct h.
  - eexists _, _, _, _, _.
    split; eauto.
Qed.

Corollary eqtrans_homo_hetero  Γ' l t u A :
  Γ' ⊨⟨ l ⟩ t = u : A <-> Γ' ⊨⟨ l ⟩ t ≃ u : A.
Proof.
  split; eauto using eqtrans_hetero_to_homo, eqtrans_homo_to_hetero.
Qed.

Lemma tr_conv_change_ty Γ l t u A A' B B' e:
  A ⊏ A' ->
  B ⊏ B' ->
  Γ ⊨⟨ l ⟩ t ≃ u : A ->
  Γ ⊢< prop > e : obseq (Ax l) (Sort l) A' B' -> 
  Γ ⊨⟨ l ⟩ t ≃ u : A ↦ A' = B'.
Proof.
  intros.
  destruct H1 as (t' & u' &  A0' & A0'' & e').
  destruct l.
  2:admit.
  destruct e' as (e' & h1 & h2 & h3 & h4 & h5 & h6 & h7).
  eapply validity_ty_ty in H2 as H2'.
  eapply type_inv in H2'. dependent destruction H2'.
  assert (A' ~ A0') by eauto using dec_to_sim, sim_sym, sim_trans. 
  assert (A' ~ A0'') by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H1, H3; eauto using validity_ty_ty.
  destruct H3, H1.
  assert (exists e'', Γ ⊢< prop > e'' : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) A' B') by admit.
  destruct H4. clear H2.
  eapply type_heq_sym in H4; eauto.
  (* eapply type_heq_trans in H3; eauto using validity_ty_ty. *)
  eapply type_heq_trans in H3; eauto using validity_ty_ty. clear H4.
  eapply type_hetero_to_homo in H3, H1; eauto using validity_ty_ty.
  eapply type_obseq_sym in H1, H3; eauto using validity_ty_ty.
  eapply type_heq_cast in h5 as h5'. 4:eauto. all:eauto using validity_ty_ty.
  eapply type_heq_cast in h6 as h6'. 4:eauto. all:eauto using validity_ty_ty.
  eapply type_heq_trans in h6'. 5:eapply h7. all:eauto.
  2:eapply type_cast; eauto using validity_ty_ty.
  eapply type_heq_sym in h5'; eauto using typing, validity_ty_ty.
  eapply type_heq_trans in h6'. 5:eauto.
  all:eauto using typing, validity_ty_ty.
  eexists _,_,_. split. 2:split. 3:split. 4:split. 5:split.
  6:eapply  h6'.
  all :eauto using typing, validity_ty_ty, decoration.
Admitted.

Lemma tr_conv_change_ty' Γ l t u A A' :
  A ⊏ A' ->
  Γ ⊨⟨ l ⟩ t = u : A ->
  Γ ⊢< Ax l > A' : Sort l ->
  Γ ⊨⟨ l ⟩ t = u : A ↦ A'.
Proof.
  intros.
  destruct H0 as (t' & u' &  A0' & e & h').
  destruct l. 2:admit.
  destruct h' as (h1 & h2 & h3 & h4 & h5 & h6).
  assert (A' ~ A0') by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H0; eauto using validity_ty_ty.
  destruct H0.
  eapply type_heq_sym in H0; eauto using validity_ty_ty.
  eapply type_hetero_to_homo in H0; eauto using validity_ty_ty.
  eapply type_cast in h4 as h4'; eauto using validity_ty_ty.
  eapply type_cast in h5 as h5'; eauto using validity_ty_ty.
  eapply type_heq_cast in h4 as h4''; eauto using validity_ty_ty.
  eapply type_heq_cast in h5 as h5''; eauto using validity_ty_ty.
  eapply type_heq_trans in h5''. 5:eauto.
  all:eauto. 
  eapply type_heq_sym in h4''; eauto using validity_ty_ty.
  eapply type_heq_trans in h5''. 5:eauto. all:eauto using validity_ty_ty.
  eexists _, _, _.
  split. 2:split. 3:split. 4:split. 5:split.
  6:eapply h5''.
  all:eauto using decoration.
Admitted.


Lemma ty_conv_homo_destruct Γ l t u A A' : 
  Γ ⊨⟨ l ⟩ t = u : A ↦ A' ->
  exists t' u' e,
  Γ ⊨⟨ l ⟩ t : A ↦ t' : A' /\
  Γ ⊨⟨ l ⟩ u : A ↦ u' : A' /\
  Γ ⊢< prop > e : heq l A' A' t' u'.
Proof.
  intros.
  destruct H as (t' & u' & e & h).
  destruct l. 2:admit.
  destruct h as (h1 & h2 & h3 & h4 & h5 & h6).
  eexists _,_,_.
  split.
  2:split.
  1:split. 2:split.
  4:split. 5:split.
  1:eapply h4. 3:eapply h5.
  all:eauto.
Admitted.


Notation "D ⊨⟨ l ⟩ t : A ≃ u : B" := (* heterogeneous A *)
  (exists t' u' A' B' e, B ⊏ B' /\ eqtrans D l t u A t' A' u' B' e)
  (at level 50, t, A, u, B at next level).

Lemma tr_eq_make_hetero Γ' e l A A' B B' t u :
  Γ' ⊢< Ax l > A' : Sort l ->
  Γ' ⊢< Ax l > B' : Sort l ->
  Γ' ⊢< prop > e : heq (Ax l) (Sort l) (Sort l) A' B' -> 
  A ⊏ A' ->
  B ⊏ B' ->
  Γ' ⊨⟨ l ⟩ t : A ≃ u : B ->
  Γ' ⊨⟨ l ⟩ t = u : A.
Proof.
  intros.
  rewrite eqtrans_homo_hetero.
  destruct l. 2:admit.
  destruct H4 as (t' & u' & A_ & A__ & e' & H4).
  (* eapply validity_ty_ty in H as H'. eapply type_inv in H'. dependent destruction H'. *)
  repeat destruct H4 as (? & H4).
  assert (B' ~ A__) by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H11; eauto using validity_ty_ty. destruct H11.
  eapply type_heq_trans in H11. 5:eauto. all:eauto using validity_ty_ty.
  eapply type_hetero_to_homo in H11; eauto using validity_ty_ty.
  eapply type_obseq_sym in H11.
  eapply type_heq_cast in H10 as H10'. 4:eapply H11. all: eauto using validity_ty_ty.
  eapply type_heq_trans in H10'. 5:eauto. all:eauto. 2:econstructor;eauto using validity_ty_ty.
  eexists _,_,_,_,_. split. 2:unfold eqtrans. 
  2:split. 3:split. 4:split. 5:split. 6:split. 
  7:eapply H10'.
  all:eauto.
  1:econstructor; eauto.
  econstructor; eauto using validity_ty_ty.
Admitted.


Lemma tr_eq_conclude Γ' e l A A' B B' t t' u u' :
  t ⊏ t' ->
  u ⊏ u' ->
  A ⊏ A' ->
  B ⊏ B' ->
  Γ' ⊢< l > t' : A' ->
  Γ' ⊢< l > u' : B' ->
  Γ' ⊢< prop > e : heq l A' B' t' u' ->
  Γ' ⊨⟨ l ⟩ t = u : A.
Proof.
  intros. 
  destruct l. 2:admit.
  assert (exists e', Γ' ⊢< prop > e' : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) A' B') by admit.
  destruct H6.
  eapply tr_eq_make_hetero in H6; eauto using validity_ty_ty.
  eexists _,_,_,_,_. split.
  2:split. 3:split. 4:split. 5:split. 6:split.
  7:eapply H5. all:eauto.
Admitted.


Lemma aaux_old Γ' e l A A' B B' t u :
  Γ' ⊢< Ax l > A' : Sort l ->
  Γ' ⊢< Ax l > B' : Sort l ->
  Γ' ⊢< prop > e : heq (Ax l) (Sort l) (Sort l) A' B' -> 
  A ⊏ A' ->
  B ⊏ B' ->
  Γ' ⊨⟨ l ⟩ t ≃ u : A ->
  Γ' ⊨⟨ l ⟩ t : A ≃ u : B.
Proof.
  intros.
  destruct l. 2:admit.
  destruct H4 as (t' & u' & A_ & A__ & e' & H4).
  (* eapply validity_ty_ty in H as H'. eapply type_inv in H'. dependent destruction H'. *)
  repeat destruct H4 as (? & H4).
  assert (A__ ~ A') by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H11; eauto using validity_ty_ty. destruct H11.
  eapply type_heq_trans in H1. 5:eauto. all:eauto using validity_ty_ty.
  eapply type_hetero_to_homo in H1; eauto using validity_ty_ty.
  eapply type_heq_cast in H10 as H10'; eauto using validity_ty_ty.
  eapply type_heq_trans in H10'. 5:eauto. all:eauto.
  2:econstructor; eauto using validity_ty_ty.
  eexists _,_,_,_,_. intuition eauto. unfold eqtrans. 
  split. 2:split. 3:split. 4:split. 5:split. 
  6:eapply H10'.
  all:eauto.
  1:econstructor; eauto.
  econstructor; eauto using validity_ty_ty.
Admitted.

(* Lemma ty_conv_hetero_destruct Γ l t u A A' B B': 
  Γ ⊨⟨ l ⟩ t ≃ u : A ↦ A' B' ->
  exists t' u' e,
  Γ ⊨⟨ l ⟩ t : A ↦ t' : A' /\
  Γ ⊨⟨ l ⟩ u : A ↦ u' : A' /\
  Γ ⊢< prop > e : heq l A' A' t' u'.
Proof.
  intros.
  destruct H as (t' & u' & e & h).
  destruct l. 2:admit.
  destruct h as (h1 & h2 & h3 & h4 & h5 & h6).
  eexists _,_,_.
  split.
  2:split.
  1:split. 2:split.
  4:split. 5:split.
  1:eapply h4. 3:eapply h5.
  all:eauto.
Admitted. *)




(* 
Definition new_eqtrans Γ l t u A := 
  forall Δ B, 
  ⊢× Γ ≡ Δ ->
  Γ ⊢< Ax l >× A ≡ B : Sort l ->
  forall Γ' Δ',
  tr_ctx Γ Γ' -> 
  tr_ctx Δ Δ' ->
  exists t' u' A' B' e,
    t ⊏ t' ∧
    u ⊏ u' ∧
    A ⊏ A' ∧
    B ⊏ B' ∧
    Γ' ⊢< l > t' : A' /\
    Δ' ⊢< l > u' : B' /\  
    pack Γ Δ ⊢< prop > e : heq l (renL ⋅ A') (renR ⋅ B') (renL ⋅ t') (renR ⋅ u'). *)


(* Type heads *)

Inductive type_head := hSort (l : level) | hPi | hNat | hacc | hobseq.

Inductive has_type_head : term → type_head → Prop :=
| isSort l : has_type_head (Sort l) (hSort l)
| isPi i j A B : has_type_head (Pi i j A B) hPi
| isNat : has_type_head Nat hNat
| isacc i A R x : has_type_head (acc i A R x) hacc
| isobseq i A u v : has_type_head (obseq i A u v) hobseq.

Lemma keep_head_ty_aux Γ l A t h u :
  t ⊏ u ->
  Γ ⊢< l > u : A -> 
  has_type_head t h ->
  exists B e v, 
    t ⊏ v /\
    has_type_head v h /\
    Γ ⊢< l > v : B /\
    Γ ⊢< prop > e : heq l A B u v.
Proof.
  intros. induction H1.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H0. dependent destruction H0. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx, decoration.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    + eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H1. dependent destruction H1. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx. 
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H0. dependent destruction H0. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    + eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H2. dependent destruction H2. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym. 4,5:eapply conv_refl.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eauto using typing, conv_sym.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H2. dependent destruction H2. subst.
      eexists. eexists. eexists. 
      Unshelve. 4:exact (obseq (ty n) A' a' b'). 2,3:shelve.  
      intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym. 4,5:eapply conv_refl.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eauto using typing, conv_sym.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v' & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
Qed.

Lemma keep_head_ty Γ l A A0 h :
  A0 ⊏ A ->
  Γ ⊢< Ax l > A : Sort l -> 
  has_type_head A0 h ->
  exists B e, 
    A0 ⊏ B /\
    has_type_head B h /\
    Γ ⊢< prop > e : obseq (Ax l) (Sort l) A B.
Proof.
  intros. eapply keep_head_ty_aux in H1; eauto.
  destruct H1 as (B & e & v & refines & has_head & v_Wt & e_Wt).
  dependent destruction has_head;
  eapply type_inv in v_Wt; dependent destruction v_Wt.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - dependent destruction lvl_eq. destruct l; dependent destruction H1.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    4:eapply conv_refl.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo. 3:eapply e_Wt. all:eauto using typing, validity_ty_ctx.
Qed.


Lemma keep_head Γ' l t A h :
  Γ' ⊨⟨ l ⟩ t : A →
  has_type_head A h →
  ∃ A',
    has_type_head A' h ∧
    Γ' ⊨⟨ l ⟩ t : A ⇒ A'.
Proof.
  intros ht hh.
  destruct ht. destruct H. destruct H. destruct H0.
  eapply validity_ty_ty in H as H'.
  eapply keep_head_ty in hh; eauto.
  destruct hh as (B & e & refines & has_head & e_Wt).
  eexists. split; eauto.
  econstructor. econstructor. 
  1:eapply type_cast.
  3:eapply e_Wt.
  3:eauto.
  3:intuition eauto using decoration.
  all:eapply validity_ty_ty, type_inv in e_Wt; dependent destruction e_Wt; eauto.
Qed.
(* 
Lemma keep_head_conv Γ' l t u A h :
  Γ' ⊨⟨ l ⟩ t ≡ u : A →
  has_type_head A h →
  ∃ A',
    has_type_head A' h ∧
    Γ' ⊨⟨ l ⟩ t ≡ u : A ⇒ A'.
Proof.
  intros ht hh.
  destruct ht. destruct H. destruct H. destruct H. 
  destruct H0. destruct H1.
  eapply validity_conv_left in H as H'. eapply validity_ty_ty in H'.
  eapply keep_head_ty in hh; eauto.
  destruct hh as (B & e & refines & has_head & e_Wt).
  eexists. split; eauto.
  econstructor. econstructor. econstructor. 
  1:eapply conv_cast.
  3:eapply conv_refl, e_Wt.
  3:eauto.
  1:eauto using conv_refl.
  1:eapply validity_ty_ty, type_inv in e_Wt; dependent destruction e_Wt; eauto using conv_refl.
  intuition eauto using decoration.
Qed. *)

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

(* Corollary keep_sort_conv Γ' i j A B :
  Γ' ⊨⟨ i ⟩ A ≡ B : Sort j →
  Γ' ⊨⟨ i ⟩ A ≡ B : Sort j ⇒ Sort j.
Proof.
  intros h.
  eapply keep_head_conv in h. 2: econstructor.
  destruct h as (A' & h & hA).
  inversion h. subst.
  assumption.
Qed. *)

Lemma change_type Γ' i t A A' :
  Γ' ⊨⟨ i ⟩ t : A →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ' ⊨⟨ i ⟩ t : A ⇒ A'.
Proof.
  intros.
  destruct H. destruct H. destruct H. destruct H1.
  destruct H0. destruct H3.
  assert (x ~ A') by eauto using dec_to_sim, sim_trans, sim_sym.
  eapply validity_ty_ty in H as x_Wt.
  eapply sim_heq_same_ctx in H5; eauto.
  destruct H5.
  eapply type_hetero_to_homo in H5; eauto.
  eapply type_cast in H. 4:eapply H5.
  2,3:eauto.
  econstructor. econstructor.
  1:eauto.
  split; eauto using decoration.
Qed.

(* Lemma change_type_conv Γ' i t u A A' :
  Γ' ⊨⟨ i ⟩ t ≡ u : A →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ' ⊨⟨ i ⟩ t ≡ u : A ⇒ A'.
Proof.
  intros.
  destruct H. destruct H. destruct H. destruct H. destruct H1.
  destruct H0. destruct H2. destruct H3.
  assert (x ~ A') by eauto using dec_to_sim, sim_trans, sim_sym.
  eapply validity_conv_left in H as x_Wt. eapply validity_ty_ty in x_Wt.
  eapply sim_heq_same_ctx in H6; eauto.
  destruct H6.
  eapply type_hetero_to_homo in H6; eauto.
  eapply conv_cast in H as H'. 4:eapply conv_refl, H6.
  2,3:eapply conv_refl; eauto.
  econstructor; econstructor; econstructor.
  1:eauto.
  intuition eauto using decoration.
Qed. *)


(* Translation of derivations *)

Lemma tr_meta Γ' i j t t' A A' B B' :
  Γ' ⊨⟨ i ⟩ t : A ↦ t' : A' →
  i = j →
  A = B →
  A' = B' →
  Γ' ⊨⟨ j ⟩ t : B ↦ t' : B'.
Proof.
  intros h -> -> ->. assumption.
Qed.

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

(* TODO MOVE *)
Lemma varty_unique Γ l x A B :
  Γ ∋< l > x : A →
  Γ ∋< l > x : B →
  A = B.
Proof.
  intros hA hB.
  induction hA in B, hB |- *.
  - inversion hB. reflexivity.
  - inversion hB. subst. firstorder congruence.
Qed.

Lemma tr_var_known Γ Γ' x A A' l :
  Γ ∋< l >× x : A →
  Γ' ∋< l > x : A' →
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ l ⟩ var x : A ↦ var x : A'.
Proof.
  intros hx hx1 hc.
  eapply varty_trans in hx as hx2. 2: eassumption.
  destruct hx2 as (A'' & hx2 & hA).
  eapply varty_unique in hx1 as e. 2: eassumption.
  subst.
  split.
  { econstructor. 2: eauto. apply hc. }
  intuition constructor.
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
  Γ' ⊨⟨ Ax (Ax l) ⟩ Sort l : Sort (Ax l) ↦ Sort l : Sort (Ax l).
Proof.
  intros hc.
  split. 2: intuition constructor.
  econstructor. apply hc.
Qed.

Lemma tr_Pi i j Γ' A A' B B' :
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ',, (i, A') ⊨⟨ Ax j ⟩ B : Sort j ↦ B' : Sort j →
  Γ' ⊨⟨ Ax (Ru i j) ⟩ Pi i j A B : Sort (Ru i j) ↦ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros ihA ihB.
  destruct ihA as (? & ? & ?), ihB as (? & ? & ?).
  split. 2: intuition (constructor ; eauto).
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

Lemma tr_zero_full Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat ↦ zero : Nat.
Proof.
  intros hc.
  split. 2: intuition constructor.
  constructor. apply hc.
Qed.

Lemma tr_zero Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat.
Proof.
  intros hc.
  eexists _,_. eapply tr_zero_full. eassumption.
Qed.

Lemma tr_succ_full Γ' t t' :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat ↦ t' : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat ↦ succ t' : Nat.
Proof.
  intros iht.
  destruct iht as (? & ? & ?).
  split. 2: intuition (constructor ; eauto).
  constructor. assumption.
Qed.

Lemma tr_succ Γ' t :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat.
Proof.
  intros iht.
  eapply keep_head in iht. 2: econstructor.
  destruct iht as (? & hh & iht). inversion hh. subst.
  destruct iht as (? & ?).
  eexists _,_. eapply tr_succ_full. eassumption.
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

Lemma tr_subst_scons l Γ' Δ' σ σ' A A' u u' :
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ l ⟩ u : A <[ σ ] ↦ u' : A' <[ σ' ] →
  Γ' ⊨s (u .: σ) : Δ' ,, (l, A') ⇒ (u' .: σ').
Proof.
  intros [hs1 hs2] [hu1 hu2].
  split.
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
  2:{intros. unfold ">>". econstructor. }
  apply WellSubst_ren.
  - assumption.
  - apply hc.
Qed.

Lemma tr_subst_one Γ' i A A' u u' :
  Γ' ⊨⟨ i ⟩ u : A ↦ u' : A' →
  Γ' ⊨s u .. : Γ' ,, (i, A') ⇒ (u' ..).
Proof.
  intros hu.
  split.
  - apply subst_one. apply hu.
  - apply dec_subst_one. apply hu.
Qed.

Lemma tr_rename l Γ Γ' Δ' t t' A A' ρ :
  Δ' ⊨⟨ l ⟩ t : A ↦ t' : A' →
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨⟨ l ⟩ ρ ⋅ t : ρ ⋅ A ↦ ρ ⋅ t' : ρ ⋅ A'.
Proof.
  intros ht hc hr.
  destruct ht.
  split.
  - eapply typing_conversion_ren. all: eauto. apply hc.
  - intuition eauto using rename_dec.
Qed.

Lemma tr_rename_sort l Γ Γ' Δ' i A A' ρ :
  Δ' ⊨⟨ l ⟩ A : Sort i ↦ A' : Sort i →
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨⟨ l ⟩ ρ ⋅ A : Sort i ↦ ρ ⋅ A' : Sort i.
Proof.
  intros ht hc hr.
  eapply tr_rename in ht. 2,3: eauto.
  assumption.
Qed.

Lemma tr_substitution i Γ Γ' t t' A A' Δ' σ σ' :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ t : A ↦ t' : A' →
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ i ⟩ t <[ σ ] : A <[ σ ] ↦ t' <[ σ' ] : A' <[ σ' ].
Proof.
  intros hc ht hs.
  destruct ht as (? & ? & ?), hs as (? & ?).
  split. 2: intuition eauto using substs_decs.
  eapply typing_conversion_subst.
  - eassumption.
  - apply hc.
  - assumption.
Qed.

Corollary tr_substitution_sort i Γ Γ' A A' l Δ' σ σ' :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ A : Sort l ↦ A' : Sort l →
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ i ⟩ A <[ σ ] : Sort l ↦ A' <[ σ' ] : Sort l.
Proof.
  intros hc ht hs.
  eapply tr_substitution in hs. 2,3: eassumption.
  assumption.
Qed.

Corollary tr_substitution_one i j Γ Γ' t t' u u' A A' B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ t : A ↦ t' : A' →
  Γ' ⊨⟨ j ⟩ u : B ↦ u' : B' →
  Γ' ⊨⟨ i ⟩ t <[ u .. ] : A <[ u .. ] ↦ t' <[ u' .. ] : A' <[ u' .. ].
Proof.
  intros hc ht hu.
  eapply tr_substitution. 1,2: eassumption.
  eapply tr_subst_one. eassumption.
Qed.

Corollary tr_substitution_one_sort i j Γ Γ' A A' u u' l B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ A : Sort l ↦ A' : Sort l →
  Γ' ⊨⟨ j ⟩ u : B ↦ u' : B' →
  Γ' ⊨⟨ i ⟩ A <[ u .. ] : Sort l ↦ A' <[ u' .. ] : Sort l.
Proof.
  intros hc ht hu.
  eapply tr_substitution_one in hu. 2,3: eassumption.
  assumption.
Qed.

Lemma tr_acc Γ' n A A' R R' a a' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ,, (ty n, A'),, (ty n, S ⋅ A') ⊨⟨ Ax prop ⟩ R : Sort prop ↦ R' : Sort prop →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ Ax prop ⟩ acc (ty n) A R a : Sort prop ↦ acc (ty n) A' R' a' : Sort prop.
Proof.
  intros ihA ihR iha.
  destruct
    ihA as (? & ? & _),
    ihR as (? & ? & _),
    iha as (? & ? & _).
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eauto.
Qed.

Lemma tr_obseq Γ' n A A' a a' b b' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ ty n ⟩ b : A ↦ b' : A' →
  Γ' ⊨⟨ Ax prop ⟩ obseq (ty n) A a b : Sort prop ↦ obseq (ty n) A' a' b' : Sort prop.
Proof.
  intros ihA iha ihb.
  destruct ihA, iha, ihb.
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eassumption.
Qed.

Lemma tr_obsrefl Γ' n A A' a a' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ prop ⟩ obsrefl (ty n) A a : obseq (ty n) A a a ↦ obsrefl (ty n) A' a' : obseq (ty n) A' a' a'.
Proof.
  intros ihA iha.
  destruct ihA, iha.
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eassumption.
Qed.

Lemma tr_conv Γ' l t A B : 
  Γ' ⊨⟨ l ⟩ t : A ->
  Γ' ⊨⟨ Ax l ⟩ A = B : Sort l ->
  Γ' ⊨⟨ l ⟩ t : B.
Proof.
  intros.
  destruct H. destruct H. destruct H. destruct H1. rename x0 into t'. rename x into A'.
  destruct H0 as (A'' & B' & sort & e & h).
  destruct h. destruct H3. destruct H4. destruct H5. destruct H6. 
  assert (A' ~ A'') by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H8; eauto using validity_ty_ty.
  destruct H8.
  eapply type_heq_trans in H7. 5:eauto. all:eauto using validity_ty_ty.
  assert (sort ~ Sort l) by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H9; eauto using validity_ty_ty.
  destruct H9. eapply type_hetero_to_homo in H9; eauto using validity_ty_ty.
  eapply type_heq_cast in H6 as H6'. 4:eauto. all:eauto using validity_ty_ty.
  eapply type_heq_trans in H6'. 5:eauto.  all:eauto using validity_ty_ty, type_cast.
  eapply type_hetero_to_homo in H6'; eauto using validity_ty_ty, type_cast.
  eapply type_cast in H. 4:eauto. all:eauto using validity_ty_ty, type_cast.
  econstructor. econstructor. econstructor. 1: eapply H.
  all: intuition eauto using decoration.
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
      Γ' ⊨⟨ l ⟩ u = v : A
  ).
Proof.
  apply Typing.typing_mutind.

  (* solves SProp equality cases *)
  all : try solve [ intros; exists Nat; exists Nat; exists Nat; exists Nat; exists Nat; econstructor ].

  (* Typing rules *)

  - intros * ? hx ? hc.
    eapply tr_var. all: eassumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_Sort. eassumption.
  - intros * ? e ? ih ? hc.
    eapply tr_assm_sig in e as e'. destruct e' as (A' & e' & ? & ?).
    eexists _, (assm _). split.
    { econstructor. 2,3: eassumption. apply hc. }
    intuition constructor.
  - intros * ? ihA ? ihB ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    eexists _,_. eapply tr_Pi. all: eassumption.
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
    eapply change_type in iht. 2:{ eapply tr_Pi. all: eassumption. }
    destruct iht as (t' & iht).
    specialize ihu with (1 := hc).
    eapply change_type in ihu. 2: eassumption.
    destruct ihu as (u' & ihu).
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
  - intros * ?? hc. eapply tr_zero. eassumption.
  - intros * ? iht ? hc.
    specialize iht with (1 := hc).
    eapply tr_succ. assumption.
  - intros * ? ihP ? ihz ? ihs ? iht ? hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Nat. eassumption. }
    destruct iht as (?t' & iht).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _),
      iht as (? & ? & _).
    eexists _,_. split. 2: split. 2: constructor ; eauto.
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: assumption.
  - intros * ? ihA ? ihR ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct ihR as [R' ihR], iha as [a' iha].
    eexists _,_.
    eapply tr_acc. all: eassumption.
  - intros * ? ihA ? ihR ? iha. cbn zeta. intros ? ihp ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    eapply tr_ctx_cons in hca as hcar.
    2:{
      eapply tr_substitution_sort. 1,2: eauto.
      eapply tr_subst_scons with (A := S ⋅ A).
      1: eapply tr_subst_scons with (A := A).
      - eapply tr_subst_ren. 1: eassumption.
        apply WellRen_S.
      - rasimpl. eapply tr_var_known. 3: eassumption.
        + eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        + eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      - rasimpl. eapply tr_rename. 1,2: eassumption.
        apply WellRen_S.
    }
    eapply tr_ctx_cons with (A := (S >> S) ⋅ A) in hcar as hcara.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply WellRen_weak. apply WellRen_S.
    }
    specialize ihp with (1 := hc).
    eapply change_type in ihp.
    2:{
      eapply tr_meta.
      { eapply tr_Pi. 1: eassumption.
        eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_substitution_sort. 1,2: eauto.
            eapply tr_subst_scons with (A := S ⋅ A).
            + eapply tr_subst_scons with (A := A).
              * eapply tr_subst_ren. 1: eassumption.
                apply WellRen_S.
              * {
                eapply tr_var_known. 3: eassumption.
                - eapply BasicMetaTheory.varty_meta.
                  { repeat econstructor. }
                  rasimpl. reflexivity.
                - eapply varty_meta.
                  { repeat econstructor. }
                  rasimpl. reflexivity.
              }
            + rasimpl. eapply tr_rename. 1,2: eauto.
              apply WellRen_S.
          - eapply tr_acc.
            + eapply tr_rename_sort. 1,2: eassumption.
              apply WellRen_weak. apply WellRen_S.
            + eapply tr_rename_sort. 1: eauto.
              * eapply tr_ctx_cons. 1: eassumption.
                rasimpl. eapply tr_rename_sort. 1,2: eassumption.
                do 2 apply WellRen_weak. apply WellRen_S.
              * apply WellRen_up. 2:{ rasimpl. reflexivity. }
                apply WellRen_up. 2: reflexivity.
                apply WellRen_weak. apply WellRen_S.
            + eapply tr_var_known. 3: eassumption.
              * eapply BasicMetaTheory.varty_meta.
                { repeat econstructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat econstructor. }
                rasimpl. reflexivity.
        }
        all: reflexivity.
      }
      all: reflexivity.
    }
    destruct ihp as [p' ihp].
    destruct ihA, ihR, iha, ihp.
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihR ? iha ? ihp ? ihb ? ihr ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihp with (1 := hc).
    eapply change_type in ihp. 2:{ eapply tr_acc. all: eauto. }
    destruct ihp as [p' ihp].
    specialize ihb with (1 := hc).
    eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    specialize ihr with (1 := hc).
    eapply change_type in ihr.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply tr_subst_scons with (A := S ⋅ A).
      - eapply tr_subst_one. eassumption.
      - rasimpl. eassumption.
    }
    destruct ihr as [r' ihr].
    destruct ihA, ihR, iha, ihp, ihb, ihr.
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros ?? l * ? ihA ? ihR ? ihP. cbn zeta. intros ? ihp ? iha ? ihq ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    lazymatch type of ihp with
    | ∀ G', tr_ctx ?G G' → _ => eassert (hcap : tr_ctx G _)
    end.
    { eapply tr_ctx_cons. 1: eassumption.
      eapply tr_Pi.
      - eapply tr_rename_sort. 1,2: eassumption.
        apply WellRen_S.
      - eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_rename_sort. 1,2: eassumption.
            apply well_rcons_alt. 1: apply well_rcons_alt.
            + apply WellRen_weak. apply WellRen_S.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
          - eapply tr_rename_sort. 1: eassumption.
            + eapply tr_ctx_cons. 1: eassumption.
              eapply tr_rename_sort. 1,2: eassumption.
              apply well_rcons_alt. 1: apply well_rcons_alt.
              * apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
            + apply well_rcons_alt.
              * do 2 apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
        }
        all: destruct l ; reflexivity.
    }
    specialize ihp with (1 := hcap).
    eapply change_type in ihp.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply well_rcons_alt.
      - apply WellRen_weak. apply WellRen_S.
      - eapply varty_meta.
        { repeat constructor. }
        rasimpl. reflexivity.
    }
    destruct ihp as [p' ihp].
    specialize ihq with (1 := hc).
    eapply change_type in ihq. 2:{ eapply tr_acc. all: eauto. }
    destruct ihq as [q' ihq].
    destruct ihA, ihR, ihP, iha, ihp, ihq.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: intuition assumption.
  - intros * ? ihA ? iha ? ihb ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihb with (1 := hc). eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    eexists _,_. eapply tr_obseq. all: eassumption.
  - intros * ? ihA ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    eexists _,_. eapply tr_obsrefl. all: eassumption.
  - intros * ? ihA ? iha ? ihP ? ihp ? ihb ? ihe ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihb with (1 := hc). eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize ihp with (1 := hc).
    eapply change_type in ihp.
    2:{ eapply tr_substitution_one_sort. all: eassumption. }
    destruct ihp as [p' ihp].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{ eapply tr_obseq. all: eassumption. }
    destruct ihe as [e' ihe].
    destruct ihA, iha, ihP, ihp, ihb, ihe.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: intuition assumption.
  - intros * ? ihA ? ihB ? ihe ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize ihB with (1 := hc). eapply keep_sort in ihB.
    destruct ihB as [B' ihB].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq. 2,3: eassumption.
      eapply tr_Sort. eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    destruct ihA, ihB, ihe, iha.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition eauto.
  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? hc.
    specialize ihA1 with (1 := hc). eapply keep_sort in ihA1.
    destruct ihA1 as [A1' ihA1].
    eapply tr_ctx_cons in hc as hca1. 2: eassumption.
    specialize ihB1 with (1 := hca1). eapply keep_sort in ihB1.
    destruct ihB1 as [B1' ihB1].
    specialize ihA2 with (1 := hc). eapply keep_sort in ihA2.
    destruct ihA2 as [A2' ihA2].
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2). eapply keep_sort in ihB2.
    destruct ihB2 as [B2' ihB2].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq.
      - eapply tr_Sort. eassumption.
      - eapply tr_Pi. all: eassumption.
      - eapply tr_Pi. all: eassumption.
    }
    destruct ihe as [e' ihe].
    destruct ihA1, ihB1, ihA2, ihB2, ihe.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition (constructor ; eauto).
  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? iha2. cbn zeta. intros ? hc.
    specialize ihA1 with (1 := hc). eapply keep_sort in ihA1.
    destruct ihA1 as [A1' ihA1].
    eapply tr_ctx_cons in hc as hca1. 2: eassumption.
    specialize ihB1 with (1 := hca1). eapply keep_sort in ihB1.
    destruct ihB1 as [B1' ihB1].
    specialize ihA2 with (1 := hc). eapply keep_sort in ihA2.
    destruct ihA2 as [A2' ihA2].
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2). eapply keep_sort in ihB2.
    destruct ihB2 as [B2' ihB2].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq.
      - eapply tr_Sort. eassumption.
      - eapply tr_Pi. all: eassumption.
      - eapply tr_Pi. all: eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha2 with (1 := hc). eapply change_type in iha2. 2: eassumption.
    destruct iha2 as [a2' iha2].
    destruct ihA1, ihB1, ihA2, ihB2, ihe, iha2.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + constructor.
      * constructor.
      * eapply substs_decs_one. all: intuition (repeat constructor ; eauto).
      * eapply substs_decs_one. all: intuition eauto.
  - intros * ? iht ? ihAB ? hc.
    eapply iht in hc as tWt.
    eapply ihAB in hc as AconvB.
    eapply tr_conv; eauto.

  (* Conversion rules *)

  - intros * ??? hc. admit.

  - admit.
  - intros. admit.
  - intros. 
    assert (⊢ Γ') by (destruct H2; eauto).
    eapply H0 in H2 as h0. eapply tr_conv_change_ty' in h0.
    2:econstructor.
    2:eauto using typing.
    eapply ty_conv_homo_destruct in h0 as (A0 & A'0 & e' & h1 & h2 & h3).

    assert (tr_ctx (Γ,, (i, A)) (Γ',, (i, A0))).
    1:eapply tr_ctx_cons. 1,2:eauto.

    eapply H1 in H4 as h1'. eapply tr_conv_change_ty' in h1'.
    2:econstructor.
    2:eauto using typing, ctx_typing;admit.
    eapply ty_conv_homo_destruct in h1' as (B0 & B'0 & e'' & k1 & k2 & k3). 
    destruct h1. destruct h2. destruct k1. destruct k2.
    assert (exists e', Γ' ⊢< prop > e' : obseq (Ax i) (Sort i) A'0 A0).
    1:{ eexists. eapply type_hetero_to_homo in h3; eauto. eapply type_obseq_sym; eauto. }
    destruct H13.
    (* eapply type_hetero_to_homo in h3 as temp; eauto. *)
    (* eapply type_obseq_sym in temp. *)
    (* eapply decombine_subst in temp; eauto. destruct temp. *)
    eapply subst_ty in H11. 3:eapply cast_subst. 5:eauto.
    all:eauto using ctx_typing, validity_ty_ctx.
    rasimpl in H11.

    eapply type_heq_pi in h3 as h3'.
    2,3:eauto. 2:eapply H9. 2:eapply H11.
    2:admit.
    eapply tr_eq_conclude. 
    7:eapply h3'.
    all:intuition eauto 8 using typing, decoration, cast_subst_refines. 
    
    Unshelve. exact Nat.
    
  - intros.
   (* eapply eqtrans_hetero_to_homo. *)
    assert (⊢ Γ') by (destruct H3; eauto).
    eapply H0 in H3 as h0. eapply tr_conv_change_ty' in h0.
    2:econstructor.
    2:eauto using typing.
    eapply ty_conv_homo_destruct in h0 as (A0 & A'0 & e' & h1 & h2 & h3).

    assert (tr_ctx (Γ,, (i, A)) (Γ',, (i, A0))).
    1:eapply tr_ctx_cons. 1,2:eauto.

    eapply H1 in H5 as h1'. eapply tr_conv_change_ty' in h1'.
    2:econstructor.
    2:eauto using typing, ctx_typing;admit.
    eapply ty_conv_homo_destruct in h1' as (B0 & B'0 & e'' & k1 & k2 & k3).

    eapply H2 in H5 as h2'. 
    
    destruct h1, h2, k1, k2.
    eapply eqtrans_homo_to_hetero , tr_conv_change_ty in h2'.
    4:eapply type_hetero_to_homo. 4:eapply H10. 4:eapply H12.
    4:eauto. all:intuition eauto.
    destruct h2' as (t_ & t'_ & e_ & h).
    destruct j. 2:admit.
    unfold eqtrans in h; intuition eauto.
    assert (exists e', Γ' ⊢< prop > e' : obseq (Ax i) (Sort i) A'0 A0).
    1:{ eexists. eapply type_hetero_to_homo in h3; eauto. eapply type_obseq_sym; eauto. }
    destruct H23.
    eapply subst_ty in H12. 3:eapply cast_subst. 5:eauto.
    all:eauto using ctx_typing, validity_ty_ctx.
    eapply subst_ty in H22. 3:eapply cast_subst. 5:eauto.
    all:eauto using ctx_typing, validity_ty_ctx.
    rasimpl in H22.


    eapply type_heq_lam in h3 as h3'.
    2:eapply H21. 2:eapply H22.
    2:admit.

    eapply tr_eq_conclude. 7:eapply h3'.
    all:eauto using typing. 
    all:econstructor;eauto.
    all:eapply cast_subst_refines; eauto. Unshelve. all:exact Nat.

  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros. admit.
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
  - intros * ? ihP ? ihz ? ihs ?  hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _). 
      admit.
    (* destruct l; eexists _,_,_,_,_. 
    + econstructor. 2:econstructor. 3:econstructor. 4:econstructor. 5:econstructor. 6:econstructor.
      3:econstructor. all:eauto. 3:econstructor.
      3:econstructor; eauto using typing, validity_ty_ctx.
      1,2:eapply substs_decs_one; eauto using decoration.
      eapply type_conv.
      1:eapply type_heq_refl.
      3:eapply conv_heq.
      3,4,6:eapply conv_refl.
      6:eapply conv_sym, conv_rec_zero; eauto.
      all:eauto.
      all:eapply subst_ty; eauto using subst_one, typing, validity_ty_ctx.
    + econstructor. Unshelve. all:exact Nat.   *)
  - intros * ? ihP ? ihz ? ihs ? iht ? hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Nat. eassumption. }
    destruct iht as (?t' & iht).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _),
      iht as (? & ? & _).
    assert (Γ' ⊢< l > rec l P' z' s' (succ t') ≡ s' <[ rec l P' z' s' t' .: t'..] : P' <[ (succ t')..]) by eauto using conversion.
    admit.
    (* destruct l; eexists _,_,_,_,_. 
    + econstructor. 2:econstructor. 3:econstructor. 4:econstructor. 5:econstructor. 6:econstructor.
      3:econstructor. 1,2:eapply substs_decs_one.
      1-8:eauto. 1-3:econstructor; eauto.
      1:eapply substs_decs_two. 2:econstructor. all:eauto.
      1,2:eauto using validity_conv_left, validity_conv_right.
      eapply type_conv.
      1:eapply type_heq_refl.
      3:eapply conv_heq.
      3,4,6:eapply conv_refl.
      all: eauto using validity_conv_left, validity_conv_right, conv_sym.
      all:eapply subst_ty; eauto using subst_one, typing, validity_ty_ctx.
    + econstructor. Unshelve. all:exact Nat. *)
  - intros. admit.
  - admit.
  - admit.
Admitted.

Lemma conservativity_ty A A0 :
  A ⊏ A0 ->
  ∙ ⊢< Ax prop > A : Sort prop -> 
  ∙ ⊢< Ax prop > A0 : Sort prop -> 
  exists e, ∙ ⊢< prop > e : obseq (Ax prop) (Sort prop) A0 A.
Proof.
  intros Hinc Hty Hty0.
  unshelve epose proof (H := sim_heq 0 ∙ ∙ A A0 (Sort prop) (Sort prop) _ _ Hty Hty0).
  1: econstructor.
  1: now eapply dec_to_sim. 
  assert (renL ⋅ A = A). 
  { apply closed_ren. eapply typing_closed; eauto. }
  assert (renR ⋅ A0 = A0).
  { apply closed_ren. eapply typing_closed; eauto. }
  destruct H as [e H].
  rewrite H0, H1 in H. cbn in H.
  eapply type_hetero_to_homo in H; eauto.
  eapply type_obseq_sym in H.
  eexists; eauto.
Qed.

Lemma conservativity e P :
  ∙ ⊢< ty 0 > P : Sort prop  ->
  ∙ ⊢< prop >× e : P ->
  exists e', ∙ ⊢< prop > e' : P.
Proof.
  intros Hty HP.
  eapply typing_conversion_trans in HP.
  2: repeat econstructor.
  destruct HP as [P' [e' [HP [Hincl Hincl']]]].
  assert (HP' : ∙ ⊢< Ax prop > P' : Sort prop) by now eapply validity_ty_ty in HP.
  destruct (conservativity_ty _ _ Hincl' Hty HP') as [eqp Heq].
  eexists (cast _ P' P eqp e').
  eapply type_cast; eauto.
Qed.  

Lemma type_mk_Nat k : ∙ ⊢< ty 0 > mk_Nat k : Nat.
Proof.
  induction k; simpl.
  - eapply type_zero; econstructor.
  - eapply type_succ; eauto. 
Qed. 

Lemma prop_canonicity n : 
  ∙ ⊢< ty 0 > n : Nat ->
  ∙ ⊢< ty 0 >× n : Nat ->
  exists k e, ∙ ⊢< prop > e : obseq (ty 0) Nat n (mk_Nat k).
Proof.
  intros H H'.
  eapply canonicity_conv in H'.
  destruct H' as [k H']. exists k.  
  eassert (∙ ⊢< _ >× _ : obseq (ty 0) Nat n (mk_Nat k)) as Hcan.
  1:eapply Typing.type_conv.
  1:eapply Typing.type_obsrefl.
  3:econstructor.
  5:eauto.
  all:eauto using Typing.typing, BasicMetaTheory.validity_conv_left, BasicMetaTheory.conv_refl, BasicMetaTheory.validity_ty_ctx.
  eapply conservativity in Hcan; eauto.
  eapply type_obseq; eauto.
  1: eapply type_nat; econstructor.
  eapply type_mk_Nat.
Qed.
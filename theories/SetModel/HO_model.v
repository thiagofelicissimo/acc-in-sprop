From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory Reduction. 
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.

Open Scope subst_scope.

Definition to_ZF_level (l : level) : nat :=
  match l with
  | ty n => n
  | prop => 0
  end.

Scheme typing_mutS := Induction for typing Sort Prop
with ctx_typing_mutS := Induction for ctx_typing Sort Prop
with conversion_mutS := Induction for conversion Sort Prop.
Combined Scheme ctx_typing_conversion_mutindS from typing_mutS, ctx_typing_mutS, conversion_mutS.

(* Interprétation comme des fonctions partielles
   - [_] : ctx -> ZFSet
   - [_ ⊢ _] : level -> tm -> ZFSet -> ZFSet *)

Inductive interp_ctx : forall (Γ : ctx), ZFSet -> Prop :=

| interp_empty : interp_ctx ∙ ⋆

| interp_cons_rel : forall Γ l A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty l)) A iA
                    -> interp_ctx (Γ ,, (ty l , A)) (ctxExt l iΓ (fun γ => 𝕌el l (iA γ)))

| interp_cons_irr : forall Γ A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA
                    -> interp_ctx (Γ ,, (BasicAST.prop , A)) (ctxExt 0 iΓ iA)

with nth_proj : forall (Γ : ctx) (l : level) (x : nat), (ZFSet -> ZFSet) -> Prop :=

| here_rel : forall Γ l A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty l)) A iA
             -> nth_proj (Γ ,, (ty l , A)) (ty l) 0 (setSndSigma l iΓ (fun γ => 𝕌el l (iA γ)))

| there_rel : forall Γ l lA A x iΓ iA ix, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty lA)) A iA -> nth_proj Γ l x ix
              -> nth_proj (Γ ,, (ty lA , A)) l (S x) (fun γa => ix (setFstSigma lA iΓ (fun γ => 𝕌el lA (iA γ)) γa))

| here_irr : forall Γ A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA
             -> nth_proj (Γ ,, (BasicAST.prop , A)) BasicAST.prop 0 (setSndSigma 0 iΓ iA)

| there_irr : forall Γ l A x iΓ iA ix, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA -> nth_proj Γ l x ix
              -> nth_proj (Γ ,, (BasicAST.prop , A)) l (S x) (fun γa => ix (setFstSigma 0 iΓ iA γa))

with interp_tm : forall (Γ : ctx) (l : level) (A : term), (ZFSet -> ZFSet) -> Prop :=

| interp_var : forall Γ l x ix, nth_proj Γ l x ix
               -> interp_tm Γ l (var x) ix

| interp_type : forall Γ l, 
                interp_tm Γ (Ax (Ax (ty l))) (Sort (ty l)) (univTy_HO l)

| interp_prop : forall Γ, 
                interp_tm Γ (ty 1) (Sort BasicAST.prop) propTy_HO

| interp_pi_rr : forall Γ lA lB A B iA iB, interp_tm Γ (Ax (ty lA)) A iA
                 -> interp_tm (Γ ,, (ty lA , A)) (Ax (ty lB)) B iB
                 -> interp_tm Γ (Ax (Ru (ty lA) (ty lB))) (Pi (ty lA) (ty lB) A B) 
                              (piTy_HO lA lB iA iB)

| interp_pi_ir : forall Γ lB A B iA iB, interp_tm Γ (Ax BasicAST.prop) A iA
                 -> interp_tm (Γ ,, (BasicAST.prop , A)) (Ax (ty lB)) B iB
                 -> interp_tm Γ (Ax (ty lB)) (Pi BasicAST.prop (ty lB) A B)
                              (piTy_HO 0 lB (boxTy_HO iA) iB)

| interp_pi_ri : forall Γ lA A B iA iB, interp_tm Γ (Ax (ty lA)) A iA
                 -> interp_tm (Γ ,, (ty lA , A)) (Ax BasicAST.prop) B iB
                 -> interp_tm Γ (Ax BasicAST.prop) (Pi (ty lA) BasicAST.prop A B) 
                              (forallTy_HO lA iA iB)

| interp_pi_ii : forall Γ A B iA iB, interp_tm Γ (Ax BasicAST.prop) A iA
                 -> interp_tm (Γ ,, (BasicAST.prop , A)) (Ax BasicAST.prop) B iB
                 -> interp_tm Γ (Ax BasicAST.prop) (Pi BasicAST.prop BasicAST.prop A B)
                              (forallTy_HO 0 (boxTy_HO iA) iB)

| interp_lam_rr : forall Γ lA lB A B t iA it, interp_tm Γ (Ax (ty lA)) A iA
                  -> interp_tm (Γ ,, (ty lA , A)) (ty lB) t it
                  -> interp_tm Γ (Ru (ty lA) (ty lB)) (lam (ty lA) (ty lB) A B t) (lamTm_HO lA lB iA it)

| interp_lam_ir : forall Γ lB A B t iA it, interp_tm Γ (Ax BasicAST.prop) A iA
                  -> interp_tm (Γ ,, (BasicAST.prop , A)) BasicAST.prop t it
                  -> interp_tm Γ (ty lB) (lam BasicAST.prop (ty lB) A B t) (lamTm_HO 0 lB (boxTy_HO iA) it)

| interp_app_rr : forall Γ lA lB A B t u iA it iu, interp_tm Γ (Ax (ty lA)) A iA
                  -> interp_tm Γ (Ru (ty lA) (ty lB)) t it
                  -> interp_tm Γ (ty lA) u iu
                  -> interp_tm Γ (ty lB) (app (ty lA) (ty lB) A B t u) (appTm_HO lA lB iA it iu)

| interp_app_ir : forall Γ lB A B t u iA it iu, interp_tm Γ (Ax BasicAST.prop) A iA
                  -> interp_tm Γ (ty lB) t it
                  -> interp_tm Γ BasicAST.prop u iu
                  -> interp_tm Γ (ty lB) (app BasicAST.prop (ty lB) A B t u) (appTm_HO 0 lB (boxTy_HO iA) it iu).

(* | interp_nat : forall Γ, *)
(*                interp_tm Γ (ty 1) Nat natTy_HO *)

(* | interp_zero : forall Γ, *)
(*                 interp_tm Γ (ty 0) zero zeroTm_HO *)

(* | interp_succ : forall Γ t it, interp_tm Γ (ty 0) t it *)
(*                 -> interp_tm Γ (ty 0) (succ t) (sucTm_HO it) *)

(* | interp_natrec : *)

(* | interp_acc : *)

(* | interp_accelim : *)

(* | interp_obseq : *)

(* | interp_cast : *)



(* Interprétation des renommages et des substitutions *)


(* Fonction partielle (?) *)


(* Lemme fondamental *)

Inductive model_ctx (Γ : ctx) : Prop :=
| mkModelCtx (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ).

Inductive model_typing_rel (Γ : ctx) (l : nat) (t A : term) : Prop :=
| mkModelTypingRel (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax (ty l)) A iA)
    (it : ZFSet -> ZFSet)
    (ft : interp_tm Γ (ty l) t it)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l)
    (vt : ∀ γ ∈ iΓ, it γ ∈ 𝕌el l (iA γ)).

Inductive model_typing_irr (Γ : ctx) (t A : term) : Prop :=
| mkModelTypingIrr (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax BasicAST.prop) A iA)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω)
    (vt : ∀ γ ∈ iΓ, ∅ ∈ iA γ).

Definition model_typing (Γ : ctx) (l : level) (t A : term) : Prop :=
  match l with
  | BasicAST.prop => model_typing_irr Γ t A
  | ty l => model_typing_rel Γ l t A
  end.

Inductive model_conv_rel (Γ : ctx) (l : nat) (t u A : term) : Prop :=
| mkModelConvRel (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax (ty l)) A iA)
    (it : ZFSet -> ZFSet)
    (ft : interp_tm Γ (ty l) t it)
    (iu : ZFSet -> ZFSet)
    (fu : interp_tm Γ (ty l) u iu)
    (* (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l) *)
    (* (vt : ∀ γ ∈ iΓ, it γ ∈ 𝕌el l (iA γ)) *)
    (vu : ∀ γ ∈ iΓ, it γ ≡ iu γ).
  
Inductive model_conv_irr (Γ : ctx) (t u A : term) : Prop := True.
(* | mkModelConvIrr (iΓ : ZFSet) *)
(*     (fΓ : interp_ctx Γ iΓ) *)
(*     (iA : ZFSet -> ZFSet) *)
(*     (fA : interp_tm Γ (Ax BasicAST.prop) A iA) *)
(*     (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω) *)
(*     (vt : ∀ γ ∈ iΓ, ∅ ∈ iA γ). *)

Definition model_conv (Γ : ctx) (l : level) (t u A : term) : Prop :=
  match l with
  | BasicAST.prop => model_conv_irr Γ t u A
  | ty l => model_conv_rel Γ l t u A
  end.

(* We assume that the extra assumptions are validated by the model *)
Axiom model_assm : forall c A iA, nth_error assm_sig c = Some A
                                  -> interp_tm ∙ (ty 0) A iA
                                  -> ∅ ∈ iA ∅.

Theorem model : (forall Γ l t A, Γ ⊢< l > t : A -> model_typing Γ l t A) 
              /\ (forall Γ, ⊢ Γ -> model_ctx Γ)
              /\ (forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> model_conv Γ l t u A).
Proof.
  apply ctx_typing_conversion_mutindS.
  - admit.
  - intros Γ l tΓ [ iΓ fΓ ]. destruct l as [ l | ].
    + econstructor.
      * exact fΓ.
      * apply interp_type.
      * apply interp_type.
      * apply univTy_HO_typing.
      * apply univTy_HO_typing'.
    + econstructor.
      * exact fΓ.
      * apply interp_type.
      * apply interp_prop.
      * apply univTy_HO_typing.
      * apply propTy_HO_typing'.
  - intros Γ c A tΓ [ iΓ fΓ ] Hc tA [ iΓ' fΓ' iΩ fΩ iA fA vΩ vA ]. econstructor.
    * exact fΓ.
    * assert (interp_tm Γ (Ax BasicAST.prop) A (fun _ => iA ∅)) as H. admit. exact H. (* weakening of interpretation *)
    * intros γ Hγ. cbn. admit.  (* some massaging is in order here *)
    * intros γ Hγ. now apply (model_assm c A).
  - intros Γ i j A B tA [ iΓ fΓ iS fS iA fA vS vA ] tB [ iΓ' fΓ' iT fT iB fB vT vB ].
    destruct i as [ i | ] ; destruct j as [ j | ] ; cbn in *.
    + econstructor.
      * exact fΓ.
      * apply interp_type.
      * apply interp_pi_rr. exact fA. exact fB.
      * apply univTy_HO_typing.
      *

Admitted.

Corollary consistency : forall t , ∙ ⊢< BasicAST.prop > t : Pi (ty 0) BasicAST.prop (Sort BasicAST.prop) (var 0) -> False.
Proof.
  (* We interpret the judgment in our ZF model *)
  intros t H. apply model in H. destruct H as [ iΓ fΓ iA fA _ vt ].
  (* We unfold the interpretation function using [inversion] *)
  inversion fΓ. destruct H0. clear fΓ.
  inversion fA. symmetry in H1. destruct H1. symmetry in H. destruct H.
  symmetry in H0. destruct H0. symmetry in H2. destruct H2. destruct H4. clear fA.
  inversion H3. symmetry in H. destruct H. destruct H2. clear H3.
  inversion H5. symmetry in H0. destruct H0. symmetry in H1. destruct H1.
  symmetry in H. destruct H. destruct H3. clear H5.
  inversion H2. symmetry in H. destruct H. symmetry in H0. destruct H0.
  symmetry in H3. destruct H3. destruct H5. clear H2.
  inversion H1. destruct H0. clear H1.
  inversion H4. symmetry in H. destruct H. destruct H2. clear H4.
  (* We derive a contradiction *)
  assert (∅ ∈ ⋆) as Hγ. { now apply inSetSingl. }
  specialize (vt _ Hγ). clear Hγ. apply prop_true_if in vt.
  assert (∅ ∈ 𝕌el 0 (propTy_HO ∅)) as Hp.
  { refine (transpS (fun X => ∅ ∈ X) (sym el_propTy) _).
    apply ZFinpower. intros x Hx. apply ZFinempty in Hx. destruct Hx. }
  specialize (vt _ Hp). assert (∅ ∈ ∅).
  { refine (transpS (fun X => ∅ ∈ X) _ vt). apply setSigmaβ2.
    - intros γ Hγ. apply 𝕌el_typing. now apply (propTy_HO_typing (Γ := ⋆)).
    - now apply inSetSingl.
    - exact Hp. }
  apply ZFinempty in H. destruct H.
Qed.

Print Assumptions consistency.

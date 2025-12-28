From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp model_def model_univ model_pi.

Open Scope subst_scope.

Scheme typing_mutS := Induction for typing Sort Prop
with ctx_typing_mutS := Induction for ctx_typing Sort Prop
with conversion_mutS := Induction for conversion Sort Prop.
Combined Scheme ctx_typing_conversion_mutindS from typing_mutS, ctx_typing_mutS, conversion_mutS.

(* Assumptions are validated by the model *)

Lemma model_assm (Γ : ctx) (c : nat) (A : term) (tΓ : ⊢ Γ) (mΓ : model_ctx Γ) (Hc : nth_error assm_sig c = Some A)
  (tA : ∙ ⊢< Ax BasicAST.prop > A : Sort BasicAST.prop) (mA : model_typing ∙ (Ax BasicAST.prop) A (Sort BasicAST.prop)) :
  model_typing Γ BasicAST.prop (assm c) A.
Proof.
  destruct mΓ as [ iΓ fΓ ]. destruct mA as [ iΓ' fΓ' iΩ fΩ iA fA vΩ vA ]. econstructor.
  * exact fΓ.
  * assert (interp_tm Γ (Ax BasicAST.prop) A (fun _ => iA ∅)) as H. admit. exact H. (* weakening of interpretation *)
  * intros γ Hγ. cbn. inversion fΓ'. subst. inversion fΩ. subst.
    assert (∅ ∈ ⋆) as Hγ'. { now apply inSetSingl. } 
    refine (transpS (fun X => iA ∅ ∈ X) _ (vA _ Hγ')). now apply el_propTy.
  * intros γ Hγ. now apply (valid_assm c A).
Admitted.

(* Fundamental lemma *)

Theorem model : (forall Γ l t A, Γ ⊢< l > t : A -> model_typing Γ l t A) 
              /\ (forall Γ, ⊢ Γ -> model_ctx Γ)
              /\ (forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> model_conv Γ l t u A).
Proof.
  apply ctx_typing_conversion_mutindS.
  - admit.  (* Variables *)
  - apply model_univ.
  - apply model_assm.
  - apply model_pi.
  - apply model_lambda.
  - apply model_app.
Admitted.

(* Corollary : the theory is consistent *)

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

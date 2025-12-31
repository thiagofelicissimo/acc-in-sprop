From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp model_def model_univ model_pi model_nat model_acc model_obseq.

Open Scope subst_scope.

Scheme typing_mutS := Induction for typing Sort Prop
with ctx_typing_mutS := Induction for ctx_typing Sort Prop
with conversion_mutS := Induction for conversion Sort Prop.
Combined Scheme ctx_typing_conversion_mutindS from typing_mutS, ctx_typing_mutS, conversion_mutS.

(* Assumptions are validated by the model *)
Axiom valid_assm : forall c A iA, nth_error assm_sig c = Some A
                                  -> interp_tm ∙ (ty 0) A iA
                                  -> ∅ ∈ iA ∅.

Lemma model_assm (Γ : ctx) (c : nat) (A : term) (tΓ : ⊢ Γ) (mΓ : model_ctx Γ) (Hc : nth_error assm_sig c = Some A)
  (tA : ∙ ⊢< Ax prop > A : Sort prop) (mA : model_typing ∙ (Ax prop) A (Sort prop)) :
  model_typing Γ prop (assm c) A.
Proof.
  destruct mΓ as [ iΓ fΓ ]. destruct mA as [ iΓ' fΓ' iΩ fΩ iA fA vΩ vA ]. econstructor.
  * exact fΓ.
  * assert (interp_tm Γ (Ax prop) A (fun _ => iA ∅)) as H. admit. exact H. (* weakening of interpretation *)
  * intros γ Hγ. cbn. inversion fΓ'. subst. inversion fΩ. subst.
    assert (∅ ∈ ⋆) as Hγ'. { now apply inSetSingl. } 
    refine (transpS (fun X => iA ∅ ∈ X) _ (vA _ Hγ')). now apply el_propTy.
  * intros γ Hγ. now apply (valid_assm c A).
Admitted.

(* Conversion *)

Lemma model_conversion (Γ : ctx) (l : level) (A B t : term)
  (ta : Γ ⊢< l > t : A) (ma : model_typing Γ l t A)
  (tAB : Γ ⊢< Ax l > A ≡ B : Sort l) (mAB : model_conv Γ (Ax l) A B (Sort l)) :
  model_typing Γ l t B.
Proof.
  apply of_model_conv_univ in mAB. destruct l as [ l | ].
  - destruct mAB as [ iΓ fΓ iA fA iB fB vA vB ].
    destruct ma as [ iΓ' fΓ' iA' fA' ia fa _ va ].
    destruct (functional_ctx Γ fΓ fΓ') ; clear fΓ'. destruct (functional_tm A fA fA') ; clear fA'.
    econstructor.
    + exact fΓ.
    + exact fB.
    + exact fa.
    + intros γ Hγ. exact (transpS (fun X => X ∈ 𝕌 l) (vB γ Hγ) (vA γ Hγ)).
    + intros γ Hγ. exact (transpS (fun X => ia γ ∈ 𝕌el l X) (vB γ Hγ) (va γ Hγ)).
  - destruct mAB as [ iΓ fΓ iA fA iB fB vA vB ].
    destruct ma as [ iΓ' fΓ' iA' fA' _ va ].
    destruct (functional_ctx Γ fΓ fΓ') ; clear fΓ'. destruct (functional_tm A fA fA') ; clear fA'.
    econstructor.
    + exact fΓ.
    + exact fB.
    + intros γ Hγ. exact (transpS (fun X => X ∈ Ω) (vB γ Hγ) (vA γ Hγ)).
    + intros γ Hγ. exact (transpS (fun X => ∅ ∈ X) (vB γ Hγ) (va γ Hγ)).
Qed.

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
  - apply model_nat.
  - apply model_zero.
  - apply model_suc.
  - apply model_natrec.
  - apply model_acc. 
  - apply model_accin.
  - apply model_accinv.
  - apply model_accelim.
  - apply model_obseq.
  - apply model_obsrefl.
  - apply model_J.
  - apply model_cast.
  - apply model_injpi1.
  - apply model_injpi2.
  - apply model_conversion.
  - econstructor. apply interp_empty.
  - admit. (* Context extension *)
  - admit. (* Variable congruence *)
  - apply model_univ_cong.
  - 
Admitted.

(* Corollary : the theory is consistent *)

Corollary consistency : forall t , ∙ ⊢< prop > t : Pi (ty 0) prop (Sort prop) (var 0) -> False.
Proof.
  (* We interpret the judgment in our ZF model *)
  intros t H. apply model in H. destruct H as [ iΓ fΓ iA fA _ vt ].
  (* We unfold the interpretation function using [inversion] *)
  inversion fΓ ; subst ; clear fΓ. 
  inversion fA ; subst ; clear fA. 
  inversion H3 ; subst ; clear H3.
  inversion H5 ; subst ; clear H5. 
  inversion H2 ; subst ; clear H2. 
  inversion H1 ; subst ; clear H1. 
  inversion H4 ; subst ; clear H4. 
  (* We derive a contradiction *)
  assert (∅ ∈ ⋆) as Hγ. { now apply inSetSingl. }
  specialize (vt _ Hγ). clear Hγ. apply subsingl_true_if in vt.
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


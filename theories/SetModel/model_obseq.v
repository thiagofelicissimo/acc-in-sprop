From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_acc HO_obseq HO_forall.
Require Import model_interp model_def.

Lemma model_obseq (Γ : ctx) (i : level) (A a b : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (ta : Γ ⊢< i > a : A) (ma : model_typing Γ i a A)
  (tb : Γ ⊢< i > b : A) (mb : model_typing Γ i b A) :
  model_typing Γ (Ax prop) (obseq i A a b) (Sort prop).
Proof.
  destruct i as [ i | ].
  - destruct ma as [ iΓ fΓ iA fA ia fa vA va ]. destruct mb as [ iΓ' fΓ' iA' fA' ib fb vA' vb ].
    destruct (functional_ctx Γ fΓ fΓ'). destruct (functional_tm A fA fA'). clear fΓ' fA' vA'. econstructor.
    + exact fΓ.
    + apply interp_prop.
    + apply interp_obseq_r. exact fA. exact fa. exact fb.
    + apply propTy_HO_typing.
    + eapply eqTy_HO_typing'. exact vA. exact va. exact vb.
  - destruct ma as [ iΓ fΓ iA fA vA va ]. destruct mb as [ iΓ' fΓ' iA' fA' vA' vb ].
    destruct (functional_ctx Γ fΓ fΓ'). destruct (functional_tm A fA fA'). clear fΓ' fA' vA'. econstructor.
    + exact fΓ.
    + apply interp_prop.
    + apply interp_obseq_i. 
    + apply propTy_HO_typing.
    + intros. refine (transpS (fun X => ⋆ ∈ X) (sym _) _). apply el_propTy. now apply ZFinpower. 
Qed.

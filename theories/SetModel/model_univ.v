From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp model_def.

Open Scope subst_scope.

Lemma model_univ (Γ : ctx) (l : level) (tΓ : ⊢ Γ) (mΓ : model_ctx Γ) :
  model_typing Γ (Ax (Ax l)) (Sort l) (Sort (Ax l)).
Proof.
  destruct mΓ as [ iΓ fΓ ]. destruct l as [ l | ].
  (* Type *)
  + econstructor.
    * exact fΓ.
    * apply interp_type.
    * apply interp_type.
    * apply univTy_HO_typing.
    * apply univTy_HO_typing'.
  (* Prop *)
  + econstructor.
    * exact fΓ.
    * apply interp_type.
    * apply interp_prop.
    * apply univTy_HO_typing.
    * apply propTy_HO_typing'.
Qed.

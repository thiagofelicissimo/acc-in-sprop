From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp.

Open Scope subst_scope.

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
    (fA : interp_tm Γ (Ax prop) A iA)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω)
    (vt : ∀ γ ∈ iΓ, ∅ ∈ iA γ).

Definition model_typing (Γ : ctx) (l : level) (t A : term) : Prop :=
  match l with
  | prop => model_typing_irr Γ t A
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
    (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l)
    (vt : ∀ γ ∈ iΓ, it γ ∈ 𝕌el l (iA γ))
    (vu : ∀ γ ∈ iΓ, it γ ≡ iu γ).
  
Inductive model_conv_irr (Γ : ctx) (t u A : term) : Prop := True.
(* | mkModelConvIrr (iΓ : ZFSet) *)
(*     (fΓ : interp_ctx Γ iΓ) *)
(*     (iA : ZFSet -> ZFSet) *)
(*     (fA : interp_tm Γ (Ax prop) A iA) *)
(*     (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω) *)
(*     (vt : ∀ γ ∈ iΓ, ∅ ∈ iA γ). *)

Definition model_conv (Γ : ctx) (l : level) (t u A : term) : Prop :=
  match l with
  | prop => model_conv_irr Γ t u A
  | ty l => model_conv_rel Γ l t u A
  end.

(* We assume that the extra assumptions are validated by the model *)
Axiom valid_assm : forall c A iA, nth_error assm_sig c = Some A
                                  -> interp_tm ∙ (ty 0) A iA
                                  -> ∅ ∈ iA ∅.

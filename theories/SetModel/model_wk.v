From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_acc HO_obseq HO_forall.
Require Import model_interp.

Open Scope subst_scope.

Inductive interp_ren : forall (Δ : ctx) (Γ : ctx) (ρ : nat -> nat) (iρ : ZFSet -> ZFSet), Prop :=

| interp_ren_empty : forall Δ ρ, interp_ren Δ ∙ ρ (fun γ => ∅)

| interp_ren_cons : forall Γ Δ l A ρ iρ ix, interp_ren Δ Γ (↑ >> ρ) iρ
                    -> nth_proj Δ l (ρ 0) ix
                    -> interp_ren Δ (Γ ,, (l , A)) ρ (fun γ => ⟨ iρ γ ; ix γ ⟩).

Definition has_ren_interp_ctx (Γ : ctx) (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ) : Prop :=
  True.

Inductive has_ren_interp_tm (Γ : ctx) (l : level)
  (t : term) (it : ZFSet -> ZFSet) (ft : interp_tm Γ l t it)
  (Δ : ctx) (iΔ : ZFSet) (fΔ : interp_ctx Δ iΔ)
  (ρ : nat -> nat) (iρ : ZFSet -> ZFSet) (fρ : interp_ren Δ Γ ρ iρ) : Prop :=
| mkHasRenInterpTm : forall (iu : ZFSet -> ZFSet) (fu : interp_tm Δ l (ρ ⋅ t) iu) (vtu : iu ≡ (fun δ => it (iρ δ))),
    has_ren_interp_tm Γ l t it ft Δ iΔ fΔ ρ iρ fρ.

Inductive has_ren_interp_proj (Γ : ctx) (l : level)
  (x : nat) (ix : ZFSet -> ZFSet) (fx : nth_proj Γ l x ix)
  (Δ : ctx) (iΔ : ZFSet) (fΔ : interp_ctx Δ iΔ)
  (ρ : nat -> nat) (iρ : ZFSet -> ZFSet) (fρ : interp_ren Δ Γ ρ iρ) : Prop :=
| mkHasRenInterpProj : forall (iy : ZFSet -> ZFSet) (fy : nth_proj Δ l (ρ x) iy) (vxy : iy ≡ (fun δ => ix (iρ δ))),
    has_ren_interp_proj Γ l x ix fx Δ iΔ fΔ ρ iρ fρ.

Lemma has_ren_interp : (forall Γ l t it ft, (forall Δ iΔ fΔ ρ iρ fρ, has_ren_interp_tm Γ l t it ft Δ iΔ fΔ ρ iρ fρ))
                       /\ (forall Γ iΓ fΓ, has_ren_interp_ctx Γ iΓ fΓ)
                       /\ (forall Γ l x ix fx, (forall Δ iΔ fΔ ρ iρ fρ, has_ren_interp_proj Γ l x ix fx Δ iΔ fΔ ρ iρ fρ)).
Proof.
  apply interp_mutind.
  - intros. specialize (H Δ iΔ fΔ ρ iρ fρ). destruct H as [ iρ' fρ' vρ' ]. econstructor.
    + apply interp_var. exact fρ'.
    + exact vρ'.
  - intros. econstructor.
    + cbn. apply interp_type.
    + easy.
  - intros. econstructor.
    + apply interp_prop.
    + easy.
  - intros. specialize (H Δ iΔ fΔ ρ iρ fρ). destruct H as [ iA' fA' vA' ].
    set (Δ' := Δ,, (ty lA, ρ ⋅ A)).
    assert (interp_ctx Δ' (ctxExt lA iΔ iA')) as fΔ'.
    { apply interp_cons_rel. exact fΔ. exact fA'. }
    set (iρu := (fun γa => ⟨ iρ (ctx_wk lA iΔ iA' γa) ; ctx_var0 lA iΔ iA' γa ⟩)).
    assert (interp_ren Δ' (Γ,, (ty lA, A)) (upRen_term_term ρ) iρu) as fρu.
    { apply interp_ren_cons.
      - asimpl. admit.
      - asimpl. now apply here_rel. }
    specialize (H0 Δ' _ fΔ' (upRen_term_term ρ) iρu fρu). destruct H0 as [ iB' fB' vB' ].
    econstructor.
    + cbn. apply interp_pi_rr. apply fA'. apply fB'.
    + destruct (sym vB'). destruct (sym vA'). unfold piTy_HO. admit.
  - admit.
  - admit.
  - admit.
  - 
Admitted.

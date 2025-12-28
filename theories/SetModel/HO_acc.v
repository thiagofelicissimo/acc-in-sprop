Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO.

Definition ctxExt2 (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) : ZFSet :=
  ctxExt n (ctxExt n Γ A) (fun γa => A (ctx_wk n Γ A γa)).

(* Accessibility predicate *)

Definition accTy_HO (A R a : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => prop (acc (A γ) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) (a γ)).

Lemma accTy_HO_typing {n : nat} {Γ : ZFSet} {A R a : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HR : ∀ γaa ∈ ctxExt2 n Γ A, R γaa ∈ Ω)
  (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, accTy_HO A R a γ ∈ Ω.
Proof.
  intros γ Hγ. unfold accTy_HO. apply prop_typing.
Qed.

(* Eliminator of accessibility *)

Definition accelimTm_HO (n : nat) (A R P p a : ZFSet -> ZFSet) :=
  fun γ => accrec n (A γ) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) (fun x => P ⟨ γ ; x ⟩) (fun x f => p ⟨ ⟨ γ ; x ⟩ ; f ⟩) (a γ).


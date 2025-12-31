Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO.

Definition ctxExt2 (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) : ZFSet :=
  ctxExt n (ctxExt n Γ A) (fun γa => A (ctx_wk n Γ A γa)).

(* Accessibility predicate *)

Definition accTy_HO (A R a : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => subsingl (acc (A γ) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) (a γ)).

Lemma accTy_HO_cong {n : nat} {Γ : ZFSet} {A1 A2 R1 R2 a1 a2 : ZFSet -> ZFSet}
  (HAe : ∀ γ ∈ Γ, A1 γ ≡ A2 γ) (HRe : ∀ γaa ∈ ctxExt2 n Γ A1, R1 γaa ≡ R2 γaa) (Hae : ∀ γ ∈ Γ, a1 γ ≡ a2 γ) :
  ∀ γ ∈ Γ, accTy_HO A1 R1 a1 γ ≡ accTy_HO A2 R2 a2 γ.
Proof.
Admitted.

Lemma accTy_HO_typing {n : nat} {Γ : ZFSet} {A R a : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HR : ∀ γaa ∈ ctxExt2 n Γ A, R γaa ∈ Ω)
  (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, accTy_HO A R a γ ∈ Ω.
Proof.
  intros γ Hγ. unfold accTy_HO. apply subsingl_typing.
Qed.

(* Eliminator of accessibility *)

Definition accelimTm_HO (n : nat) (A R P p a : ZFSet -> ZFSet) :=
  fun γ => accrec n (A γ) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) (fun x => P ⟨ γ ; x ⟩) (fun x f => p ⟨ ⟨ γ ; x ⟩ ; f ⟩) (a γ).


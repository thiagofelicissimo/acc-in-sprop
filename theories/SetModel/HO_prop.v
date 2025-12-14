Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO.

(* Universe of propositions *)

Definition propTy_HO : ZFSet -> ZFSet := fun _ => ⟨ Ω ; ⟨ ZFfour ; ∅ ⟩ ⟩.

Lemma propTy_HO_typing {n : nat} {Γ : ZFSet} : ∀ γ ∈ Γ, propTy_HO γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. apply setMkPair_typing.
  - apply Ω_typing.
  - apply setMkPair_typing.
    + apply four_typing.
    + apply empty_in_univ.
Qed.

Lemma el_propTy {n : nat} {γ : ZFSet} : 𝕌el n (propTy_HO γ) ≡ Ω.
Proof.
  apply setPairβ1.
  + apply Ω_typing.
  + apply setMkPair_typing. apply four_typing. apply empty_in_univ.
Qed.

(* False proposition *)

Definition falseTy_HO : ZFSet -> ZFSet := fun γ => prop FalseS.

Lemma falseTy_HO_typing (Γ : ZFSet) : ∀ γ ∈ Γ, falseTy_HO γ ∈ Ω.
Proof.
  intros. cbn. apply prop_typing.
Qed.

(* Eliminator of False *)

Definition emptyrecTm_HO (A : ZFSet -> ZFSet) (H : ZFSet -> ZFSet) := ∅.

Lemma emptyrecTm_HO_typing {n : nat} {Γ : ZFSet} {A H : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HH : ∀ γ ∈ Γ, H γ ∈ falseTy_HO γ) :
  ∀ γ ∈ Γ, emptyrecTm_HO A H ∈ 𝕌el n (A γ).
Proof.
  intros γ Hγ. specialize (HH γ Hγ). cbn in HH. apply prop_true_if in HH. destruct HH.
Qed.

(* Observational equality *)

Definition eqTy_HO (A t u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => prop (t γ ≡ u γ).

Definition reflTm_HO (A t : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma eqTy_HO_typing {n : nat} {Γ : ZFSet} {A t u : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, eqTy_HO A t u γ ∈ Ω.
Proof.
  intros γ Hγ. cbn. apply prop_typing.
Qed.

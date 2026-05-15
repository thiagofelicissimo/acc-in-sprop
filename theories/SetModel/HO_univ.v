Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO.

(* Interpretation of the universe of types in our higher-order model *)

Definition univTy_HO (n : nat) : ZFSet -> ZFSet := fun _ => ⟨ 𝕌 n ; ⟨ ZFthree ; ∅ ⟩ ⟩.

Lemma univTy_HO_typing {n : nat} {Γ : ZFSet} : ∀ γ ∈ Γ, univTy_HO n γ ∈ 𝕌 (S n).
Proof.
  intros γ Hγ. apply setMkPair_typing.
  - apply 𝕌_in_𝕍.
  - apply setMkPair_typing.
    + apply three_typing.
    + apply empty_in_univ.
Qed.

Lemma el_univTy {n : nat} {γ : ZFSet} : 𝕌el (S n) (univTy_HO n γ) ≡ 𝕌 n.
Proof.
  apply setPairβ1.
  + apply 𝕌_in_𝕍.
  + apply setMkPair_typing. apply three_typing. apply empty_in_univ.
Qed.


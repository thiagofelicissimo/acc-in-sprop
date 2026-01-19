Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO.

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

(* Clipped version *)

Definition univTy_cl (n : nat) (Γ : ZFSet) : ZFSet -> ZFSet := clip Γ (univTy_HO n).

Lemma univTy_cl_typing {n : nat} {Γ : ZFSet} : ∀ γ ∈ Γ, univTy_cl n Γ γ ∈ 𝕌 (S n).
Proof.
  apply clipped_typing_𝕌. now apply univTy_HO_typing.
Qed.

Lemma el_univTy_cl {n : nat} {Γ γ : ZFSet} (Hγ : γ ∈ Γ) : 𝕌el (S n) (univTy_cl n Γ γ) ≡ 𝕌 n.
Proof.
  unfold univTy_cl. destruct (sym (clip_inside Γ (univTy_HO n) γ Hγ)). now apply el_univTy.
Qed.

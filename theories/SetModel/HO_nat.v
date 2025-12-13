Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO HO_pi.

Definition natTy_HO : ZFSet -> ZFSet := fun _ => ⟨ ω ; ⟨ ∅ ; ∅ ⟩ ⟩.

Lemma el_natTy {n : nat} {γ : ZFSet} : 𝕌el n (natTy_HO γ) ≡ ω.
Proof.
  apply setPairβ1.
  + apply ZFuniv_uncountable.
  + apply setMkPair_typing. apply zero_typing. apply empty_in_univ.
Qed.

Lemma natTy_HO_typing (n : nat) {γ : ZFSet} : natTy_HO γ ∈ 𝕌 n.
Proof.
  apply setMkPair_typing.
  - now apply ZFuniv_uncountable.
  - apply setMkPair_typing.
    + apply zero_typing.
    + apply empty_in_univ.
Qed.

(* Zero *)

Definition zeroTm_HO : ZFSet -> ZFSet := fun _ => ∅.

Lemma zeroTm_HO_typing (n : nat) {γ : ZFSet} : zeroTm_HO γ ∈ 𝕌el n (natTy_HO γ).
Proof.
  refine (transpS (fun x => _ ∈ x) _ _).
  - symmetry. apply el_natTy. 
  - apply zero_typing.
Qed.

(* Successor *)

Definition sucTm_HO (n : nat) (t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ZFsuc (t γ).

Lemma sucTm_HO_typing {n : nat} {Γ γ : ZFSet} {t : ZFSet -> ZFSet} (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (natTy_HO γ)) (Hγ : γ ∈ Γ) :
  sucTm_HO n t γ ∈ 𝕌el n (natTy_HO γ).
Proof.
  refine (transpS (fun x => _ ∈ x) _ _).
  { symmetry. apply el_natTy. }
  apply suc_typing.
  refine (transpS (fun x => _ ∈ x) _ _).
  { apply (@el_natTy n γ). }
  now apply Ht.
Qed.

(* Recursor *)

Definition natrecTm_HO (n : nat) (P : ZFSet -> ZFSet -> ZFSet) (pz : ZFSet -> ZFSet)
  (ps : ZFSet -> ZFSet -> ZFSet -> ZFSet) (m : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => natrec2 n (P γ) (pz γ) (ps γ) (m γ).

(* Lemma natrecTm_HO_typing {n : nat} {Γ : ZFSet} {P : ZFSet -> ZFSet -> ZFSet} {pz : ZFSet -> ZFSet} *)
(*   {ps : ZFSet -> ZFSet -> ZFSet -> ZFSet} {m : ZFSet -> ZFSet} *)
(*   (HP : ∀ γ ∈ Γ, ∀ m ∈ 𝕌el n (natTy_HO γ), P γ m ∈ 𝕌 n) (Hpz : ∀ γ ∈ Γ, pz Γ ∈ P γ (zeroTm_HO γ)) *)
(*   (Hps : ∀ γ ∈ Γ, ∀ m ∈ 𝕌el n (natTy_HO γ), ∀ pm ∈ 𝕌el n (P γ m), *)
(*       ps γ m pm ∈ P γ (sucTm_HO n (fun γnp => ))) *)
(*   (Hm : ∀ γ ∈ Γ, m γ ∈ 𝕌el n (natTy_HO γ)) :  *)
(*   ∀ γ ∈ Γ, natrecTm_HO n P pz ps m ∈ 𝕌el n (P γ m). *)

(* Definition sucTm_HO (n : nat) (t : ZFSet -> ZFSet) : ZFSet -> ZFSet := *)

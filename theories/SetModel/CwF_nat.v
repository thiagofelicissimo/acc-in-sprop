Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.
Require Import CwF.

Lemma zero_typing : ∅ ∈ ω.
Proof.
  now apply ZFininfinity. 
Qed.

Lemma empty_in_univ (n : nat) : ∅ ∈ 𝕍 n.
Proof.
  eapply ZFuniv_trans. apply zero_typing. apply ZFuniv_uncountable.
Qed.

Definition HO_Ty (n : nat) (Γ : ZFSet) (f : ZFSet -> ZFSet) := relToGraph Γ (𝕍 n × (ω × 𝕍 n)) (HO_rel f).
Definition HO_Tm (n : nat) (Γ : ZFSet) (f : ZFSet -> ZFSet) := relToGraph Γ (𝕍 n) (HO_rel f).

Lemma cwfTy_to_depSet_HO {n : nat} {Γ γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n × (ω × 𝕍 n)) (Hγ : γ ∈ Γ) :
  cwfTy_to_depSet n Γ (HO_Ty n Γ f) γ ≡ setFstPair (𝕍 n) (ω × 𝕍 n) (f γ).
Proof.
  refine (fequal (setFstPair _ _) _).
  now apply setAppArr_HO.
Qed. 

(* Type of natural numbers *)

Definition natTy_HO : ZFSet -> ZFSet := fun _ => ⟨ ω ; ⟨ ∅ ; ∅ ⟩ ⟩.

Definition natTy (n : nat) (Γ : ZFSet) := HO_Ty n Γ natTy_HO. 

Lemma natTy_HO_typing (n : nat) {γ : ZFSet} : natTy_HO γ ∈ 𝕍 n × (ω × 𝕍 n).
Proof.
  apply setMkPair_typing.
  - now apply ZFuniv_uncountable.
  - apply setMkPair_typing.
    + apply zero_typing.
    + apply empty_in_univ.
Qed.

Lemma cwfNat {n : nat} (Γ : ZFSet) : natTy n Γ ∈ cwfTy n Γ.
Proof.  
  apply relToGraph_typing.
  apply HO_rel_typing. intros. now apply natTy_HO_typing.
Qed.

(* Zero *)

Definition zeroTm_HO : ZFSet -> ZFSet := fun _ => ∅.

Definition zeroTm (n : nat) (Γ : ZFSet) := HO_Tm n Γ zeroTm_HO.

Lemma zeroTm_HO_pretyping (n : nat) {γ : ZFSet} : zeroTm_HO γ ∈ 𝕍 n.
Proof.
  apply empty_in_univ.
Qed.

Lemma cwfZero {n : nat} (Γ : ZFSet) : zeroTm n Γ ∈ cwfTm n Γ (natTy n Γ).
Proof.
  apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing. intros. now apply zeroTm_HO_pretyping.
  - intros γ Hγ. refine (transp2S (fun X Y => X ∈ Y) _ _ _).
    + symmetry. apply setAppArr_HO. intros ; now apply zeroTm_HO_pretyping. assumption.
    + symmetry. refine (trans _ _).
      { apply cwfTy_to_depSet_HO. intros ; now apply natTy_HO_typing. assumption. }
      apply setPairβ1. apply ZFuniv_uncountable.
      apply setMkPair_typing. apply zero_typing. apply empty_in_univ.
    + apply zero_typing.
Qed.

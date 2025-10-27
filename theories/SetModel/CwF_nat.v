Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.
Require Import CwF.
Require Import CwF_library.

(* Type of natural numbers *)

Definition natTy_HO : ZFSet -> ZFSet := fun _ => ⟨ ω ; ⟨ ∅ ; ∅ ⟩ ⟩.

Definition natTy (n : nat) (Γ : ZFSet) := HO_Ty n Γ natTy_HO. 

Lemma setFstPair_natTy {n : nat} {γ : ZFSet} : setFstPair (𝕍 n) (ω × 𝕍 n) (natTy_HO γ) ≡ ω.
Proof.
  apply setPairβ1.
  + apply ZFuniv_uncountable.
  + apply setMkPair_typing. apply zero_typing. apply empty_in_univ.
Qed.

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

Lemma zeroTm_HO_typing (n : nat) {γ : ZFSet} : zeroTm_HO γ ∈ setFstPair (𝕍 n) (ω × 𝕍 n) (natTy_HO γ).
Proof.
  refine (transpS (fun x => _ ∈ x) _ _).
  - symmetry. apply setFstPair_natTy. 
  - apply zero_typing.
Qed.

Lemma cwfZero {n : nat} (Γ : ZFSet) : zeroTm n Γ ∈ cwfTm n Γ (natTy n Γ).
Proof.
  apply HO_Tm_typing.
  - intros. apply natTy_HO_typing.
  - intros γ Hγ. apply zeroTm_HO_typing.
Qed.

(* Successor *)

Definition sucTm_HO (n : nat) (Γ : ZFSet) (t : ZFSet) : ZFSet -> ZFSet :=
  fun γ => ZFsuc (setAppArr Γ (𝕍 n) t γ).

Definition sucTm (n : nat) (Γ : ZFSet) (t : ZFSet) :=
  HO_Tm n Γ (sucTm_HO n Γ t).

Lemma sucTm_HO_typing {n : nat} {Γ t γ : ZFSet} (Ht : t ∈ cwfTm n Γ (natTy n Γ)) (Hγ : γ ∈ Γ) :
  sucTm_HO n Γ t γ ∈ setFstPair (𝕍 n) (ω × 𝕍 n) (natTy_HO γ).
Proof.
  refine (transpS (fun x => _ ∈ x) _ _).
  { symmetry. apply setFstPair_natTy. }
  apply suc_typing.
  refine (transpS (fun x => _ ∈ x) _ _).
  { apply (@setFstPair_natTy n γ). }
  apply setAppArr_Tm_detyping ; try assumption.
  intros ; apply natTy_HO_typing.
Qed.

Lemma cwfSuc {n : nat} {Γ t : ZFSet} (Ht : t ∈ cwfTm n Γ (natTy n Γ)) :
  sucTm n Γ t ∈ cwfTm n Γ (natTy n Γ).
Proof.
  apply HO_Tm_typing.
  - intros. apply natTy_HO_typing.
  - intros γ Hγ. now apply sucTm_HO_typing.
Qed.


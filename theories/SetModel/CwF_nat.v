Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO HO_pi HO_nat.
Require Import CwF CwF_library.

(* Type of natural numbers *)

Definition natTy (n : nat) (Γ : ZFSet) := HO_to_cwfTy n Γ natTy_HO. 

Lemma cwfNat {n : nat} (Γ : ZFSet) : natTy n Γ ∈ cwfTy n Γ.
Proof.  
  apply relToGraph_typing.
  apply HO_rel_typing. intros. now apply natTy_HO_typing.
Qed.

Lemma cwfNat_to_HO {n : nat} (Γ : ZFSet) : ∀ γ ∈ Γ, cwfTy_to_HO n Γ (natTy n Γ) γ ≡ natTy_HO γ.
Proof.
  intros γ Hγ. cbn. apply setAppArr_HO. 2:assumption. clear γ Hγ.
  intros γ Hγ. now apply natTy_HO_typing.
Qed.

(* Zero *)

Definition zeroTm (n : nat) (Γ : ZFSet) := HO_to_cwfTm n Γ zeroTm_HO.

Lemma cwfZero {n : nat} (Γ : ZFSet) : zeroTm n Γ ∈ cwfTm n Γ (natTy n Γ).
Proof.
  apply HO_to_cwfTm_typing.
  - intros. apply natTy_HO_typing.
  - intros γ Hγ. apply zeroTm_HO_typing.
Qed.

(* Successor *)

Definition sucTm (n : nat) (Γ : ZFSet) (t : ZFSet) :=
  HO_to_cwfTm n Γ (sucTm_HO n (cwfTm_to_HO n Γ t)).

Lemma cwfSuc {n : nat} {Γ t : ZFSet} (Ht : t ∈ cwfTm n Γ (natTy n Γ)) :
  sucTm n Γ t ∈ cwfTm n Γ (natTy n Γ).
Proof.
  apply HO_to_cwfTm_typing.
  - intros. apply natTy_HO_typing.
  - intros γ Hγ. apply (sucTm_HO_typing (Γ := Γ)). 2:assumption. clear γ Hγ.
    intros γ Hγ. refine (transpS (fun X => _ ∈ 𝕌el n X) (cwfNat_to_HO (n := n) Γ γ Hγ) _).
    apply cwfTm_to_HO_typing. apply cwfNat. assumption. assumption.
Qed.


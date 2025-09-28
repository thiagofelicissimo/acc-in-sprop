Set Primitive Projections.
Set Universe Polymorphism.
Set Definitional UIP.

Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.

(* We define a CwF that supports all the type formers and operations of CICobs *)

(* Underlying category *)

Definition cwfSub (Γ Δ : ZFSet) := Γ ⇒ Δ.
Definition cwfId (Γ : ZFSet) := setIdArr Γ.
Definition cwfComp (Γ Δ Θ σ τ : ZFSet) := setCompArr Θ Δ Γ τ σ.

Lemma cwfId_typing (Γ : ZFSet) : cwfId Γ ∈ cwfSub Γ Γ.
Proof.
  exact (setIdArr_typing Γ).
Qed.

Lemma cwfComp_typing {Γ Δ Θ σ τ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) (Hτ : τ ∈ cwfSub Θ Δ) : cwfComp Γ Δ Θ σ τ ∈ cwfSub Θ Γ.
Proof.
  exact (setCompArr_typing Hτ Hσ).
Qed.

Lemma cwfCompId_right {Γ Δ σ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) : cwfComp Γ Δ Δ σ (cwfId Δ) ≡ σ.
Proof.
  exact (setCompId_left Hσ).
Qed.

Lemma cwfCompId_left {Γ Δ σ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) : cwfComp Γ Γ Δ (cwfId Γ) σ ≡ σ.
Proof.
  exact (setCompId_right Hσ).
Qed.

Lemma cwfCompAssoc {Γ Δ Θ Ξ σ τ υ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) (Hτ : τ ∈ cwfSub Θ Δ) (Hυ : υ ∈ cwfSub Ξ Θ) :
  cwfComp Γ Δ Ξ σ (cwfComp Δ Θ Ξ τ υ) ≡ cwfComp Γ Θ Ξ (cwfComp Γ Δ Θ σ τ) υ.
Proof.
  exact (sym (setCompAssoc Hυ Hτ Hσ)).
Qed.

(* Terminal object *)

Definition cwfEmpty : ZFSet := setSingl ∅.
Definition cwfSubEmpty (Γ : ZFSet) : ZFSet := Γ × cwfEmpty.

Lemma cwfSubEmpty_typing (Γ : ZFSet) : cwfSubEmpty Γ ∈ cwfSub Γ cwfEmpty.
Proof.
  apply ZFincomp. split.
  - apply ZFinpower. intros x Hx. exact Hx.
  - assert (∅ ∈ cwfEmpty) as H. { apply inSetSingl. reflexivity. }
    intros γ Hγ. exists ∅. split.
    + split. exact H. exact (setMkPair_typing Hγ H).
    + intros x [ Hx _ ]. apply inSetSingl in Hx. exact (sym Hx).
Qed.

Lemma cwfSubEmpty_unique {Γ σ : ZFSet} (Hσ : σ ∈ cwfSub Γ cwfEmpty) : σ ≡ cwfSubEmpty Γ.
Proof.
  apply (setArr_funext Hσ (cwfSubEmpty_typing Γ)). intros γ Hγ.
  pose proof (setAppArr_typing Hσ Hγ) as H1. apply inSetSingl in H1. refine (trans H1 _).
  pose proof (setAppArr_typing (cwfSubEmpty_typing Γ) Hγ) as H2. apply inSetSingl in H2. exact (sym H2).
Qed.

(* Presheaf of types *)

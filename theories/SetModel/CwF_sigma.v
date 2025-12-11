Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.
Require Import CwF.
Require Import CwF_library.


Definition sigmaTy_HO (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setSigma n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a))
           ; ⟨ ZFone ; typeTelescope2 n Γ A B γ ⟩ ⟩.

Definition sigmaTy (n : nat) (Γ : ZFSet) (A : ZFSet) (B : ZFSet) : ZFSet :=
  HO_to_cwfTy n Γ (sigmaTy_HO n Γ (cwfTy_to_HO n Γ A) (cwfTy_to_HO2 n Γ A B)).

Lemma sigmaTy_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) : ∀ γ ∈ Γ, sigmaTy_HO n Γ A B γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setSigma_typing.
    + apply 𝕌el_typing. now apply HA.
    + intros a Ha. apply 𝕌el_typing. now apply HB. 
  - apply setMkPair_typing.
    + apply one_typing.
    + now apply typeTelescope2_typing.
Qed.

Lemma el_sigmaTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌el n (sigmaTy_HO n Γ A B γ) ≡ setSigma n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a)).
Proof.
  apply setPairβ1.
  - apply setSigma_typing. apply 𝕌el_typing. now apply HA.
    intros a Ha. apply 𝕌el_typing. now apply HB.
  - apply setMkPair_typing.
    + apply one_typing.
    + now apply typeTelescope2_typing.
Qed.

Lemma cwfSigma {n : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) :
  sigmaTy n Γ A B ∈ cwfTy n Γ.
Proof.
  apply relToGraph_typing. apply HO_rel_typing. apply sigmaTy_HO_typing.
  - now apply cwfTy_to_HO_typing.
  - now apply cwfTy_to_HO2_typing.
Qed.

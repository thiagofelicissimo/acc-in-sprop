Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.

Definition 𝕌 (n : nat) := 𝕍 n × (ω × 𝕍 n).
Definition 𝕌el (n : nat) (A : ZFSet) := setFstPair (𝕍 n) (ω × 𝕍 n) A.
Definition 𝕌hd (n : nat) (A : ZFSet) := setFstPair ω (𝕍 n) (setSndPair (𝕍 n) (ω × 𝕍 n) A).
Definition 𝕌lbl (n : nat) (A : ZFSet) := setSndPair ω (𝕍 n) (setSndPair (𝕍 n) (ω × 𝕍 n) A).

Lemma 𝕌el_typing {n : nat} {A : ZFSet} : A ∈ 𝕌 n -> 𝕌el n A ∈ 𝕍 n.
Proof.
  intro HA. now apply setFstPair_typing. 
Qed.

Lemma 𝕌hd_typing {n : nat} {A : ZFSet} : A ∈ 𝕌 n -> 𝕌hd n A ∈ ω.
Proof.
  intro HA. apply setFstPair_typing. now apply setSndPair_typing.
Qed.

Lemma 𝕌lbl_typing {n : nat} {A : ZFSet} : A ∈ 𝕌 n -> 𝕌lbl n A ∈ 𝕍 n.
Proof.
  intro HA. apply setSndPair_typing. now apply setSndPair_typing.
Qed.

Lemma 𝕌_incl_𝕍 {n : nat} : 𝕌 n ⊂ 𝕍 n.
Proof.
  intros x Hx. refine (transpS (fun X => X ∈ 𝕍 n) (sym (setPairη Hx)) _). apply setMkPair_sorting.
  - now apply setFstPair_typing.
  - set (y := setSndPair (𝕍 n) (ω × 𝕍 n) x). assert (y ∈ ω × 𝕍 n) as Hy. { now apply setSndPair_typing. }
    clearbody y. clear x Hx. refine (transpS (fun X => X ∈ 𝕍 n) (sym (setPairη Hy)) _). apply setMkPair_sorting.
    + eapply ZFuniv_trans. now apply setFstPair_typing. apply ZFuniv_uncountable.
    + now apply setSndPair_typing.
Qed.

Lemma 𝕌_in_𝕍 {n : nat} : 𝕌 n ∈ 𝕍 (S n).
Proof.
  apply setProd_typing.
  + apply ZFuniv_hierarchy.
  + apply setProd_typing.
    * apply ZFuniv_uncountable.
    * apply ZFuniv_hierarchy.
Qed.

(* Extended contexts *)

Definition ctxExt (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) := setSigma n Γ (fun γ => 𝕌el n (A γ)).

Definition ctx_wk (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (γa : ZFSet) := setFstSigma n Γ (fun γ => 𝕌el n (A γ)) γa.

Definition ctx_var0 (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (γa : ZFSet) := setSndSigma n Γ (fun γ => 𝕌el n (A γ)) γa.

Lemma ctx_wk_typing {n : nat} {Γ γa : ZFSet} {A : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Hγa : γa ∈ ctxExt n Γ A) :
  ctx_wk n Γ A γa ∈ Γ.
Proof.
  apply (setFstSigma_typing (A := Γ) (B := fun γ => 𝕌el n (A γ))).
  - intros γ Hγ. apply 𝕌el_typing. now apply HA.
  - assumption.
Qed.  

Lemma ctx_var0_typing {n : nat} {Γ γa : ZFSet} {A : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Hγa : γa ∈ ctxExt n Γ A) :
  ctx_var0 n Γ A γa ∈ 𝕌el n (A (ctx_wk n Γ A γa)).
Proof.
  apply (setSndSigma_typing (A := Γ) (B := fun γ => 𝕌el n (A γ))).
  - intros γ Hγ. apply 𝕌el_typing. now apply HA.
  - assumption.
Qed.

Lemma ctxExtβ1 {n : nat} {Γ γ a : ZFSet} {A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Hγ : γ ∈ Γ) (Ha : a ∈ 𝕌el n (A γ)) :
  ctx_wk n Γ A ⟨ γ ; a ⟩ ≡ γ.
Proof.
  apply (setSigmaβ1 (A := Γ) (B := fun γ => 𝕌el n (A γ))) ; try assumption.
  intros γ' Hγ'. apply 𝕌el_typing. now apply HA.
Qed.

Lemma ctxExtβ2 {n : nat} {Γ γ a : ZFSet} {A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Hγ : γ ∈ Γ) (Ha : a ∈ 𝕌el n (A γ)) :
  ctx_var0 n Γ A ⟨ γ ; a ⟩ ≡ a.
Proof.
  apply (setSigmaβ2 (A := Γ) (B := fun γ => 𝕌el n (A γ))) ; try assumption.
  intros γ' Hγ'. apply 𝕌el_typing. now apply HA.
Qed.


Lemma typeExt_typing {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  ∀ a ∈ 𝕌el n (A γ), B ⟨ γ ; a ⟩ ∈ 𝕌 n.
Proof.
  intros a Ha. apply HB. apply setMkSigma_typing ; try assumption.
  clear γ Hγ a Ha. intros γ Hγ. apply 𝕌el_typing. now apply HA.
Qed.

Lemma termExt_typing {n : nat} {Γ γ : ZFSet} {A B t : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γa ∈ ctxExt n Γ A, t γa ∈ 𝕌el n (B γa)) (Hγ : γ ∈ Γ) :
  ∀ a ∈ 𝕌el n (A γ), t ⟨ γ ; a ⟩ ∈ 𝕌el n (B ⟨ γ ; a ⟩).
Proof.
  intros a Ha. apply Ht. apply setMkSigma_typing ; try assumption.
  clear γ Hγ a Ha. intros γ Hγ. apply 𝕌el_typing. now apply HA.
Qed.

(* Telescopes (useful for labels) *)

Definition typeToGraph (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) :=
  relToGraph (𝕌el n A) (𝕌 n) (HO_rel B).

Definition typeTelescope2 (n : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) :=
  fun γ => ⟨ A γ ; typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩) ⟩. 

Lemma typeToGraph_sorting (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕌 n)
  (HB : ∀ a ∈ 𝕌el n A, B a ∈ 𝕌 n) : typeToGraph n A B ∈ 𝕍 n.
Proof.
  assert (relToGraph (𝕌el n A) (𝕌 n) (HO_rel B) ∈ (𝕌el n A) ⇒ 𝕌 n).
  { apply relToGraph_typing. apply HO_rel_typing. intros a Ha. now apply HB. }
  assert (𝕌el n A ⇒ 𝕌 n ⊂ 𝕍 n) as H1.
  { apply setArr_big_typing. apply 𝕌el_typing. now apply HA. apply 𝕌_incl_𝕍. }
  apply H1. exact H.
Qed.

Lemma typeTelescope2_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) :
  ∀ γ ∈ Γ, typeTelescope2 n A B γ ∈ 𝕍 n.
Proof.
  intros γ Hγ. cbn. unfold typeTelescope2. apply setMkPair_sorting.
  - apply 𝕌_incl_𝕍. now apply HA.
  - apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

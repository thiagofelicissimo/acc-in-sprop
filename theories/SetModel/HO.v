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

(* Telescopes (useful for labels) *)

Definition typeToGraph (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) :=
  relToGraph (𝕌el n A) (𝕌 n) (HO_rel B).

Definition typeTelescope2 (n : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet -> ZFSet) :=
  fun γ => ⟨ A γ ; typeToGraph n (A γ) (B γ) ⟩. 

Lemma typeToGraph_sorting (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕌 n)
  (HB : ∀ a ∈ 𝕌el n A, B a ∈ 𝕌 n) : typeToGraph n A B ∈ 𝕍 n.
Proof.
  assert (relToGraph (𝕌el n A) (𝕌 n) (HO_rel B) ∈ (𝕌el n A) ⇒ 𝕌 n).
  { apply relToGraph_typing. apply HO_rel_typing. intros a Ha. now apply HB. }
  assert (𝕌el n A ⇒ 𝕌 n ⊂ 𝕍 n) as H1.
  { apply setArr_big_typing. apply 𝕌el_typing. now apply HA. apply 𝕌_incl_𝕍. }
  apply H1. exact H.
Qed.

Lemma typeTelescope2_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) : ∀ γ ∈ Γ, typeTelescope2 n A B γ ∈ 𝕍 n.
Proof.
  intros γ Hγ. cbn. unfold typeTelescope2. apply setMkPair_sorting.
  - apply 𝕌_incl_𝕍. now apply HA.
  - apply typeToGraph_sorting. now apply HA. now apply HB.
Qed.

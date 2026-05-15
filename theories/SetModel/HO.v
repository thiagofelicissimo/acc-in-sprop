From Stdlib Require Import Arith.
Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.

(* This file is the beginning of our higher-order model of observational type theory in IZF set theory.
   Most notably, we define the universe 𝕌, which contains the "codes" for the types. Each code consists of
   - The set of its elements
   - A natural number which represents its head constructor (0 for nat, 1 for pi, 2 for sigma, etc)
   - A list of subtypes, on which we want injectivity. For instance, in the case of A → B, we want
     injectivity on A and B. *)

Definition 𝕌 (n : nat) := 𝕍 n × (ω × 𝕍 n).
Definition 𝕌el (n : nat) (A : ZFSet) := setFstPair (𝕍 n) (ω × 𝕍 n) A.
Definition 𝕌hd (n : nat) (A : ZFSet) := setFstPair ω (𝕍 n) (setSndPair (𝕍 n) (ω × 𝕍 n) A).
Definition 𝕌lbl (n : nat) (A : ZFSet) := setSndPair ω (𝕍 n) (setSndPair (𝕍 n) (ω × 𝕍 n) A).

Lemma 𝕌el_typing {n : nat} {A : ZFSet} : A ∈ 𝕌 n -> 𝕌el n A ∈ 𝕍 n.
Proof.
  intro HA. now apply setFstPair_typing. 
Qed.

(* This is a more powerful version of [𝕌el_typing] which makes use of the axiom ZFuniv_descr, whose
   constructive status I am somewhat unsure of (maybe it requires collection instead of replacement).
   We use it in only one place (congruence for lambda abstraction), and I am pretty sure that we could
   do without it. *)

Lemma 𝕌el_typing' {n : nat} {A : ZFSet} : 𝕌el n A ∈ 𝕍 n. 
Proof.
  unfold 𝕌el. unfold setFstPair. apply ZFuniv_descr. intros x Hx. apply ZFincomp in Hx. now destruct Hx.
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

Lemma 𝕌_le_incl {n m : nat} : (n <= m) -> 𝕌 n ⊂ 𝕌 m.
Proof.
  intros H x Hx. refine (transpS (fun X => X ∈ 𝕌 m) (sym (setPairη Hx)) _). apply setMkPair_typing.
  - eapply univ_le_incl. exact H. now apply setFstPair_typing.
  - assert (setSndPair (𝕍 n) (ω × 𝕍 n) x ∈ ω × 𝕍 n) as Hy.
    { now apply setSndPair_typing. }
    refine (transpS (fun X => X ∈ ω × 𝕍 m) (sym (setPairη Hy)) _). apply setMkPair_typing.
    + now apply setFstPair_typing.
    + eapply univ_le_incl. exact H. now apply setSndPair_typing.
Qed.

(* Universe of propositions *)

Definition unit_set := setSingl ∅.
Notation "⋆" := unit_set.

Definition Ω := 𝒫 ⋆.
Definition subsingl (P : SProp) := { x ϵ ⋆ ∣ P }.

Lemma Ω_typing (n : nat) : Ω ∈ 𝕍 n.
Proof.
  apply ZFuniv_power. apply ZFuniv_pair.
  1,2: eapply ZFuniv_trans. 1,3: apply zero_typing. 1,2:apply ZFuniv_uncountable.
Qed.

Lemma subsingl_typing (P : SProp) : subsingl P ∈ Ω.
Proof.
  apply ZFinpower. intros x Hx. apply ZFincomp in Hx. now destruct Hx.
Qed.

Lemma subsingl_true_if (P : SProp) : ∀ x ∈ subsingl P, P.
Proof.
  intros x Hx. cbn. apply ZFincomp in Hx. now destruct Hx.
Qed.

Lemma subsingl_true_iff (P : SProp) : ∅ ∈ subsingl P ↔ P.
Proof.
  split.
  - apply subsingl_true_if.
  - intro H. apply ZFincomp. split.
    + apply ZFinpairing. now left.
    + assumption.
Qed.

Lemma proof_irr {P : ZFSet} (HP : P ∈ Ω) : ∀ p ∈ P, p ≡ ∅.
Proof.
  intros p Hp. unfold Ω in HP. apply ZFinpower in HP. specialize (HP p Hp). apply inSetSingl in HP.
  exact HP.
Qed.

Lemma proof_irr' {P : ZFSet} (HP : P ∈ Ω) : ∀ x ∈ P, ∅ ∈ P.
Proof.
  intros p Hp. unfold Ω in HP. apply ZFinpower in HP. specialize (HP p Hp). apply inSetSingl in HP.
  cbn. refine (transpS (fun X => X ∈ P) HP Hp).
Qed.

Lemma subsingl_impl {P Q : SProp} : (P -> Q) ↔ (subsingl P ⊂ subsingl Q).
Proof.
  split.
  - intro H. intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx HP ].
    apply ZFincomp. split. assumption. tauto.
  - intros H HP. assert (∅ ∈ subsingl P) as H1. { apply ZFincomp. split ; try assumption. now apply inSetSingl. }
    apply H in H1. apply ZFincomp in H1. now destruct H1.
Qed.

Lemma subsingl_ext {P Q : SProp} : (P ↔ Q) ↔ (subsingl P ≡ subsingl Q).
Proof.
  split.
  - intros [ H1 H2 ]. apply ZFext ; now apply (fstS subsingl_impl).
  - intro H. split ; apply (sndS subsingl_impl).
    + refine (transpS (fun X => _ ⊂ X) H _). easy.
    + refine (transpS (fun X => X ⊂ _) H _). easy.
Qed.

(* The contexts of our model will simply be sets. We define context extension as a dependent sum *)

Definition ctxExt (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) := setSigma n Γ (fun γ => 𝕌el n (A γ)).

Definition ctx_wk (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (γa : ZFSet) := setFstSigma n Γ (fun γ => 𝕌el n (A γ)) γa.

Definition ctx_var0 (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (γa : ZFSet) := setSndSigma n Γ (fun γ => 𝕌el n (A γ)) γa.

Lemma ctxExt_typing {n : nat} {Γ γ a : ZFSet} {A : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Hγ : γ ∈ Γ) (Ha : a ∈ 𝕌el n (A γ)) : ⟨ γ ; a ⟩ ∈ ctxExt n Γ A.
Proof.
  apply setMkSigma_typing ; try assumption.
  clear γ a Hγ Ha. intros γ Hγ. apply 𝕌el_typing. now apply HA.
Qed.

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


Lemma typeExt_typing {nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  ∀ a ∈ 𝕌el nA (A γ), B ⟨ γ ; a ⟩ ∈ 𝕌 nB.
Proof.
  intros a Ha. apply HB. apply setMkSigma_typing ; try assumption.
  clear γ Hγ a Ha. intros γ Hγ. apply 𝕌el_typing. now apply HA.
Qed.

Lemma termExt_typing {nA nB : nat} {Γ γ : ZFSet} {A B t : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γa ∈ ctxExt nA Γ A, t γa ∈ 𝕌el nB (B γa)) (Hγ : γ ∈ Γ) :
  ∀ a ∈ 𝕌el nA (A γ), t ⟨ γ ; a ⟩ ∈ 𝕌el nB (B ⟨ γ ; a ⟩).
Proof.
  intros a Ha. apply Ht. apply setMkSigma_typing ; try assumption.
  clear γ Hγ a Ha. intros γ Hγ. apply 𝕌el_typing. now apply HA.
Qed.

(* Given a type [A] and a dependent type [B], we define the "telescope" of A and B to
   be the pair of A and the graph of B. We want the dependent product [Π A B] to be injective
   with respect to the telescope of A and B, so we will store the telescope in its label. *)

Definition typeToGraph (nA nB : nat) (A : ZFSet) (B : ZFSet -> ZFSet) :=
  relToGraph (𝕌el nA A) (𝕌 nB) (HO_rel B).

Definition typeTelescope2 (nA nB : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) :=
  fun γ => ⟨ ⟨ nat_to_ω nA ; A γ ⟩ ; ⟨ nat_to_ω nB ; typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩) ⟩ ⟩. 

Lemma typeToGraph_cong (nA nB : nat) (A : ZFSet) {B1 B2 : ZFSet -> ZFSet} (HB : ∀ a ∈ 𝕌el nA A, B1 a ≡ B2 a) :
  typeToGraph nA nB A B1 ≡ typeToGraph nA nB A B2.
Proof.
  unfold typeToGraph. unfold HO_rel. unfold relToGraph. apply ZFext.
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
    + assumption.
    + refine (trans (sym _) Hx2). apply HB. apply setFstPair_typing. assumption.
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
    + assumption.
    + refine (trans _ Hx2). apply HB. apply setFstPair_typing. assumption.
Qed.

Lemma typeTelescope2_cong {nA nB : nat} {Γ : ZFSet} {A1 A2 B1 B2 : ZFSet -> ZFSet} 
  (HAe : ∀ γ ∈ Γ, A1 γ ≡ A2 γ) (HBe : ∀ γa ∈ ctxExt nA Γ A1, B1 γa ≡ B2 γa) :
  ∀ γ ∈ Γ, typeTelescope2 nA nB A1 B1 γ ≡ typeTelescope2 nA nB A2 B2 γ.
Proof.
  intros γ Hγ. cbn. unfold typeTelescope2. destruct (HAe γ Hγ).
  refine (fequal (fun X => ⟨ ⟨ nat_to_ω nA; A1 γ ⟩; ⟨ nat_to_ω nB; X ⟩ ⟩) _).
  apply typeToGraph_cong. intros a Ha. apply HBe.
  apply setMkSigma_typing ; try assumption. clear γ Hγ a Ha. 
  intros γ Hγ. apply 𝕌el_typing'. 
Qed.

Lemma typeToGraph_sorting (nA nB : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕌 nA)
  (HB : ∀ a ∈ 𝕌el nA A, B a ∈ 𝕌 nB) : typeToGraph nA nB A B ∈ 𝕍 (max nA nB).
Proof.
  assert (relToGraph (𝕌el nA A) (𝕌 nB) (HO_rel B) ∈ (𝕌el nA A) ⇒ 𝕌 nB).
  { apply relToGraph_typing. apply HO_rel_typing. intros a Ha. now apply HB. }
  assert (𝕌el nA A ⇒ 𝕌 nB ⊂ 𝕍 (max nA nB)) as H1.
  { apply setArr_big_typing.
    - eapply univ_le_incl. apply Nat.le_max_l. apply 𝕌el_typing. now apply HA.
    - eapply subset_trans. apply 𝕌_incl_𝕍. apply univ_le_incl. apply Nat.le_max_r. }
  apply H1. exact H.
Qed.

Lemma typeTelescope2_typing (nA nB : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) :
  ∀ γ ∈ Γ, typeTelescope2 nA nB A B γ ∈ 𝕍 (max nA nB).
Proof.
  intros γ Hγ. cbn. unfold typeTelescope2. apply setMkPair_sorting.
  - apply setMkPair_sorting.
    + eapply ZFuniv_trans. now apply nat_to_ω_typing. apply ZFuniv_uncountable.
    + eapply univ_le_incl. apply Nat.le_max_l. apply 𝕌_incl_𝕍. now apply HA.
  - apply setMkPair_sorting.
    + eapply ZFuniv_trans. now apply nat_to_ω_typing. apply ZFuniv_uncountable.
    + apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

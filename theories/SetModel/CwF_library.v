Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.
Require Import CwF.

(* Elements of 𝕌 are also elements of 𝕍 *)

Lemma 𝕌_incl_𝕍 {n : nat} : 𝕌 n ⊂ 𝕍 n.
Proof.
  intros x Hx. refine (transpS (fun X => X ∈ 𝕍 n) (sym (setPairη Hx)) _). apply setMkPair_sorting.
  - now apply setFstPair_typing.
  - set (y := setSndPair (𝕍 n) (ω × 𝕍 n) x). assert (y ∈ ω × 𝕍 n) as Hy. { now apply setSndPair_typing. }
    clearbody y. clear x Hx. refine (transpS (fun X => X ∈ 𝕍 n) (sym (setPairη Hy)) _). apply setMkPair_sorting.
    + eapply ZFuniv_trans. now apply setFstPair_typing. apply ZFuniv_uncountable.
    + now apply setSndPair_typing.
Qed.

(* Defining terms and types using higher-order stuff *)

Definition HO_to_cwfTy (n : nat) (Γ : ZFSet) (f : ZFSet -> ZFSet) :=
  relToGraph Γ (𝕌 n) (HO_rel f).

Definition HO_to_cwfTm (n : nat) (Γ : ZFSet) (f : ZFSet -> ZFSet) :=
  relToGraph Γ (𝕍 n) (HO_rel f).

Definition cwfTy_to_HO (n : nat) (Γ A : ZFSet) :=
  fun γ => setAppArr Γ (𝕌 n) A γ.

Definition cwfTy_to_HO2 (n : nat) (Γ A B : ZFSet) :=
  fun γ a => setAppArr (ctxExt n Γ A) (𝕌 n) B ⟨ γ ; a ⟩.

Lemma cwfTy_to_HO_typing {n : nat} {Γ A : ZFSet} (HA : A ∈ cwfTy n Γ) : ∀ γ ∈ Γ, cwfTy_to_HO n Γ A γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. now apply setAppArr_typing.
Qed.

Lemma cwfTy_to_HO2_typing {n : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) :
  ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (cwfTy_to_HO n Γ A γ), cwfTy_to_HO2 n Γ A B γ a ∈ 𝕌 n.
Proof.
  intros γ Hγ a Ha. apply setAppArr_typing. assumption.
  apply setMkSigma_typing.
  - clear γ Hγ a Ha. intros γ Hγ. now apply cwfTy_to_depSet_typing.
  - assumption.
  - assumption.
Qed.

Lemma HO_to_cwfTy_sorting (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕌 n)
  : HO_to_cwfTy n A B ∈ 𝕍 n.
Proof.
  assert (relToGraph A (𝕌 n) (HO_rel B) ∈ A ⇒ 𝕌 n).
  { apply relToGraph_typing. now apply HO_rel_typing. }
  assert (A ⇒ 𝕌 n ⊂ 𝕍 n) as H1.
  { apply setArr_big_typing. assumption. apply 𝕌_incl_𝕍. }
  now apply H1.
Qed.

Lemma HO_to_cwfTm_pretyping {n : nat} {Γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n) :
  HO_to_cwfTm n Γ f ∈ Γ ⇒ 𝕍 n.
Proof.
  apply relToGraph_typing. now apply HO_rel_typing.
Qed.

Lemma setAppArr_HO_to_cwfTm {n : nat} {Γ γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n) (Hγ : γ ∈ Γ) : 
  setAppArr Γ (𝕍 n) (HO_to_cwfTm n Γ f) γ ≡ f γ.
Proof.
  now apply setAppArr_HO.
Qed.

Lemma HO_to_cwfTy_to_depSet {n : nat} {Γ γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  cwfTy_to_depSet n Γ (HO_to_cwfTy n Γ f) γ ≡ 𝕌el n (f γ).
Proof.
  refine (fequal (setFstPair _ _) _).
  now apply setAppArr_HO.
Qed. 

Lemma setAppArr_Tm_typing {n : nat} {Γ t : ZFSet} {A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Ht : t ∈ Γ ⇒ 𝕍 n) :
  (∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ∈ 𝕌el n (A γ)) -> (t ∈ cwfTm n Γ (HO_to_cwfTy n Γ A)).
Proof.
  intro Ht'. apply ZFincomp. split ; try assumption.
  intros γ Hγ. refine (transpS (fun x => _ ∈ x) _ (Ht' γ Hγ)).
  symmetry. now apply HO_to_cwfTy_to_depSet.
Qed.

Lemma setAppArr_Tm_detyping {n : nat} {Γ t : ZFSet} {A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) :
  (t ∈ cwfTm n Γ (HO_to_cwfTy n Γ A)) -> ∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ∈ 𝕌el n (A γ).
Proof.
  intros Ht' γ Hγ. apply ZFincomp in Ht'. destruct Ht' as [ _ Ht' ].
  refine (transpS (fun x => _ ∈ x) _ (Ht' γ Hγ)).
  now apply HO_to_cwfTy_to_depSet.
Qed.

Lemma HO_to_cwfTm_typing {n : nat} {Γ : ZFSet} {f A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) :
  (∀ γ ∈ Γ, f γ ∈ 𝕌el n (A γ)) -> (HO_to_cwfTm n Γ f ∈ cwfTm n Γ (HO_to_cwfTy n Γ A)).
Proof.
  intro H. assert (∀ γ ∈ Γ, f γ ∈ 𝕍 n) as Hf.
  { intros γ Hγ. eapply ZFuniv_trans. now apply H. apply setFstPair_typing. now apply HA. }
  eapply (setAppArr_Tm_typing HA (HO_to_cwfTm_pretyping Hf)).
  intros γ Hγ. refine (transpS (fun x => x ∈ _) _ (H γ Hγ)).
  symmetry. now apply setAppArr_HO_to_cwfTm.
Qed.

Lemma HO_to_cwfTm_detyping {n : nat} {Γ : ZFSet} {f A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n) :
  (HO_to_cwfTm n Γ f ∈ cwfTm n Γ (HO_to_cwfTy n Γ A)) -> (∀ γ ∈ Γ, f γ ∈ 𝕌el n (A γ)).
Proof.
  intros H γ Hγ. eapply (setAppArr_Tm_detyping HA) in H.
  refine (transpS (fun x => x ∈ _) _ H). now apply setAppArr_HO_to_cwfTm. assumption.
Qed.

(* Telescopes (useful for labels) *)

Definition typeTelescope2 (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet -> ZFSet) :=
  fun γ => ⟨ A γ ; HO_to_cwfTy n (𝕌el n (A γ)) (B γ) ⟩.

Lemma typeTelescope2_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) : ∀ γ ∈ Γ, typeTelescope2 n Γ A B γ ∈ 𝕍 n.
Proof.
  intros γ Hγ. cbn. unfold typeTelescope2. apply setMkPair_sorting.
  - apply 𝕌_incl_𝕍. now apply HA.
  - apply HO_to_cwfTy_sorting. apply 𝕌el_typing. now apply HA. now apply HB.
Qed.

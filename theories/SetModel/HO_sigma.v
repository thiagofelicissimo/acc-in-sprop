Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO.

(* Sigma types *)

Definition sigmaTy_HO (n : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setSigma n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩))
           ; ⟨ ZFtwo ; typeTelescope2 n A B γ ⟩ ⟩.

Lemma sigmaTy_HO_typing {n : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) :
  ∀ γ ∈ Γ, sigmaTy_HO n A B γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setSigma_typing.
    + apply 𝕌el_typing. now apply HA.
    + intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB). 
  - apply setMkPair_typing.
    + apply two_typing.
    + apply (typeTelescope2_typing n (Γ := Γ)) ; try assumption. 
Qed.

Lemma el_sigmaTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌el n (sigmaTy_HO n A B γ) ≡ setSigma n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩)).
Proof.
  apply setPairβ1'. now apply (sigmaTy_HO_typing (Γ := Γ)).
Qed.

Lemma hd_sigmaTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌hd n (sigmaTy_HO n A B γ) ≡ ZFtwo.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply (sigmaTy_HO_typing (Γ := Γ)).
  apply setPairβ1. apply two_typing. apply (typeTelescope2_typing n (Γ := Γ)) ; try assumption.
Qed.  

Lemma lbl_sigmaTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌lbl n (sigmaTy_HO n A B γ) ≡ typeTelescope2 n A B γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply (sigmaTy_HO_typing (Γ := Γ)).
  apply setPairβ2. apply two_typing. apply (typeTelescope2_typing n (Γ := Γ)) ; try assumption.
Qed.

(* Injectivity of Sigma types *)

Definition dom_sigmaTy (n : nat) (x : ZFSet) :=
  setFstPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Definition cod_sigmaTy (n : nat) (x : ZFSet) :=
  setSndPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Lemma dom_sigmaTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  dom_sigmaTy n (sigmaTy_HO n A B γ) ≡ A γ.
Proof.
  refine (trans (fequal (setFstPair (𝕌 n) (𝕍 n)) _) _).
  now apply (lbl_sigmaTy (Γ := Γ)). apply setPairβ1. now apply HA.
  apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma cod_sigmaTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  cod_sigmaTy n (sigmaTy_HO n A B γ) ≡ typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩).
Proof.
  refine (trans (fequal (setSndPair (𝕌 n) (𝕍 n)) _) _).
  now apply (lbl_sigmaTy (Γ := Γ)). apply setPairβ2. now apply HA.
  apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma sigmaTy_HO_inj1 {n : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO n A B γ ≡ sigmaTy_HO n A' B' γ) : A γ ≡ A' γ.
Proof.
  refine (trans (b := dom_sigmaTy n (sigmaTy_HO n A B γ)) _ _).
  { symmetry. now apply (dom_sigmaTy_eq (Γ := Γ)). }
  refine (trans (fequal (dom_sigmaTy n) H) _). now apply (dom_sigmaTy_eq (Γ := Γ)).
Qed.

Lemma sigmaTy_HO_inj2' {n : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO n A B γ ≡ sigmaTy_HO n A' B' γ) :
  typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩) ≡ typeToGraph n (A γ) (fun a => B' ⟨ γ ; a ⟩).
Proof.
  pose proof (sigmaTy_HO_inj1 HA HB HA' HB' Hγ H) as HAA'.
  refine (trans (b := cod_sigmaTy n (sigmaTy_HO n A B γ)) _ _).
  symmetry. now apply (cod_sigmaTy_eq (Γ := Γ)). refine (trans (fequal (cod_sigmaTy n) H) _).
  refine (transpS (fun X => _ ≡ typeToGraph n X _) (sym HAA') _).
  now apply (cod_sigmaTy_eq (Γ := Γ)).
Qed.

Lemma sigmaTy_HO_inj2 {n : nat} {Γ γ a : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO n A B γ ≡ sigmaTy_HO n A' B' γ) (Ha : a ∈ 𝕌el n (A γ)) :
  B ⟨ γ ; a ⟩ ≡ B' ⟨ γ ; a ⟩.
Proof.
  pose proof (sigmaTy_HO_inj1 HA HB HA' HB' Hγ H) as HAA'.
  pose proof (sigmaTy_HO_inj2' HA HB HA' HB' Hγ H) as HBB'.
  refine (trans (b := setAppArr (𝕌el n (A γ)) (𝕌 n) (typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩)) a) _ _).
  { symmetry. refine (trans _ _). apply setAppArr_HO ; try assumption.
    now apply (typeExt_typing HA HB). reflexivity. }
  refine (trans (fequal (fun X => setAppArr (𝕌el n (A γ)) (𝕌 n) X a) HBB') _).
  refine (trans _ _). apply setAppArr_HO ; try assumption. 2:reflexivity.
  intros a' Ha'. pose proof (transpS (fun X => a' ∈ 𝕌el n X) HAA' Ha') as Ha''. cbn in Ha''. clear Ha'.
  revert a' Ha''. now apply (typeExt_typing HA' HB').
Qed.

(* Pairing *)

Definition pairTm_HO (n : nat) (t : ZFSet -> ZFSet) (u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ t γ ; u γ ⟩.

Lemma pairTm_HO_typing {n : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (B ⟨ γ ; t γ ⟩))
  : ∀ γ ∈ Γ, pairTm_HO n t u γ ∈ 𝕌el n (sigmaTy_HO n A B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_sigmaTy HA HB Hγ)) _). apply setMkSigma_typing.
  - intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Ht.
  - now apply Hu.
Qed.

(* First projection *)

Definition fstTm_HO (n : nat) (A B t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setFstSigma n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩)) (t γ).

Lemma fstTm_HO_typing {n : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (sigmaTy_HO n A B γ)) : ∀ γ ∈ Γ, fstTm_HO n A B t γ ∈ 𝕌el n (A γ).
Proof.
  intros γ Hγ. cbn. unfold fstTm_HO. apply setFstSigma_typing.
  - intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - refine (transpS (fun X => _ ∈ X) (el_sigmaTy HA HB Hγ) _). now apply Ht.
Qed.

(* Second projection *)

Definition sndTm_HO (n : nat) (A B t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setSndSigma n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩)) (t γ).

Lemma sndTm_HO_typing {n : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (sigmaTy_HO n A B γ)) : ∀ γ ∈ Γ, sndTm_HO n A B t γ ∈ 𝕌el n (B ⟨ γ ; fstTm_HO n A B t γ ⟩).
Proof.
  intros γ Hγ. cbn. unfold fstTm_HO. refine (transpS (fun X => _ ∈ X) _ _).
  2:{ apply setSndSigma_typing.
      - intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
      - refine (transpS (fun X => _ ∈ X) (el_sigmaTy HA HB Hγ) _). now apply Ht. }
  reflexivity.
Qed.

(* Equations (β and η) *)

Lemma sigmaTy_HO_β1 {n : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (B ⟨ γ ; t γ ⟩)) :
  ∀ γ ∈ Γ, fstTm_HO n A B (pairTm_HO n t u) γ ≡ t γ.
Proof.
  intros γ Hγ. cbn. apply setSigmaβ1.
  - intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Ht.
  - now apply Hu.
Qed.

Lemma sigmaTy_HO_β2 {n : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (B ⟨ γ ; t γ ⟩)) :
  ∀ γ ∈ Γ, sndTm_HO n A B (pairTm_HO n t u) γ ≡ u γ.
Proof.
  intros γ Hγ. cbn. apply setSigmaβ2.
  - intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Ht.
  - now apply Hu.
Qed.

Lemma sigmaTy_HO_η {n : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (sigmaTy_HO n A B γ)) :
  ∀ γ ∈ Γ, t γ ≡ pairTm_HO n (fstTm_HO n A B t) (sndTm_HO n A B t) γ.
Proof.
  intros γ Hγ. cbn. apply setSigmaη.
  - intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - refine (transpS (fun X => _ ∈ X) (el_sigmaTy HA HB Hγ) _). now apply Ht.
Qed.

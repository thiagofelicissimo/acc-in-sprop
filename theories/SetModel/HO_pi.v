Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO.

(* Pi types *)

Definition piTy_HO (n : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a))
           ; ⟨ ZFone ; typeTelescope2 n A B γ ⟩ ⟩.

Lemma piTy_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) :
  ∀ γ ∈ Γ, piTy_HO n A B γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setPi_typing.
    + apply 𝕌el_typing. now apply HA.
    + intros a Ha. apply 𝕌el_typing. now apply HB. 
  - apply setMkPair_typing.
    + apply one_typing.
    + now apply (typeTelescope2_typing n (Γ := Γ)).
Qed.

Lemma el_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌el n (piTy_HO n A B γ) ≡ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a)).
Proof.
  apply setPairβ1'. now apply (piTy_HO_typing n (Γ := Γ)).
Qed.

Lemma hd_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌hd n (piTy_HO n A B γ) ≡ ZFone.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply (piTy_HO_typing n (Γ := Γ)).
  apply setPairβ1. apply one_typing. now apply (typeTelescope2_typing n (Γ := Γ)).
Qed.  

Lemma lbl_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌lbl n (piTy_HO n A B γ) ≡ typeTelescope2 n A B γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply (piTy_HO_typing n (Γ := Γ)).
  apply setPairβ2. apply one_typing. now apply (typeTelescope2_typing n (Γ := Γ)).
Qed.

(* Injectivity of Pi types *)

Definition dom_piTy (n : nat) (x : ZFSet) :=
  setFstPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Definition cod_piTy (n : nat) (x : ZFSet) :=
  setSndPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Lemma dom_piTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  dom_piTy n (piTy_HO n A B γ) ≡ A γ.
Proof.
  refine (trans (fequal (setFstPair (𝕌 n) (𝕍 n)) _) _).
  now apply (lbl_piTy (Γ := Γ)). apply setPairβ1. now apply HA.
  apply typeToGraph_sorting. now apply HA. now apply HB.
Qed.

Lemma cod_piTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  cod_piTy n (piTy_HO n A B γ) ≡ typeToGraph n (A γ) (B γ).
Proof.
  refine (trans (fequal (setSndPair (𝕌 n) (𝕍 n)) _) _).
  now apply (lbl_piTy (Γ := Γ)). apply setPairβ2. now apply HA.
  apply typeToGraph_sorting. now apply HA. now apply HB.
Qed.

Lemma piTy_HO_inj1 (n : nat) {Γ γ : ZFSet} {A A' : ZFSet -> ZFSet} {B B' : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A' γ), B' γ a ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n A B γ ≡ piTy_HO n A' B' γ) : A γ ≡ A' γ.
Proof.
  refine (trans (b := dom_piTy n (piTy_HO n A B γ)) _ _).
  { symmetry. now apply (dom_piTy_eq (Γ := Γ)). }
  refine (trans (fequal (dom_piTy n) H) _). now apply (dom_piTy_eq (Γ := Γ)).
Qed.

Lemma piTy_HO_inj2' (n : nat) {Γ γ : ZFSet} {A A' : ZFSet -> ZFSet} {B B' : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A' γ), B' γ a ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n A B γ ≡ piTy_HO n A' B' γ) :
  typeToGraph n (A γ) (B γ) ≡ typeToGraph n (A γ) (B' γ).
Proof.
  pose proof (piTy_HO_inj1 n HA HB HA' HB' Hγ H) as HAA'.
  refine (trans (b := cod_piTy n (piTy_HO n A B γ)) _ _).
  symmetry. now apply (cod_piTy_eq (Γ := Γ)). refine (trans (fequal (cod_piTy n) H) _).
  refine (transpS (fun X => _ ≡ typeToGraph n X (B' γ)) (sym HAA') _).
  now apply (cod_piTy_eq (Γ := Γ)).
Qed.

Lemma piTy_HO_inj2 (n : nat) {Γ γ a : ZFSet} {A A' : ZFSet -> ZFSet} {B B' : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A' γ), B' γ a ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n A B γ ≡ piTy_HO n A' B' γ) (Ha : a ∈ 𝕌el n (A γ)) :
  B γ a ≡ B' γ a.
Proof.
  pose proof (piTy_HO_inj1 n HA HB HA' HB' Hγ H) as HAA'.
  pose proof (piTy_HO_inj2' n HA HB HA' HB' Hγ H) as HBB'.
  refine (trans (b := setAppArr (𝕌el n (A γ)) (𝕌 n) (typeToGraph n (A γ) (B γ)) a) _ _).
  { symmetry. apply setAppArr_HO. intros a' Ha'. now apply HB. assumption. }
  refine (trans (fequal (fun X => setAppArr (𝕌el n (A γ)) (𝕌 n) X a) HBB') _).
  apply setAppArr_HO. intros a' Ha'. apply HB' ; try assumption.
  refine (transpS (fun X => a' ∈ 𝕌el n X) HAA' _). assumption. assumption.
Qed.

(* Lambda abstraction *)

Definition lamTm_HO (n : nat) (A : ZFSet -> ZFSet) 
  (t : ZFSet -> ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => relToGraph (𝕌el n (A γ)) (𝕍 n) (HO_rel (t γ)).

Lemma lamTm_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  {t : ZFSet -> ZFSet -> ZFSet} (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), t γ a ∈ 𝕌el n (B γ a)) :
  ∀ γ ∈ Γ, lamTm_HO n A t γ ∈ 𝕌el n (piTy_HO n A B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_piTy HA HB Hγ)) _).
  apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing. intros a Ha.
    eapply ZFuniv_trans. now apply Ht. apply 𝕌el_typing. now apply HB.
  - intros a Ha. refine (transpS (fun X => X ∈ 𝕌el n (B γ a)) _ (Ht γ Hγ a Ha)).
    refine (sym _). apply setAppArr_HO ; [ | assumption].
    intros a' Ha'. eapply ZFuniv_trans. now apply Ht. apply 𝕌el_typing. now apply HB.
Qed.

(* Application *)

Definition appTm_HO (n : nat) (A : ZFSet -> ZFSet) 
  (t : ZFSet -> ZFSet) (u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setAppArr (𝕌el n (A γ)) (𝕍 n) (t γ) (u γ).

Lemma appTm_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  {t u : ZFSet -> ZFSet} (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (piTy_HO n A B γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, appTm_HO n A t u γ ∈ 𝕌el n (B γ (u γ)).
Proof.
  intros γ Hγ. assert (t γ ∈ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a))) as Htγ.
  { refine (transpS (fun X => t γ ∈ X) _ (Ht γ Hγ)). now apply (el_piTy (Γ := Γ)). }
  cbn. unfold appTm_HO. apply ZFincomp in Htγ. destruct Htγ as [ _ H ].
  apply H. now apply Hu.
Qed.

(* Equations (β and η) *)

Lemma piTy_HO_β (n : nat) {Γ : ZFSet} {A u : ZFSet -> ZFSet} {B t : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), t γ a ∈ 𝕌el n (B γ a)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, appTm_HO n A (lamTm_HO n A t) u γ ≡ t γ (u γ).
Proof.
  intros γ Hγ. cbn. apply setAppArr_HO.
  - intros a Ha. eapply ZFuniv_trans. now apply Ht. apply 𝕌el_typing. now apply HB.
  - now apply Hu.
Qed.

Lemma piTy_HO_η (n : nat) {Γ : ZFSet} {A t : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (piTy_HO n A B γ)) :
  ∀ γ ∈ Γ, t γ ≡ lamTm_HO n A (fun γ a => appTm_HO n A t (fun γ => a) γ) γ.
Proof.
  intros γ Hγ. cbn. unfold lamTm_HO. unfold appTm_HO.
  assert (t γ ∈ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a))) as Ht'.
  { refine (transpS (fun X => t γ ∈ X) (el_piTy HA HB Hγ) _). now apply Ht. }
  apply ZFincomp in Ht'. destruct Ht' as [ Ht' _ ].
  change (fun a : ZFSet => setAppArr (𝕌el n (A γ)) (𝕍 n) (t γ) a) with (setAppArr (𝕌el n (A γ)) (𝕍 n) (t γ)).
  apply (setArr_funext (A := 𝕌el n (A γ)) (B := 𝕍 n)).
  - exact Ht'.
  - apply relToGraph_typing. apply HO_rel_typing.
    intros a Ha. apply setAppArr_typing. 2:assumption. exact Ht'.
  - intros a Ha. refine (sym _). apply setAppArr_HO. 2:assumption. clear a Ha.
    intros a Ha. apply setAppArr_typing. 2:assumption. exact Ht'.
Qed.

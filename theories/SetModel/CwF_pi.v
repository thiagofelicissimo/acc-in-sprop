Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.
Require Import CwF.
Require Import CwF_library.

(* Pi types *)

Definition piTy_HO (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a))
           ; ⟨ ZFone ; typeTelescope2 n Γ A B γ ⟩ ⟩.

Definition piTy (n : nat) (Γ : ZFSet) (A : ZFSet) (B : ZFSet) : ZFSet :=
  HO_to_cwfTy n Γ (piTy_HO n Γ (cwfTy_to_HO n Γ A) (cwfTy_to_HO2 n Γ A B)).

Lemma piTy_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) :
  ∀ γ ∈ Γ, piTy_HO n Γ A B γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setPi_typing.
    + apply 𝕌el_typing. now apply HA.
    + intros a Ha. apply 𝕌el_typing. now apply HB. 
  - apply setMkPair_typing.
    + apply one_typing.
    + now apply typeTelescope2_typing.
Qed.

Lemma el_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌el n (piTy_HO n Γ A B γ) ≡ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a)).
Proof.
  apply setPairβ1'. now apply piTy_HO_typing.
Qed.

Lemma hd_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌hd n (piTy_HO n Γ A B γ) ≡ ZFone.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply piTy_HO_typing.
  apply setPairβ1. apply one_typing. now apply typeTelescope2_typing.
Qed.  

Lemma lbl_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌lbl n (piTy_HO n Γ A B γ) ≡ typeTelescope2 n Γ A B γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply piTy_HO_typing.
  apply setPairβ2. apply one_typing. now apply typeTelescope2_typing.
Qed.

Lemma cwfPi {n : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) :
  piTy n Γ A B ∈ cwfTy n Γ.
Proof.
  apply relToGraph_typing. apply HO_rel_typing. apply piTy_HO_typing.
  - now apply cwfTy_to_HO_typing.
  - intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
Qed.

Lemma cwfPi_to_HO {n : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) :
  ∀ γ ∈ Γ, cwfTy_to_HO n Γ (piTy n Γ A B) γ ≡ piTy_HO n Γ (cwfTy_to_HO n Γ A) (cwfTy_to_HO2 n Γ A B) γ.
Proof.
  intros γ Hγ. cbn. unfold piTy. apply setAppArr_HO.
  intros γ' Hγ'. apply piTy_HO_typing. now apply cwfTy_to_HO_typing.
  intros γ'' Hγ'' a Ha. now apply cwfTy_to_HO2_typing. assumption. assumption.
Qed.

(* Injectivity of Pi types *)

Definition dom_piTy (n : nat) (x : ZFSet) :=
  setFstPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Definition cod_piTy (n : nat) (x : ZFSet) :=
  setSndPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Lemma dom_piTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  dom_piTy n (piTy_HO n Γ A B γ) ≡ A γ.
Proof.
  refine (trans (fequal (setFstPair (𝕌 n) (𝕍 n)) _) _).
  now apply lbl_piTy. apply setPairβ1. now apply HA.
  apply HO_to_cwfTy_sorting. apply 𝕌el_typing. now apply HA. now apply HB.
Qed.

Lemma cod_piTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  cod_piTy n (piTy_HO n Γ A B γ) ≡ HO_to_cwfTy n (𝕌el n (A γ)) (B γ).
Proof.
  refine (trans (fequal (setSndPair (𝕌 n) (𝕍 n)) _) _).
  now apply lbl_piTy. apply setPairβ2. now apply HA.
  apply HO_to_cwfTy_sorting. apply 𝕌el_typing. now apply HA. now apply HB.
Qed.

Lemma piTy_HO_inj1 (n : nat) {Γ γ : ZFSet} {A A' : ZFSet -> ZFSet} {B B' : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A' γ), B' γ a ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n Γ A B γ ≡ piTy_HO n Γ A' B' γ) : A γ ≡ A' γ.
Proof.
  refine (trans (b := dom_piTy n (piTy_HO n Γ A B γ)) _ _).
  { symmetry. now apply dom_piTy_eq. }
  refine (trans (fequal (dom_piTy n) H) _). now apply dom_piTy_eq.
Qed.

Lemma piTy_HO_inj2' (n : nat) {Γ γ : ZFSet} {A A' : ZFSet -> ZFSet} {B B' : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A' γ), B' γ a ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n Γ A B γ ≡ piTy_HO n Γ A' B' γ) :
  HO_to_cwfTy n (𝕌el n (A γ)) (B γ) ≡ HO_to_cwfTy n (𝕌el n (A γ)) (B' γ).
Proof.
  pose proof (piTy_HO_inj1 n HA HB HA' HB' Hγ H) as HAA'.
  refine (trans (b := cod_piTy n (piTy_HO n Γ A B γ)) _ _).
  symmetry. now apply cod_piTy_eq. refine (trans (fequal (cod_piTy n) H) _).
  refine (transpS (fun X => _ ≡ HO_to_cwfTy n (𝕌el n X) (B' γ)) (sym HAA') _).
  now apply cod_piTy_eq.
Qed.

Lemma piTy_HO_inj2 (n : nat) {Γ γ a : ZFSet} {A A' : ZFSet -> ZFSet} {B B' : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A' γ), B' γ a ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n Γ A B γ ≡ piTy_HO n Γ A' B' γ) (Ha : a ∈ 𝕌el n (A γ)) :
  B γ a ≡ B' γ a.
Proof.
  pose proof (piTy_HO_inj1 n HA HB HA' HB' Hγ H) as HAA'.
  pose proof (piTy_HO_inj2' n HA HB HA' HB' Hγ H) as HBB'.
  refine (trans (b := setAppArr (𝕌el n (A γ)) (𝕌 n) (HO_to_cwfTy n (𝕌el n (A γ)) (B γ)) a) _ _).
  { symmetry. apply setAppArr_HO. intros a' Ha'. now apply HB. assumption. }
  refine (trans (fequal (fun X => setAppArr (𝕌el n (A γ)) (𝕌 n) X a) HBB') _).
  apply setAppArr_HO. intros a' Ha'. apply HB' ; try assumption.
  refine (transpS (fun X => a' ∈ 𝕌el n X) HAA' _). assumption. assumption.
Qed.

(* Lemma piTy_inj1' {n : nat} {Γ γ A B A' B' : ZFSet} *)
(*   (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) *)
(*   (HA' : A' ∈ cwfTy n Γ) (HB' : B' ∈ cwfTy n (ctxExt n Γ A')) *)
(*   (H : piTy n Γ A B ≡ piTy n Γ A' B') (Hγ : γ ∈ Γ) : *)
(*   setAppArr Γ (𝕌 n) A γ ≡ setAppArr Γ (𝕌 n) A' γ. *)
(* Proof. *)
(*   unshelve eapply (@piTy_HO_inj1 n Γ γ (cwfTy_to_HO n Γ A) (cwfTy_to_HO n Γ A') *)
(*                      (cwfTy_to_HO2 n Γ A B) (cwfTy_to_HO2 n Γ A' B') _ _ _ _ Hγ _). *)
(*   - intros. now apply cwfTy_to_HO_typing. *)
(*   - intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing. *)
(*   - intros. now apply cwfTy_to_HO_typing. *)
(*   - intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing. *)
(*   - unfold piTy in H. admit. *)
(* Admitted. *)

(* Lemma piTy_inj1 {n : nat} {Γ A B A' B' : ZFSet} *)
(*   (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) *)
(*   (HA' : A' ∈ cwfTy n Γ) (HB' : B' ∈ cwfTy n (ctxExt n Γ A')) *)
(*   (H : piTy n Γ A B ≡ piTy n Γ A' B') : A ≡ A'. *)
(* Proof. *)
(*   apply (setArr_funext HA HA'). intros γ Hγ. now apply (piTy_inj1' HA HB HA' HB' H Hγ). *)
(* Qed. *)

(* Lambda abstraction *)

Definition lamTm_HO (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) 
  (t : ZFSet -> ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => relToGraph (𝕌el n (A γ)) (𝕍 n) (HO_rel (t γ)).

Definition lamTm (n : nat) (Γ : ZFSet) (A : ZFSet) (t : ZFSet) : ZFSet :=
  HO_to_cwfTm n Γ (lamTm_HO n Γ (cwfTy_to_HO n Γ A) (cwfTm_to_HO2 n Γ A t)).

Lemma lamTm_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  {t : ZFSet -> ZFSet -> ZFSet} (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), t γ a ∈ 𝕌el n (B γ a)) :
  ∀ γ ∈ Γ, lamTm_HO n Γ A t γ ∈ 𝕌el n (piTy_HO n Γ A B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_piTy HA HB Hγ)) _).
  apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing. intros a Ha.
    eapply ZFuniv_trans. now apply Ht. apply 𝕌el_typing. now apply HB.
  - intros a Ha. refine (transpS (fun X => X ∈ 𝕌el n (B γ a)) _ (Ht γ Hγ a Ha)).
    refine (sym _). apply setAppArr_HO ; [ | assumption].
    intros a' Ha'. eapply ZFuniv_trans. now apply Ht. apply 𝕌el_typing. now apply HB.
Qed.

Lemma cwfLam {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A))
  (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) : lamTm n Γ A t ∈ cwfTm n Γ (piTy n Γ A B).
Proof.
  apply HO_to_cwfTm_typing.
  - apply piTy_HO_typing.
    + now apply cwfTy_to_HO_typing.
    + intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
  - intros γ Hγ. apply lamTm_HO_typing.
    + now apply cwfTy_to_HO_typing.
    + intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
    + intros γ' Hγ' a Ha. now apply cwfTm_to_HO2_typing.
    + assumption.
Qed.

Lemma cwfLam_to_HO {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A))
  (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) :
  ∀ γ ∈ Γ, cwfTm_to_HO n Γ (lamTm n Γ A t) γ ≡ lamTm_HO n Γ (cwfTy_to_HO n Γ A) (cwfTm_to_HO2 n Γ A t) γ.
Proof.
  intros γ Hγ. apply setAppArr_HO. 2:assumption. clear γ Hγ.
  intros γ Hγ. eapply ZFuniv_trans. apply (lamTm_HO_typing n (B := (cwfTy_to_HO2 n Γ A B))). 
  - intros γ' Hγ'. now apply cwfTy_to_HO_typing.
  - intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
  - intros γ' Hγ' a Ha. now apply cwfTm_to_HO2_typing.
  - assumption.
  - apply 𝕌el_typing. apply piTy_HO_typing.
    + intros γ' Hγ'. now apply cwfTy_to_HO_typing.
    + intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
    + assumption.
Qed.

(* Application *)

Definition appTm_HO (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) 
  (t : ZFSet -> ZFSet) (u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setAppArr (𝕌el n (A γ)) (𝕍 n) (t γ) (u γ).

Definition appTm (n : nat) (Γ : ZFSet) (A : ZFSet) (t : ZFSet) (u : ZFSet) : ZFSet :=
  HO_to_cwfTm n Γ (appTm_HO n Γ (cwfTy_to_HO n Γ A) (cwfTm_to_HO n Γ t) (cwfTm_to_HO n Γ u)).

Lemma appTm_HO_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  {t u : ZFSet -> ZFSet} (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (piTy_HO n Γ A B γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, appTm_HO n Γ A t u γ ∈ 𝕌el n (B γ (u γ)).
Proof.
  intros γ Hγ. assert (t γ ∈ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B γ a))) as Htγ.
  { refine (transpS (fun X => t γ ∈ X) _ (Ht γ Hγ)). now apply el_piTy. }
  cbn. unfold appTm_HO. apply ZFincomp in Htγ. destruct Htγ as [ _ H ].
  apply H. now apply Hu.
Qed.

Lemma cwfApp {n : nat} {Γ A B t u : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A))
  (Ht : t ∈ cwfTm n Γ (piTy n Γ A B)) (Hu : u ∈ cwfTm n Γ A) :
  appTm n Γ A t u ∈ cwfTm n Γ (cwfTy_reindex n (ctxExt n Γ A) B Γ (sgSub n Γ A u)).
Proof.
  assert (appTm n Γ A t u ∈ cwfTm n Γ (HO_to_cwfTy n Γ (fun γ => cwfTy_to_HO n (ctxExt n Γ A) B ⟨ γ ; cwfTm_to_HO n Γ u γ ⟩))).
  { apply HO_to_cwfTm_typing.
    - intros γ Hγ. apply cwfTy_to_HO_typing. assumption. apply setMkSigma_typing ; try assumption.
      intros γ' Hγ'. apply cwfTy_to_depSet_typing ; try assumption. 
      now apply cwfTm_to_HO_typing.
    - apply (appTm_HO_typing n (B := fun γ a => cwfTy_to_HO n (ctxExt n Γ A) B ⟨ γ; a ⟩)).
      + intros γ Hγ. now apply cwfTy_to_HO_typing.
      + intros γ Hγ a Ha. apply cwfTy_to_HO_typing. assumption. apply setMkSigma_typing ; try assumption.
        intros γ' Hγ'. apply cwfTy_to_depSet_typing ; try assumption.
      + intros γ Hγ. refine (transpS (fun X => _ ∈ 𝕌el n X) (cwfPi_to_HO HA HB γ Hγ) _).
        apply cwfTm_to_HO_typing. now apply cwfPi. assumption. assumption.
      + intros γ Hγ. now apply cwfTm_to_HO_typing. }
  refine (transpS (fun X => _ ∈ cwfTm n Γ X) (sym _) H).
  now apply cwfTy_reindex_sgSub.
Qed.

(* Equations (β and η) *)

Lemma piTy_HO_β (n : nat) {Γ : ZFSet} {A u : ZFSet -> ZFSet} {B t : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), t γ a ∈ 𝕌el n (B γ a)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, appTm_HO n Γ A (lamTm_HO n Γ A t) u γ ≡ t γ (u γ).
Proof.
  intros γ Hγ. cbn. apply setAppArr_HO.
  - intros a Ha. eapply ZFuniv_trans. now apply Ht. apply 𝕌el_typing. now apply HB.
  - now apply Hu.
Qed.

Lemma cwfPiβ {n : nat} {Γ A B t u : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A))
  (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) (Hu : u ∈ cwfTm n Γ A) :
  appTm n Γ A (lamTm n Γ A t) u ≡ cwfTm_reindex n (ctxExt n Γ A) t Γ (sgSub n Γ A u).
Proof.
  apply (setArr_funext (A := Γ) (B := 𝕍 n)).
  - assert (appTm n Γ A (lamTm n Γ A t) u ∈ cwfTm n Γ (cwfTy_reindex n (ctxExt n Γ A) B Γ (sgSub n Γ A u))).
    { apply (cwfApp HA HB). now apply cwfLam. assumption. }
    apply ZFincomp in H. destruct H as [ H _ ]. exact H.
  - assert (cwfTm_reindex n (ctxExt n Γ A) t Γ (sgSub n Γ A u) ∈ cwfTm n Γ (cwfTy_reindex n (ctxExt n Γ A) B Γ (sgSub n Γ A u))).
    { apply (cwfTm_reindex_typing HB Ht). now apply sgSub_typing. }
    apply ZFincomp in H. destruct H as [ H _ ]. exact H.
  - intros γ Hγ. refine (trans _ (sym (cwfTm_reindex_sgSub_app HA HB Ht Hu Hγ))).
    refine (trans _ _).
    { apply setAppArr_HO_to_cwfTm. 2:assumption. intros γ' Hγ'. eapply ZFuniv_trans.
      - clear γ Hγ. apply (appTm_HO_typing n (B := (cwfTy_to_HO2 n Γ A B))).
        + intros γ Hγ. now apply cwfTy_to_HO_typing.
        + intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
        + intros γ Hγ. refine (transpS (fun X => X ∈ _) (sym (cwfLam_to_HO HA HB Ht γ Hγ)) _).
          apply lamTm_HO_typing ; try assumption ; clear γ Hγ.
          * intros γ Hγ. now apply cwfTy_to_HO_typing.
          * intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
          * intros γ Hγ a Ha. now apply cwfTm_to_HO2_typing.
        + intros γ Hγ. now apply cwfTm_to_HO_typing.
        + assumption.
      - apply 𝕌el_typing. apply cwfTy_to_HO2_typing ; try assumption. now apply cwfTm_to_HO_typing. }
    refine (trans _ _).
    { refine (fequal (fun X => setAppArr (𝕌el n (cwfTy_to_HO n Γ A γ)) (𝕍 n) X (cwfTm_to_HO n Γ u γ)) _).
      apply (cwfLam_to_HO HA HB Ht γ Hγ). }
    refine (trans _ _).
    { apply setAppArr_HO.
      - intros a Ha. eapply ZFuniv_trans. now apply (cwfTm_to_HO2_typing HA HB).
        apply 𝕌el_typing. now apply cwfTy_to_HO2_typing.
      - now apply cwfTm_to_HO_typing. }
    reflexivity.
Qed.

Lemma piTy_HO_η (n : nat) {Γ : ZFSet} {A t : ZFSet -> ZFSet} {B : ZFSet -> ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, ∀ a ∈ 𝕌el n (A γ), B γ a ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (piTy_HO n Γ A B γ)) :
  ∀ γ ∈ Γ, t γ ≡ lamTm_HO n Γ A (fun γ a => appTm_HO n Γ A t (fun γ => a) γ) γ.
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

Lemma cwfPiη_aux {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Ht : t ∈ cwfTm n Γ (piTy n Γ A B)) :
  appTm n (ctxExt n Γ A) (cwfTy_reindex n Γ A (ctxExt n Γ A) (ctxWk n Γ A))
    (cwfTm_reindex n Γ t (ctxExt n Γ A) (ctxWk n Γ A)) (ctxVar0 n Γ A) ∈ cwfTm n (ctxExt n Γ A) B.
Proof.
  refine (transpS (fun X => _ ∈ X) _ _).
  2: { apply (cwfApp (B := (cwfTy_reindex n (ctxExt n Γ A) B
                              (ctxExt n (ctxExt n Γ A) (cwfTy_reindex n Γ A (ctxExt n Γ A) (ctxWk n Γ A)))
                              (ctxWk1 n n Γ A A)))).
       - apply cwfTy_reindex_typing. assumption. now apply ctxWk_typing.
       - apply cwfTy_reindex_typing. assumption. now apply ctxWk1_typing.
       - admit. (* need the Π-cong equation, urgh *)
       - now apply ctxVar0_typing. }
  refine (fequal (cwfTm n (ctxExt n Γ A)) _).
  refine (trans (sym _) _).
  { apply cwfTy_reindex_comp. assumption. now apply ctxWk1_typing.
    apply sgSub_typing. apply cwfTy_reindex_typing. assumption. now apply ctxWk_typing. now apply ctxVar0_typing. }
  refine (trans (b := cwfTy_reindex n (ctxExt n Γ A) B (ctxExt n Γ A) (cwfId (ctxExt n Γ A))) _ _).
  - refine (fequal (cwfTy_reindex n (ctxExt n Γ A) B (ctxExt n Γ A)) _). admit. (* some substitution calculus silliness *)
  - apply cwfTy_reindex_id. assumption.
Admitted.

Lemma cwfPiη {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Ht : t ∈ cwfTm n Γ (piTy n Γ A B)) :
  t ≡ lamTm n Γ A
        (appTm n (ctxExt n Γ A)
                 (cwfTy_reindex n Γ A (ctxExt n Γ A) (ctxWk n Γ A)) 
                 (cwfTm_reindex n Γ t (ctxExt n Γ A) (ctxWk n Γ A)) 
                 (ctxVar0 n Γ A)).
Proof.
  apply (setArr_funext (A := Γ) (B := 𝕍 n)).
  - apply ZFincomp in Ht. destruct Ht as [ H _ ]. exact H.
  - assert (lamTm n Γ A
              (appTm n (ctxExt n Γ A)
                 (cwfTy_reindex n Γ A (ctxExt n Γ A) (ctxWk n Γ A)) 
                 (cwfTm_reindex n Γ t (ctxExt n Γ A) (ctxWk n Γ A)) 
                 (ctxVar0 n Γ A)) ∈ cwfTm n Γ (piTy n Γ A B)).
    { apply cwfLam ; try assumption. now apply cwfPiη_aux. }
    apply ZFincomp in H. destruct H as [ H _ ]. exact H.
  - intros γ Hγ. refine (sym (trans _ _)).
    { apply setAppArr_HO. 2:assumption. clear γ Hγ.
      intros γ Hγ. eapply ZFuniv_trans. apply (lamTm_HO_typing n (B := (cwfTy_to_HO2 n Γ A B))) ; try assumption ; clear γ Hγ.
      - intros γ Hγ. now apply cwfTy_to_HO_typing.
      - intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
      - intros γ Hγ a Ha. apply cwfTm_to_HO2_typing ; try assumption. now apply cwfPiη_aux.
      - apply 𝕌el_typing. apply piTy_HO_typing.
        + intros γ' Hγ'. now apply cwfTy_to_HO_typing.
        + intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
        + assumption. }

    (* doable but nightmare-inducing *)
    apply (setArr_funext (A := 𝕌el n (cwfTy_to_HO n Γ A γ)) (B := 𝕍 n)).
    + admit.
    + admit.
    + intros a Ha. refine (trans _ _).
      { apply setAppArr_HO. 2:assumption. clear a Ha. intros a Ha. eapply ZFuniv_trans.
        apply (cwfTm_to_HO2_typing (B := B)) ; try assumption. 2: apply 𝕌el_typing ; now apply cwfTy_to_HO2_typing.
        admit. }
      refine (trans _ _).
      { apply setAppArr_HO.
        - intros γa Hγa. admit.
        - apply setMkSigma_typing ; try assumption. intros γ' Hγ'. now apply cwfTy_to_depSet_typing. }
      unfold appTm_HO. unfold cwfTm_to_HO.
      (* and now it's just a bit of substitution calculs... fun fun fun! *)
Admitted.

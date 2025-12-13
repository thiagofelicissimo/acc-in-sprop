Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO.

(* Pi types *)

Definition piTy_HO (n : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩))
           ; ⟨ ZFone ; typeTelescope2 n A B γ ⟩ ⟩.

Lemma piTy_HO_typing {n : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) :
  ∀ γ ∈ Γ, piTy_HO n A B γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setPi_typing.
    + apply 𝕌el_typing. now apply HA.
    + intros a Ha. apply 𝕌el_typing. now apply (typeExt_typing HA HB). 
  - apply setMkPair_typing.
    + apply one_typing.
    + apply (typeTelescope2_typing n (Γ := Γ)) ; try assumption. 
Qed.

Lemma el_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌el n (piTy_HO n A B γ) ≡ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩)).
Proof.
  apply setPairβ1'. now apply (piTy_HO_typing (Γ := Γ)).
Qed.

Lemma hd_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌hd n (piTy_HO n A B γ) ≡ ZFone.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply (piTy_HO_typing (Γ := Γ)).
  apply setPairβ1. apply one_typing. apply (typeTelescope2_typing n (Γ := Γ)) ; try assumption.
Qed.  

Lemma lbl_piTy {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  𝕌lbl n (piTy_HO n A B γ) ≡ typeTelescope2 n A B γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _).
  apply setPairβ2'. now apply (piTy_HO_typing (Γ := Γ)).
  apply setPairβ2. apply one_typing. apply (typeTelescope2_typing n (Γ := Γ)) ; try assumption.
Qed.

(* Injectivity of Pi types *)

Definition dom_piTy (n : nat) (x : ZFSet) :=
  setFstPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Definition cod_piTy (n : nat) (x : ZFSet) :=
  setSndPair (𝕌 n) (𝕍 n) (𝕌lbl n x).

Lemma dom_piTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  dom_piTy n (piTy_HO n A B γ) ≡ A γ.
Proof.
  refine (trans (fequal (setFstPair (𝕌 n) (𝕍 n)) _) _).
  now apply (lbl_piTy (Γ := Γ)). apply setPairβ1. now apply HA.
  apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma cod_piTy_eq {n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n) (Hγ : γ ∈ Γ) :
  cod_piTy n (piTy_HO n A B γ) ≡ typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩).
Proof.
  refine (trans (fequal (setSndPair (𝕌 n) (𝕍 n)) _) _).
  now apply (lbl_piTy (Γ := Γ)). apply setPairβ2. now apply HA.
  apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma piTy_HO_inj1 {n : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n A B γ ≡ piTy_HO n A' B' γ) : A γ ≡ A' γ.
Proof.
  refine (trans (b := dom_piTy n (piTy_HO n A B γ)) _ _).
  { symmetry. now apply (dom_piTy_eq (Γ := Γ)). }
  refine (trans (fequal (dom_piTy n) H) _). now apply (dom_piTy_eq (Γ := Γ)).
Qed.

Lemma piTy_HO_inj2' {n : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n A B γ ≡ piTy_HO n A' B' γ) :
  typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩) ≡ typeToGraph n (A γ) (fun a => B' ⟨ γ ; a ⟩).
Proof.
  pose proof (piTy_HO_inj1 HA HB HA' HB' Hγ H) as HAA'.
  refine (trans (b := cod_piTy n (piTy_HO n A B γ)) _ _).
  symmetry. now apply (cod_piTy_eq (Γ := Γ)). refine (trans (fequal (cod_piTy n) H) _).
  refine (transpS (fun X => _ ≡ typeToGraph n X _) (sym HAA') _).
  now apply (cod_piTy_eq (Γ := Γ)).
Qed.

Lemma piTy_HO_inj2 {n : nat} {Γ γ a : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (Hγ : γ ∈ Γ) (H : piTy_HO n A B γ ≡ piTy_HO n A' B' γ) (Ha : a ∈ 𝕌el n (A γ)) :
  B ⟨ γ ; a ⟩ ≡ B' ⟨ γ ; a ⟩.
Proof.
  pose proof (piTy_HO_inj1 HA HB HA' HB' Hγ H) as HAA'.
  pose proof (piTy_HO_inj2' HA HB HA' HB' Hγ H) as HBB'.
  refine (trans (b := setAppArr (𝕌el n (A γ)) (𝕌 n) (typeToGraph n (A γ) (fun a => B ⟨ γ ; a ⟩)) a) _ _).
  { symmetry. refine (trans _ _). apply setAppArr_HO ; try assumption.
    now apply (typeExt_typing HA HB). reflexivity. }
  refine (trans (fequal (fun X => setAppArr (𝕌el n (A γ)) (𝕌 n) X a) HBB') _).
  refine (trans _ _). apply setAppArr_HO ; try assumption. 2:reflexivity.
  intros a' Ha'. pose proof (transpS (fun X => a' ∈ 𝕌el n X) HAA' Ha') as Ha''. cbn in Ha''. clear Ha'.
  revert a' Ha''. now apply (typeExt_typing HA' HB').
Qed.

(* Lambda abstraction *)

Definition lamTm_HO (n : nat) (A t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => relToGraph (𝕌el n (A γ)) (𝕍 n) (HO_rel (fun a => t ⟨ γ ; a ⟩)).

Lemma lamTm_HO_typing (n : nat) {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γa ∈ ctxExt n Γ A, t γa ∈ 𝕌el n (B γa)) :
  ∀ γ ∈ Γ, lamTm_HO n A t γ ∈ 𝕌el n (piTy_HO n A B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_piTy HA HB Hγ)) _). apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing.
    intros a Ha. eapply ZFuniv_trans. now apply (termExt_typing HA HB Ht).
    apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - intros a Ha. refine (transpS (fun X => X ∈ 𝕌el n (B ⟨ γ ; a ⟩)) _ (Ht ⟨ γ ; a ⟩ _)).
    + refine (sym _). refine (trans _ _). apply setAppArr_HO ; [ | assumption].
      intros a' Ha'. eapply ZFuniv_trans. now apply (termExt_typing HA HB Ht). apply 𝕌el_typing.
      now apply (typeExt_typing HA HB). reflexivity.
    + apply setMkSigma_typing ; try assumption. intros γ' Hγ'. apply 𝕌el_typing. now apply HA.
Qed.

(* Application *)

Definition appTm_HO (n : nat) (A t u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setAppArr (𝕌el n (A γ)) (𝕍 n) (t γ) (u γ).

Lemma appTm_HO_typing (n : nat) {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (piTy_HO n A B γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, appTm_HO n A t u γ ∈ 𝕌el n (B ⟨ γ ; u γ ⟩).
Proof.
  intros γ Hγ. assert (t γ ∈ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩))) as Htγ.
  { refine (transpS (fun X => t γ ∈ X) _ (Ht γ Hγ)). now apply (el_piTy (Γ := Γ)). }
  cbn. unfold appTm_HO. apply ZFincomp in Htγ. destruct Htγ as [ _ H ].
  apply H. now apply Hu.
Qed.

(* Equations (β and η) *)

Lemma piTy_HO_β (n : nat) {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γa ∈ ctxExt n Γ A, t γa ∈ 𝕌el n (B γa)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, appTm_HO n A (lamTm_HO n A t) u γ ≡ t ⟨ γ ; u γ ⟩.
Proof.
  intros γ Hγ. cbn. refine (trans _ _). apply setAppArr_HO ; try assumption. 3:reflexivity.
  - intros a Ha. eapply ZFuniv_trans. now apply (termExt_typing HA HB Ht). apply 𝕌el_typing.
    now apply (typeExt_typing HA HB).
  - now apply Hu.
Qed.

(* Γ ⊢ t : Π A B *)

(* Γ , A ⊢ wk t : Π (wk A) (wk1 B) *)
(* Γ , A ⊢ 0 : wk A *)
(* Γ , A ⊢ (wk t) @ 0 : wk1 B [ 0 ] = B *)
(* Γ ⊢ λ (wk t) @ 0 : Π A B *)

Lemma piTy_HO_η (n : nat) {Γ : ZFSet} {A B t u : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (piTy_HO n A B γ)) :
  ∀ γ ∈ Γ, t γ ≡ lamTm_HO n A (fun γa => appTm_HO n (fun γa => A (ctx_wk n Γ A γa)) (fun γa => t (ctx_wk n Γ A γa)) (ctx_var0 n Γ A) γa) γ.
Proof.
  intros γ Hγ. cbn. unfold lamTm_HO. unfold appTm_HO.
  assert (t γ ∈ setPi n (𝕌el n (A γ)) (fun a => 𝕌el n (B ⟨ γ ; a ⟩))) as Ht'.
  { refine (transpS (fun X => t γ ∈ X) (el_piTy HA HB Hγ) _). now apply Ht. }
  apply ZFincomp in Ht'. destruct Ht' as [ Ht' _ ].
  apply (setArr_funext (A := 𝕌el n (A γ)) (B := 𝕍 n)).
  - exact Ht'.
  - apply relToGraph_typing. apply HO_rel_typing. intros a Ha.
    refine (transp2S (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (t X) Y ∈ 𝕍 n)
              (sym (ctxExtβ1 HA Hγ Ha)) (sym (ctxExtβ2 HA Hγ Ha)) _).
    apply setAppArr_typing. 2:assumption. exact Ht'.
  - intros a Ha. refine (sym _). refine (trans _ _). apply setAppArr_HO. 2:assumption.
    + clear a Ha. intros a Ha. 
      refine (transp2S (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (t X) Y ∈ 𝕍 n)
                (sym (ctxExtβ1 HA Hγ Ha)) (sym (ctxExtβ2 HA Hγ Ha)) _).
      apply setAppArr_typing. 2:assumption. exact Ht'.
    + refine (fequal2 (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (t X) Y)
                ((ctxExtβ1 HA Hγ Ha)) ((ctxExtβ2 HA Hγ Ha))).
Qed.

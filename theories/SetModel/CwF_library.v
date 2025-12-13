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

Definition cwfTm_to_HO (n : nat) (Γ t : ZFSet) :=
  fun γ => setAppArr Γ (𝕍 n) t γ.

Definition cwfTm_to_HO2 (n : nat) (Γ A t : ZFSet) :=
  fun γ a => setAppArr (ctxExt n Γ A) (𝕍 n) t ⟨ γ ; a ⟩.

Lemma cwfTy_to_HO_typing {n : nat} {Γ A : ZFSet} (HA : A ∈ cwfTy n Γ) : ∀ γ ∈ Γ, cwfTy_to_HO n Γ A γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. now apply setAppArr_typing.
Qed.

Lemma cwfTy_to_HO2_typing {n : nat} {Γ A B γ a : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Hγ : γ ∈ Γ) (Ha : a ∈ 𝕌el n (cwfTy_to_HO n Γ A γ)) :
  cwfTy_to_HO2 n Γ A B γ a ∈ 𝕌 n.
Proof.
  apply setAppArr_typing. assumption.
  apply setMkSigma_typing.
  - clear γ Hγ a Ha. intros γ Hγ. now apply cwfTy_to_depSet_typing.
  - assumption.
  - assumption.
Qed.

Lemma cwfTm_to_HO_typing {n : nat} {Γ A t : ZFSet} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) :
  ∀ γ ∈ Γ, cwfTm_to_HO n Γ t γ ∈ 𝕌el n (cwfTy_to_HO n Γ A γ).
Proof.
  intros γ Hγ. now apply cwfTm_app.
Qed.

Lemma cwfTm_to_HO_sorting {n : nat} {Γ A t : ZFSet} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) :
  ∀ γ ∈ Γ, cwfTm_to_HO n Γ t γ ∈ 𝕍 n.
Proof.
  intros γ Hγ. eapply ZFuniv_trans. apply (cwfTm_to_HO_typing HA Ht γ Hγ).
  apply 𝕌el_typing. now apply cwfTy_to_HO_typing.
Qed.

Lemma cwfTm_to_HO2_typing {n : nat} {Γ A B t γ a : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Ht : t ∈ cwfTm n (ctxExt n Γ A) B)
  (Hγ : γ ∈ Γ) (Ha : a ∈ 𝕌el n (cwfTy_to_HO n Γ A γ)) :
  cwfTm_to_HO2 n Γ A t γ a ∈ 𝕌el n (cwfTy_to_HO2 n Γ A B γ a).
Proof.
  apply cwfTm_app. assumption. assumption.
  apply setMkSigma_typing ; try assumption. intros γ' Hγ'.
  now apply cwfTy_to_depSet_typing.
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

Lemma HO_to_cwfTy_typing (n : nat) {Γ : ZFSet} {A : ZFSet -> ZFSet} (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n)
  : HO_to_cwfTy n Γ A ∈ cwfTy n Γ.
Proof.
  apply relToGraph_typing. apply HO_rel_typing. assumption.
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

(* Single substitution *)

Definition sgSub (n : nat) (Γ A t : ZFSet) :=
  subExt n Γ A Γ (cwfId Γ) t.

Lemma sgSub_typing {n : nat} {Γ A t : ZFSet} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) :
  sgSub n Γ A t ∈ cwfSub Γ (ctxExt n Γ A).
Proof.
  apply subExt_typing. assumption. apply cwfId_typing.
  refine (transpS (fun X => t ∈ cwfTm n Γ X) (sym _) Ht). now apply cwfTy_reindex_id.
Qed.

Lemma cwfTy_reindex_subExt_app {n : nat} {Γ Δ A B t σ δ : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Hσ : σ ∈ cwfSub Δ Γ) (Ht : t ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ)) (Hδ : δ ∈ Δ) :
  setAppArr Δ (𝕌 n) (cwfTy_reindex n (ctxExt n Γ A) B Δ (subExt n Γ A Δ σ t)) δ
    ≡ cwfTy_to_HO n (ctxExt n Γ A) B ⟨ setAppArr Δ Γ σ δ ; cwfTm_to_HO n Δ t δ ⟩.
Proof.
  refine (trans _ _).
  { apply app_cwfTy_reindex ; try assumption. now apply subExt_typing. }
  refine (trans (fequal (setAppArr (ctxExt n Γ A) (𝕌 n) B) _) (sym _)).
  { apply setAppArr_HO ; [ | assumption ]. intros δ' Hδ'. apply subExt_HO_typing ; try assumption. }
  reflexivity.
Qed.

Lemma cwfTy_reindex_subExt' {n : nat} {Γ Δ A B t σ : ZFSet} {f : ZFSet -> ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Hσ : σ ∈ cwfSub Δ Γ) (Ht : t ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ))
  (Hf : ∀ δ ∈ Δ, f δ ≡ setAppArr Δ Γ σ δ) :
  cwfTy_reindex n (ctxExt n Γ A) B Δ (subExt n Γ A Δ σ t)
    ≡ HO_to_cwfTy n Δ (fun δ => cwfTy_to_HO n (ctxExt n Γ A) B ⟨ f δ ; cwfTm_to_HO n Δ t δ ⟩).
Proof.
  apply (setArr_funext (A := Δ) (B := 𝕌 n)).
  - apply cwfTy_reindex_typing. assumption. now apply subExt_typing.
  - apply HO_to_cwfTy_typing. intros δ Hδ. apply cwfTy_to_HO_typing. assumption.
    refine (transpS (fun X => ⟨ X ; _ ⟩ ∈ _) (sym (Hf δ Hδ)) _).
    apply setMkSigma_typing. now apply cwfTy_to_depSet_typing. now apply setAppArr_typing.
    refine (transpS (fun X => _ ∈ X) (cwfTy_reindex_to_depSet HA Hσ Hδ) _).
    apply cwfTm_to_HO_typing ; try assumption. now apply cwfTy_reindex_typing.
  - intros δ Hδ. refine (trans _ (sym _)).
    { apply cwfTy_reindex_subExt_app ; try assumption. } 
    refine (trans _ _).
    { apply (setAppArr_HO (f := (fun δ0 : ZFSet => cwfTy_to_HO n (ctxExt n Γ A) B ⟨ f δ0; cwfTm_to_HO n Δ t δ0 ⟩))).
      2:assumption. intros δ' Hδ'. apply cwfTy_to_HO_typing. assumption.
      refine (transpS (fun X => ⟨ X ; _ ⟩ ∈ _) (sym (Hf δ' Hδ')) _). apply setMkSigma_typing.
      + now apply cwfTy_to_depSet_typing.
      + now apply setAppArr_typing. 
      + refine (transpS (fun X => _ ∈ X) (cwfTy_reindex_to_depSet HA Hσ Hδ') _).
        apply cwfTm_to_HO_typing ; try assumption. now apply cwfTy_reindex_typing. }
    refine (transpS (fun X => cwfTy_to_HO n (ctxExt n Γ A) B ⟨ X ; _ ⟩ ≡ _) (sym (Hf δ Hδ)) _). reflexivity.
Qed.

Lemma cwfTy_reindex_sgSub {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Ht : t ∈ cwfTm n Γ A) :
  cwfTy_reindex n (ctxExt n Γ A) B Γ (sgSub n Γ A t)
    ≡ HO_to_cwfTy n Γ (fun γ => cwfTy_to_HO n (ctxExt n Γ A) B ⟨ γ; cwfTm_to_HO n Γ t γ ⟩).
Proof.
  apply cwfTy_reindex_subExt' ; try assumption.
  - apply cwfId_typing.
  - refine (transpS (fun X => t ∈ cwfTm n Γ X) (sym _) Ht). now apply cwfTy_reindex_id.
  - intros γ Hγ. refine (sym _). now apply setIdArr_app. 
Qed.

Lemma cwfTm_reindex_subExt_app {n : nat} {Γ Δ A B t u σ δ : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) (Hσ : σ ∈ cwfSub Δ Γ)
  (Hu : u ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ)) (Hδ : δ ∈ Δ) :
  setAppArr Δ (𝕍 n) (cwfTm_reindex n (ctxExt n Γ A) t Δ (subExt n Γ A Δ σ u)) δ
    ≡ cwfTm_to_HO n (ctxExt n Γ A) t ⟨ setAppArr Δ Γ σ δ ; cwfTm_to_HO n Δ u δ ⟩.
Proof.
  refine (trans _ _).
  { apply (app_cwfTm_reindex HB) ; try assumption. now apply subExt_typing. }
  refine (trans (fequal (setAppArr (ctxExt n Γ A) (𝕍 n) t) _) (sym _)).
  { apply setAppArr_HO ; [ | assumption ]. intros δ' Hδ'. apply subExt_HO_typing ; try assumption. }
  reflexivity.
Qed.

Lemma cwfTm_reindex_sgSub_app {n : nat} {Γ A B t u γ : ZFSet} (HA : A ∈ cwfTy n Γ)
  (HB : B ∈ cwfTy n (ctxExt n Γ A)) (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) (Hu : u ∈ cwfTm n Γ A) (Hγ : γ ∈ Γ) :
  setAppArr Γ (𝕍 n) (cwfTm_reindex n (ctxExt n Γ A) t Γ (sgSub n Γ A u)) γ
    ≡ cwfTm_to_HO n (ctxExt n Γ A) t ⟨ γ; cwfTm_to_HO n Γ u γ ⟩.
Proof.
  refine (trans _ _).
  { apply (cwfTm_reindex_subExt_app HA HB) ; try assumption.
    - apply cwfId_typing.
    - refine (transpS (fun X => u ∈ cwfTm n Γ X) (sym _) Hu). now apply cwfTy_reindex_id. }
  refine (fequal (fun X => cwfTm_to_HO n (ctxExt n Γ A) t ⟨ X ; cwfTm_to_HO n Γ u γ ⟩) _).
  now apply setIdArr_app. 
Qed.

(* weakening the second-to-last variable *)

Definition ctxWk1_HO (nA nB : nat) (Γ A B : ZFSet) : ZFSet -> ZFSet :=
  fun γab => ⟨ setFstSigma nA Γ (cwfTy_to_depSet nA Γ A)
                 (setFstSigma nB (ctxExt nA Γ A) 
                    (cwfTy_to_depSet nB (ctxExt nA Γ A) (cwfTy_reindex nB Γ B (ctxExt nA Γ A) (ctxWk nA Γ A)))
                    γab)
             ; setSndSigma nB (ctxExt nA Γ A) (cwfTy_to_depSet nB (ctxExt nA Γ A) (cwfTy_reindex nB Γ B (ctxExt nA Γ A) (ctxWk nA Γ A))) γab ⟩.

Definition ctxWk1 (nA nB : nat) (Γ A B : ZFSet) :=
  relToGraph (ctxExt nB (ctxExt nA Γ A) (cwfTy_reindex nB Γ B (ctxExt nA Γ A) (ctxWk nA Γ A))) (ctxExt nB Γ B) (HO_rel (ctxWk1_HO nA nB Γ A B)).

Lemma ctxWk1_HO_typing {nA nB : nat} {Γ A B γab : ZFSet} (HA : A ∈ cwfTy nA Γ) (HB : B ∈ cwfTy nB Γ)
  (Hγab : γab ∈ ctxExt nB (ctxExt nA Γ A) (cwfTy_reindex nB Γ B (ctxExt nA Γ A) (ctxWk nA Γ A))) :
  ctxWk1_HO nA nB Γ A B γab ∈ ctxExt nB Γ B.
Proof.
  apply setMkSigma_typing.
  - intros γ Hγ. now apply cwfTy_to_depSet_typing.
  - apply setFstSigma_typing.
    + intros γ Hγ. now apply cwfTy_to_depSet_typing.
    + apply setFstSigma_typing.
      * intros γ Hγ. apply cwfTy_to_depSet_typing. 2:assumption. apply cwfTy_reindex_typing.
        assumption. now apply ctxWk_typing.
      * exact Hγab.
  - refine (transpS (fun X => _ ∈ X) _ _).
    2: { apply setSndSigma_typing.
         - intros γa Hγa. apply cwfTy_to_depSet_typing. 2:assumption. apply cwfTy_reindex_typing.
           assumption. now apply ctxWk_typing.
         -  exact Hγab. }
    refine (trans _ _).
    { apply cwfTy_reindex_to_depSet. assumption. now apply ctxWk_typing.
      apply setFstSigma_typing. 2:assumption. intros γa Hγa. apply cwfTy_to_depSet_typing.
      2:assumption. apply cwfTy_reindex_typing. assumption. now apply ctxWk_typing. }
    refine (fequal (cwfTy_to_depSet nB Γ B) _). apply setAppArr_HO.
    + intros γa Hγa. apply setFstSigma_typing. 2:assumption. intros γ Hγ. now apply cwfTy_to_depSet_typing.
    + apply setFstSigma_typing. 2:assumption. intros γa Hγa.
      apply cwfTy_to_depSet_typing. 2:assumption. apply cwfTy_reindex_typing. assumption.
      now apply ctxWk_typing.
Qed.
        
Lemma ctxWk1_typing {nA nB : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy nA Γ) (HB : B ∈ cwfTy nB Γ) :
  ctxWk1 nA nB Γ A B ∈ cwfSub (ctxExt nB (ctxExt nA Γ A) (cwfTy_reindex nB Γ B (ctxExt nA Γ A) (ctxWk nA Γ A))) (ctxExt nB Γ B).
Proof.
  apply relToGraph_typing. apply HO_rel_typing.
  intros γab Hγab. now apply ctxWk1_HO_typing.
Qed.

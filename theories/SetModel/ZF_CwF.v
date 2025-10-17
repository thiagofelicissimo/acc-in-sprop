Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.

(* We define a CwF that supports all the type formers and operations of CICobs *)

(* Underlying category *)

Definition cwfCon := ZFSet.
Definition cwfSub (Γ Δ : ZFSet) := Γ ⇒ Δ.
Definition cwfId (Γ : ZFSet) := setIdArr Γ.
Definition cwfComp (Γ Δ Θ σ τ : ZFSet) := setCompArr Θ Δ Γ τ σ.

Lemma cwfId_typing (Γ : ZFSet) : cwfId Γ ∈ cwfSub Γ Γ.
Proof.
  exact (setIdArr_typing Γ).
Qed.

Lemma cwfComp_typing {Γ Δ Θ σ τ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) (Hτ : τ ∈ cwfSub Θ Δ) : cwfComp Γ Δ Θ σ τ ∈ cwfSub Θ Γ.
Proof.
  exact (setCompArr_typing Hτ Hσ).
Qed.

Lemma cwfCompId_right {Γ Δ σ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) : cwfComp Γ Δ Δ σ (cwfId Δ) ≡ σ.
Proof.
  exact (setCompId_left Hσ).
Qed.

Lemma cwfCompId_left {Γ Δ σ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) : cwfComp Γ Γ Δ (cwfId Γ) σ ≡ σ.
Proof.
  exact (setCompId_right Hσ).
Qed.

Lemma cwfCompAssoc {Γ Δ Θ Ξ σ τ υ : ZFSet} (Hσ : σ ∈ cwfSub Δ Γ) (Hτ : τ ∈ cwfSub Θ Δ) (Hυ : υ ∈ cwfSub Ξ Θ) :
  cwfComp Γ Δ Ξ σ (cwfComp Δ Θ Ξ τ υ) ≡ cwfComp Γ Θ Ξ (cwfComp Γ Δ Θ σ τ) υ.
Proof.
  exact (sym (setCompAssoc Hυ Hτ Hσ)).
Qed.

(* Terminal object *)

Definition cwfEmpty : ZFSet := setSingl ∅.
Definition cwfSubEmpty (Γ : ZFSet) : ZFSet := Γ × cwfEmpty.

Lemma cwfSubEmpty_typing (Γ : ZFSet) : cwfSubEmpty Γ ∈ cwfSub Γ cwfEmpty.
Proof.
  apply ZFincomp. split.
  - apply ZFinpower. intros x Hx. exact Hx.
  - assert (∅ ∈ cwfEmpty) as H. { apply inSetSingl. reflexivity. }
    intros γ Hγ. exists ∅. split.
    + split. exact H. exact (setMkPair_typing Hγ H).
    + intros x [ Hx _ ]. apply inSetSingl in Hx. exact (sym Hx).
Qed.

Lemma cwfSubEmpty_unique {Γ σ : ZFSet} (Hσ : σ ∈ cwfSub Γ cwfEmpty) : σ ≡ cwfSubEmpty Γ.
Proof.
  apply (setArr_funext Hσ (cwfSubEmpty_typing Γ)). intros γ Hγ.
  pose proof (setAppArr_typing Hσ Hγ) as H1. apply inSetSingl in H1. refine (trans H1 _).
  pose proof (setAppArr_typing (cwfSubEmpty_typing Γ) Hγ) as H2. apply inSetSingl in H2. exact (sym H2).
Qed.

(* Presheaf of types *)

Definition cwfTy (n : nat) (Γ : ZFSet) := Γ ⇒ (𝕍 n × 𝕍 n).

Definition cwfTy_reindex (n : nat) (Γ A Δ σ : ZFSet) := setCompArr Δ Γ (𝕍 n × 𝕍 n) σ A.

Definition cwfTy_to_depSet (n : nat) (Γ A : ZFSet) : ZFSet -> ZFSet :=
  fun γ => setFstPair (𝕍 n) (𝕍 n) (setAppArr Γ (𝕍 n × 𝕍 n) A γ).

Lemma cwfTy_reindex_typing {n : nat} {Γ A Δ σ : ZFSet} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ) :
  cwfTy_reindex n Γ A Δ σ ∈ cwfTy n Δ.
Proof.
  apply setCompArr_typing ; assumption. 
Qed.

Lemma cwfTy_reindex_id {n : nat} {Γ A : ZFSet} (HA : A ∈ cwfTy n Γ) : cwfTy_reindex n Γ A Γ (setIdArr Γ) ≡ A.
Proof.
  apply setCompId_left. assumption.
Qed.
  
Lemma cwfTy_reindex_comp {n : nat} {Γ A Δ σ Θ τ : ZFSet} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ) (Hτ : τ ∈ cwfSub Θ Δ) :
  cwfTy_reindex n Γ A Θ (cwfComp Γ Δ Θ σ τ) ≡ cwfTy_reindex n Δ (cwfTy_reindex n Γ A Δ σ) Θ τ.
Proof.
  unfold cwfTy_reindex. apply sym. apply setCompAssoc ; assumption.
Qed.

Lemma app_cwfTy_reindex {n : nat} {Γ A Δ σ δ} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ) (Hδ : δ ∈ Δ) :
  setAppArr Δ (𝕍 n × 𝕍 n) (cwfTy_reindex n Γ A Δ σ) δ ≡ setAppArr Γ (𝕍 n × 𝕍 n) A (setAppArr Δ Γ σ δ).
Proof.
  now apply (setCompArr_app Hσ HA).
Qed.

Lemma cwfTy_reindex_to_depSet {n : nat} {Γ A Δ σ δ} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ) (Hδ : δ ∈ Δ) :
  cwfTy_to_depSet n Δ (cwfTy_reindex n Γ A Δ σ) δ ≡ cwfTy_to_depSet n Γ A (setAppArr Δ Γ σ δ).
Proof.
  apply (fequal (setFstPair (𝕍 n) (𝕍 n))). now apply app_cwfTy_reindex.
Qed.

Lemma cwfTy_to_depSet_typing {n : nat} {Γ A : ZFSet} (HA : A ∈ cwfTy n Γ) (γ : ZFSet) (Hγ : γ ∈ Γ) :
  cwfTy_to_depSet n Γ A γ ∈ 𝕍 n.
Proof.
  unfold cwfTy_to_depSet. apply setFstPair_typing.
  apply setAppArr_typing ; assumption.
Qed.

(* Dependent presheaf of terms *)

Definition cwfInTy (n : nat) (Γ : ZFSet) (A : ZFSet) (t : ZFSet) :=
  ∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ∈ cwfTy_to_depSet n Γ A γ.

Definition cwfTm (n : nat) (Γ : ZFSet) (A : ZFSet) := { t ϵ Γ ⇒ (𝕍 n) ∣ cwfInTy n Γ A t }.

Definition cwfTm_reindex (n : nat) (Γ t Δ σ : ZFSet) := setCompArr Δ Γ (𝕍 n) σ t.

Lemma cwfTm_reindex_typing {n : nat} {Γ A t Δ σ : ZFSet} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) (Hσ : σ ∈ cwfSub Δ Γ) :
  cwfTm_reindex n Γ t Δ σ ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ).
Proof.
  apply ZFincomp in Ht. destruct Ht as [ Ht1 Ht2 ]. unfold cwfInTy in Ht2.
  apply ZFincomp. split.
  - apply setCompArr_typing ; assumption. 
  - unfold cwfInTy. intros δ Hδ.
    set (γ := setAppArr Δ Γ σ δ). assert (γ ∈ Γ) as Hγ.
    { apply setAppArr_typing ; assumption. }
    specialize (Ht2 γ Hγ). unfold cwfTy_reindex.
    refine (transpS (fun x => setAppArr Δ (𝕍 n) (cwfTm_reindex n Γ t Δ σ) δ ∈ setFstPair (𝕍 n) (𝕍 n) x)
                    (sym (setCompArr_app Hσ HA Hδ)) _).
    refine (transpS (fun x => x ∈ setFstPair (𝕍 n) (𝕍 n) (setAppArr Γ (𝕍 n × 𝕍 n) A (setAppArr Δ Γ σ δ)))
                    (sym (setCompArr_app Hσ Ht1 Hδ)) _).
    exact Ht2.
Qed.

Lemma cwfTm_reindex_id {n : nat} {Γ A t : ZFSet} (Ht : t ∈ cwfTm n Γ A) : cwfTm_reindex n Γ t Γ (setIdArr Γ) ≡ t.
Proof.
  apply setCompId_left.
  apply ZFincomp in Ht. destruct Ht as [ Ht _ ]. exact Ht.
Qed.

Lemma cwfTm_reindex_comp {n : nat} {Γ A t Δ σ Θ τ : ZFSet} (Ht : t ∈ cwfTm n Γ A) (Hσ : σ ∈ cwfSub Δ Γ) (Hτ : τ ∈ cwfSub Θ Δ) :
  cwfTm_reindex n Γ t Θ (cwfComp Γ Δ Θ σ τ) ≡ cwfTm_reindex n Δ (cwfTm_reindex n Γ t Δ σ) Θ τ.
Proof.
  unfold cwfTm_reindex. apply sym. apply setCompAssoc ; try assumption.
  apply ZFincomp in Ht. destruct Ht as [ Ht _ ]. exact Ht.
Qed.

Lemma cwfTm_app {n : nat} {Γ A t γ} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) (Hγ : γ ∈ Γ)
  : setAppArr Γ (𝕍 n) t γ ∈ cwfTy_to_depSet n Γ A γ.
Proof.
  apply ZFincomp in Ht. destruct Ht as [ Ht1 Ht2 ]. now apply Ht2.
Qed.

Lemma app_cwfTm_reindex {n : nat} {Γ A t Δ σ δ} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) (Hσ : σ ∈ cwfSub Δ Γ) (Hδ : δ ∈ Δ) :
  setAppArr Δ (𝕍 n) (cwfTm_reindex n Γ t Δ σ) δ ≡ setAppArr Γ (𝕍 n) t (setAppArr Δ Γ σ δ).
Proof.
  apply ZFincomp in Ht. destruct Ht as [ Ht1 Ht2 ].
  now apply (setCompArr_app Hσ Ht1).
Qed.

Lemma cwfTm_funext {n : nat} {Γ A t u} (HA : A ∈ cwfTy n Γ) (Ht : t ∈ cwfTm n Γ A) (Hu : u ∈ cwfTm n Γ A) :
  (∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ≡ setAppArr Γ (𝕍 n) u γ) -> t ≡ u.
Proof.
  apply ZFincomp in Ht. destruct Ht as [ Ht1 Ht2 ].
  apply ZFincomp in Hu. destruct Hu as [ Hu1 Hu2 ].
  intro H. now apply (setArr_funext Ht1 Hu1).
Qed.  

(* Context extension *)

Definition ctxExt (n : nat) (Γ A : ZFSet) :=
  setSigma n Γ (cwfTy_to_depSet n Γ A).

(* First projection for context extensions *)

Definition ctxWk_HO (n : nat) (Γ A : ZFSet) : ZFSet -> ZFSet :=
  fun γa => setFstSigma n Γ (cwfTy_to_depSet n Γ A) γa.

Definition ctxWk (n : nat) (Γ A : ZFSet) :=
  relToGraph (ctxExt n Γ A) Γ (HO_rel (ctxWk_HO n Γ A)).

Lemma ctxWk_HO_typing {n : nat} {Γ A γa : ZFSet} (HA : A ∈ cwfTy n Γ) (Hγa : γa ∈ ctxExt n Γ A) :
  ctxWk_HO n Γ A γa ∈ Γ.
Proof.
  unfold ctxWk_HO. apply setFstSigma_typing. 
  - now apply cwfTy_to_depSet_typing.
  - assumption.
Qed.

Lemma ctxWk_typing (n : nat) (Γ A : ZFSet) (HA : A ∈ cwfTy n Γ) : ctxWk n Γ A ∈ cwfSub (ctxExt n Γ A) Γ.
Proof.
  apply relToGraph_typing. apply HO_rel_typing.
  intros γa Hγa. now apply ctxWk_HO_typing.
Qed.

(* Second projection for context extensions *)

Definition ctxVar0_HO (n : nat) (Γ A : ZFSet) :=
  fun γa => setSndSigma n Γ (cwfTy_to_depSet n Γ A) γa.

Definition ctxVar0 (n : nat) (Γ A : ZFSet) :=
  relToGraph (ctxExt n Γ A) (𝕍 n) (HO_rel (ctxVar0_HO n Γ A)).

Lemma ctxVar0_HO_pretyping {n : nat} {Γ A : ZFSet} (HA : A ∈ cwfTy n Γ) {γa : ZFSet} (Hγa : γa ∈ ctxExt n Γ A) :
  ctxVar0_HO n Γ A γa ∈ 𝕍 n.
Proof.
  eapply ZFuniv_trans. exact (setSndSigma_typing (cwfTy_to_depSet_typing HA) Hγa).
  eapply (cwfTy_to_depSet_typing HA).
  exact (setFstSigma_typing (cwfTy_to_depSet_typing HA) Hγa). 
Qed.

Lemma ctxVar0_pretyping {n : nat} {Γ A : ZFSet} (HA : A ∈ cwfTy n Γ) :
  ctxVar0 n Γ A ∈ ctxExt n Γ A ⇒ 𝕍 n.
Proof.
  apply relToGraph_typing. apply HO_rel_typing. now apply ctxVar0_HO_pretyping.
Qed.

Lemma ctxVar0_typing (n : nat) (Γ A : ZFSet) (HA : A ∈ cwfTy n Γ) :
  ctxVar0 n Γ A ∈ cwfTm n (ctxExt n Γ A) (cwfTy_reindex n Γ A (ctxExt n Γ A) (ctxWk n Γ A)).
Proof.
  apply ZFincomp. split.
  - now apply ctxVar0_pretyping. 
  - intros γa Hγa.
    (* destruct γa *)
    set (γ := setFstSigma n Γ (cwfTy_to_depSet n Γ A) γa).
    assert (γ ∈ Γ) as Hγ. exact (setFstSigma_typing (cwfTy_to_depSet_typing HA) Hγa).
    set (a := setSndSigma n Γ (cwfTy_to_depSet n Γ A) γa).
    assert (a ∈ cwfTy_to_depSet n Γ A γ) as Ha. exact (setSndSigma_typing (cwfTy_to_depSet_typing HA) Hγa).
    (* show typing *)
    refine (transp2S (fun X Y => X ∈ Y) _ _ Ha).
    + symmetry. apply setAppArr_HO ; try assumption. now apply ctxVar0_HO_pretyping.
    + symmetry. refine (trans _ _).
      * refine (cwfTy_reindex_to_depSet HA _ Hγa). now apply ctxWk_typing.
      * refine (fequal (fun X => setFstPair (𝕍 n) (𝕍 n) (setAppArr Γ (𝕍 n × 𝕍 n) A X)) _).
        apply setAppArr_HO ; try assumption. intros x Hx. now apply ctxWk_HO_typing.
Qed.

(* Substitution extensions *)

Definition subExt_HO (n : nat) (Γ Δ σ t : ZFSet) :=
  fun δ => ⟨ setAppArr Δ Γ σ δ ; setAppArr Δ (𝕍 n) t δ ⟩.

Definition subExt (n : nat) (Γ A Δ σ t : ZFSet) :=
  relToGraph Δ (ctxExt n Γ A) (HO_rel (subExt_HO n Γ Δ σ t)).

Lemma subExt_HO_typing {n : nat} {Γ A Δ σ t : ZFSet} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ)
  (Ht : t ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ)) (δ : ZFSet) (Hδ : δ ∈ Δ) :
  subExt_HO n Γ Δ σ t δ ∈ ctxExt n Γ A.
Proof.
  apply setMkSigma_typing.
  - now apply cwfTy_to_depSet_typing. 
  - now apply setAppArr_typing.
  - apply ZFincomp in Ht. destruct Ht as [ Ht1 Ht2 ].
    refine (transpS (fun X => setAppArr Δ (𝕍 n) t δ ∈ setFstPair (𝕍 n) (𝕍 n) X) _ (Ht2 δ Hδ)).
    now apply app_cwfTy_reindex.
Qed.

Lemma subExt_typing {n : nat} {Γ A Δ σ t : ZFSet} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ)
  (Ht : t ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ)) :
  subExt n Γ A Δ σ t ∈ cwfSub Δ (ctxExt n Γ A).
Proof.
  apply relToGraph_typing. apply HO_rel_typing. now apply subExt_HO_typing.
Qed.

(* Beta and eta equations for substitution extensions *)

Lemma subExt_beta1 {n : nat} {Γ A Δ σ t : ZFSet} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ)
  (Ht : t ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ))
  : cwfComp Γ (ctxExt n Γ A) Δ (ctxWk n Γ A) (subExt n Γ A Δ σ t) ≡ σ.
Proof.
  unshelve eapply (setArr_funext _ Hσ).
  - apply cwfComp_typing. now apply ctxWk_typing. now apply subExt_typing.
  - intros δ Hδ. refine (trans _ _). 
    { apply setCompArr_app ; try assumption.
      - now apply subExt_typing.
      - now apply ctxWk_typing. }
    refine (trans _ _).
    { apply setAppArr_HO.
      - intros γa Hγa. now apply ctxWk_HO_typing. 
      - apply setAppArr_typing. now apply subExt_typing. assumption. }
    refine (trans _ _).
    { refine (fequal (ctxWk_HO n Γ A) _).
      apply setAppArr_HO. intros x Hx. now apply subExt_HO_typing.
      assumption. }
    apply setSigmaβ1.
    + now apply cwfTy_to_depSet_typing.
    + now apply setAppArr_typing.
    + refine (transpS (fun X => setAppArr Δ (𝕍 n) t δ ∈ X) _ (cwfTm_app (cwfTy_reindex_typing HA Hσ) Ht Hδ)).
      now apply cwfTy_reindex_to_depSet.
Qed.

Lemma subExt_beta2 {n : nat} {Γ A Δ σ t : ZFSet} (HA : A ∈ cwfTy n Γ) (Hσ : σ ∈ cwfSub Δ Γ)
  (Ht : t ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ)) (u := cwfTm_reindex n (ctxExt n Γ A) (ctxVar0 n Γ A) Δ (subExt n Γ A Δ σ t))
  : u ≡ t.
Proof.
  set (A' := cwfTy_reindex n Γ A (ctxExt n Γ A) (ctxWk n Γ A)).
  assert (A' ∈ cwfTy n (ctxExt n Γ A)) as HA'.
  { apply cwfTy_reindex_typing. assumption. now apply ctxWk_typing. }

  assert (u ∈ cwfTm n Δ (cwfTy_reindex n Γ A Δ σ)) as Hu.
  { refine (transpS (fun X => u ∈ X) _ (cwfTm_reindex_typing HA' _ _)).
    - refine (fequal (cwfTm n Δ) _). refine (trans _ _).
      + symmetry. apply cwfTy_reindex_comp ; try assumption.
        now apply ctxWk_typing. now apply subExt_typing. 
      + refine (fequal (cwfTy_reindex n Γ A Δ) _).
        now apply subExt_beta1.
    - now apply ctxVar0_typing.
    - now apply subExt_typing. }

  apply (cwfTm_funext (cwfTy_reindex_typing HA Hσ) Hu Ht).
  intros δ Hδ. refine (trans _ _).
  { exact (app_cwfTm_reindex HA' (ctxVar0_typing n Γ A HA) (subExt_typing HA Hσ Ht) Hδ). }
  refine (trans _ _).
  { apply setAppArr_HO. intros γa Hγa. now apply ctxVar0_HO_pretyping.
    apply setAppArr_typing. now apply subExt_typing. assumption. }
  refine (trans _ _).
  { refine (fequal (ctxVar0_HO n Γ A) _).
    apply setAppArr_HO. intros δ' Hδ'. now apply subExt_HO_typing. assumption. }
  apply setSigmaβ2.
  + intros γ Hγ. now apply cwfTy_to_depSet_typing.
  + now apply setAppArr_typing.
  + refine (transpS (fun X => setAppArr Δ (𝕍 n) t δ ∈ X) _ _).
    * now apply cwfTy_reindex_to_depSet.
    * apply cwfTm_app. now apply cwfTy_reindex_typing. assumption. assumption.
Qed.



Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.

(* We define a CwF that supports all the type formers and operations of CICobs *)

(* Underlying category *)

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

(* Remember: a type [A] at level i is a pair of two elements of [𝕍ᵢ] *)
(* Then the relation [Γ ⊢ t : A] is defined to be [∀ ρ : {Γ}, {t}ρ ∈ fst {A}ρ ]*)

Definition cwfTy (n : nat) (Γ : ZFSet) := Γ ⇒ (𝕍 n × 𝕍 n).

Definition cwfTy_reindex (n : nat) (Γ A Δ σ : ZFSet) := setCompArr Δ Γ (𝕍 n × 𝕍 n) σ A.

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

(* Dependent presheaf of terms *)

Definition cwfInTy (n : nat) (Γ : ZFSet) (A : ZFSet) (t : ZFSet) :=
  ∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ∈ setFstPair (𝕍 n) (𝕍 n) (setAppArr Γ (𝕍 n × 𝕍 n) A γ).

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

(* Context extension *)

Definition cwfTy_to_depSet (n : nat) (Γ A : ZFSet) : ZFSet -> ZFSet :=
  fun γ => setFstPair (𝕍 n) (𝕍 n) (setAppArr Γ (𝕍 n × 𝕍 n) A γ).

Definition ctxExt (n : nat) (Γ A : ZFSet) :=
  setSigma n Γ (cwfTy_to_depSet n Γ A).

(* First projection for context extensions *)

Definition ctxWk_HO (n : nat) (Γ A : ZFSet) : ZFSet -> ZFSet :=
  fun γa => setFstSigma n Γ (cwfTy_to_depSet n Γ A) γa.

Definition ctxWk (n : nat) (Γ A : ZFSet) :=
  relToGraph (ctxExt n Γ A) Γ (HO_rel (ctxWk_HO n Γ A)).

Lemma cwfTy_to_depSet_typing {n : nat} {Γ A γ : ZFSet} (HA : A ∈ cwfTy n Γ) (Hγ : γ ∈ Γ) :
  cwfTy_to_depSet n Γ A γ ∈ 𝕍 n.
Proof.
  unfold cwfTy_to_depSet. apply setFstPair_typing.
  apply setAppArr_typing ; assumption.
Qed.

Lemma ctxWk_HO_typing {n : nat} {Γ A γa : ZFSet} (HA : A ∈ cwfTy n Γ) (Hγa : γa ∈ ctxExt n Γ A) :
  ctxWk_HO n Γ A γa ∈ Γ.
Proof.
  unfold ctxWk_HO. apply setFstSigma_typing. 
  - intros γ Hγ. now apply cwfTy_to_depSet_typing.
  - assumption.
Qed.

Lemma ctxWk_typing (n : nat) (Γ A : ZFSet) (HA : A ∈ cwfTy n Γ) : ctxWk n Γ A ∈ cwfSub (ctxExt n Γ A) Γ.
Proof.
  apply relToGraph_typing. apply HO_rel_typing.
  intros γa Hγa. now apply ctxWk_HO_typing.
Qed.

(* Second projection for context extensions *)

Definition ctxWk_var0_typing (n : nat) (Γ A : ZFSet) : ctxWk_var0 n Γ A ∈ cwfTm n (ctxExt n Γ A) (cwfTy_reindex A).
  

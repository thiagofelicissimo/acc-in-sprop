Require Import library.
Require Import ZF_axioms.
Require Import ZF_library.
Require Import CwF.

(* Defining terms and types using higher-order stuff *)

Definition HO_Ty (n : nat) (Γ : ZFSet) (f : ZFSet -> ZFSet) := relToGraph Γ (𝕍 n × (ω × 𝕍 n)) (HO_rel f).
Definition HO_Tm (n : nat) (Γ : ZFSet) (f : ZFSet -> ZFSet) := relToGraph Γ (𝕍 n) (HO_rel f).

Lemma HO_Tm_pretyping {n : nat} {Γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n) : HO_Tm n Γ f ∈ Γ ⇒ 𝕍 n.
Proof.
  apply relToGraph_typing. now apply HO_rel_typing.
Qed.
  
Lemma cwfTy_to_depSet_HO_Ty {n : nat} {Γ γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n × (ω × 𝕍 n)) (Hγ : γ ∈ Γ) :
  cwfTy_to_depSet n Γ (HO_Ty n Γ f) γ ≡ setFstPair (𝕍 n) (ω × 𝕍 n) (f γ).
Proof.
  refine (fequal (setFstPair _ _) _).
  now apply setAppArr_HO.
Qed. 

Lemma setAppArr_HO_Tm {n : nat} {Γ γ : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n) (Hγ : γ ∈ Γ) : 
  setAppArr Γ (𝕍 n) (HO_Tm n Γ f) γ ≡ f γ.
Proof.
  now apply setAppArr_HO.
Qed.

Lemma setAppArr_Tm_typing {n : nat} {Γ t : ZFSet} {A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕍 n × (ω × 𝕍 n)) (Ht : t ∈ Γ ⇒ 𝕍 n) :
  (∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ∈ setFstPair (𝕍 n) (ω × 𝕍 n) (A γ)) -> (t ∈ cwfTm n Γ (HO_Ty n Γ A)).
Proof.
  intro Ht'. apply ZFincomp. split ; try assumption.
  intros γ Hγ. refine (transpS (fun x => _ ∈ x) _ (Ht' γ Hγ)).
  symmetry. now apply cwfTy_to_depSet_HO_Ty.
Qed.

Lemma setAppArr_Tm_detyping {n : nat} {Γ t : ZFSet} {A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕍 n × (ω × 𝕍 n)) :
  (t ∈ cwfTm n Γ (HO_Ty n Γ A)) -> ∀ γ ∈ Γ, setAppArr Γ (𝕍 n) t γ ∈ setFstPair (𝕍 n) (ω × 𝕍 n) (A γ).
Proof.
  intros Ht' γ Hγ. apply ZFincomp in Ht'. destruct Ht' as [ _ Ht' ].
  refine (transpS (fun x => _ ∈ x) _ (Ht' γ Hγ)).
  now apply cwfTy_to_depSet_HO_Ty.
Qed.

Lemma HO_Tm_typing {n : nat} {Γ : ZFSet} {f A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕍 n × (ω × 𝕍 n)) :
  (∀ γ ∈ Γ, f γ ∈ setFstPair (𝕍 n) (ω × 𝕍 n) (A γ)) -> (HO_Tm n Γ f ∈ cwfTm n Γ (HO_Ty n Γ A)).
Proof.
  intro H. assert (∀ γ ∈ Γ, f γ ∈ 𝕍 n) as Hf.
  { intros γ Hγ. eapply ZFuniv_trans. now apply H. apply setFstPair_typing. now apply HA. }
  eapply (setAppArr_Tm_typing HA (HO_Tm_pretyping Hf)).
  intros γ Hγ. refine (transpS (fun x => x ∈ _) _ (H γ Hγ)).
  symmetry. now apply setAppArr_HO_Tm.
Qed.

Lemma HO_Tm_detyping {n : nat} {Γ : ZFSet} {f A : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕍 n × (ω × 𝕍 n)) (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕍 n) :
  (HO_Tm n Γ f ∈ cwfTm n Γ (HO_Ty n Γ A)) -> (∀ γ ∈ Γ, f γ ∈ setFstPair (𝕍 n) (ω × 𝕍 n) (A γ)).
Proof.
  intros H γ Hγ. eapply (setAppArr_Tm_detyping HA) in H.
  refine (transpS (fun x => x ∈ _) _ H). now apply setAppArr_HO_Tm. assumption.
Qed.

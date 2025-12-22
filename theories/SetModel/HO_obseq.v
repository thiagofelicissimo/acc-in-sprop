Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_prop HO_univ HO_forall HO_pi.

(* Observational equality *)

Definition eqTy_HO (A t u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => prop (t γ ≡ u γ).

Lemma eqTy_HO_typing {n : nat} {Γ : ZFSet} {A t u : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, eqTy_HO A t u γ ∈ Ω.
Proof.
  intros γ Hγ. cbn. apply prop_typing.
Qed.

(* Reflexivity *)

Definition reflTm_HO (A t : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma reflTm_HO_typing {n : nat} {Γ : ZFSet} {A t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, reflTm_HO A t γ ∈ eqTy_HO A t t γ.
Proof.
  intros γ Hγ. unfold reflTm_HO. apply prop_true_iff. reflexivity.
Qed.

(* J eliminator *)

Definition eqindTm_HO (A t P p u e : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma eqindTm_HO_typing {n : nat} {Γ : ZFSet} {A t P p u e : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) (HP : ∀ γa ∈ ctxExt n Γ A, P γa ∈ Ω)
  (Hp : ∀ γ ∈ Γ, p γ ∈ P ⟨ γ ; t γ ⟩) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) (He : ∀ γ ∈ Γ, e γ ∈ eqTy_HO A t u γ) :
  ∀ γ ∈ Γ, eqindTm_HO A t P p u e γ ∈ P ⟨ γ ; u γ ⟩.
Proof.
  intros γ Hγ. unfold eqindTm_HO. specialize (He γ Hγ). unfold eqTy_HO in He.
  apply prop_true_if in He. refine (transpS (fun X => ∅ ∈ P ⟨ γ ; X ⟩) He _). specialize (Ht γ Hγ).
  assert (⟨ γ ; t γ ⟩ ∈ ctxExt n Γ A) as Hγt.
  { apply setMkSigma_typing ; try assumption. clear γ Ht He Hγ. intros γ Hγ. apply 𝕌el_typing. now apply HA. }
  specialize (HP ⟨ γ ; t γ ⟩ Hγt). cbn in HP. eapply (proof_irr' HP). now apply Hp.
Qed.

(* Type casting *)

Definition castTm_HO (A B e t : ZFSet -> ZFSet) : ZFSet -> ZFSet := t.

Lemma castTm_HO_typing {n : nat} {Γ : ZFSet} {A B e t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (He : ∀ γ ∈ Γ, e γ ∈ eqTy_HO (univTy_HO n) A B γ)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) : ∀ γ ∈ Γ, castTm_HO A B e t γ ∈ 𝕌el n (B γ).
Proof.
  intros γ Hγ. unfold castTm_HO. specialize (He γ Hγ). unfold eqTy_HO in He.
  apply prop_true_if in He. refine (transpS (fun X => t γ ∈ 𝕌el n X) He _).
  now apply Ht.
Qed.

Lemma castTm_HO_refl {n : nat} {Γ : ZFSet} {A t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, castTm_HO A A (reflTm_HO (univTy_HO n) A) t γ ≡ t γ.
Proof.
  intros γ Hγ. reflexivity.
Qed.

(* Function extensionality *)

Definition funextTm_HO (A B f g e : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma funextTm_HO_typing {n : nat} {Γ : ZFSet} {A B f g e : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕌el n (piTy_HO n A B γ)) (Hg : ∀ γ ∈ Γ, g γ ∈ 𝕌el n (piTy_HO n A B γ))
  (He : ∀ γa ∈ ctxExt n Γ A,
      e γa ∈ eqTy_HO B (appTm_HO n (fun γa => A (ctx_wk n Γ A γa)) (fun γa => f (ctx_wk n Γ A γa)) (ctx_var0 n Γ A))
                       (appTm_HO n (fun γa => A (ctx_wk n Γ A γa)) (fun γa => g (ctx_wk n Γ A γa)) (ctx_var0 n Γ A)) γa) :
  ∀ γ ∈ Γ, funextTm_HO A B f g e γ ∈ eqTy_HO (piTy_HO n A B) f g γ.
Proof.
  intros γ Hγ. unfold funextTm_HO. unfold eqTy_HO. apply prop_true_iff.
  apply (setArr_funext (A := 𝕌el n (A γ)) (B := 𝕍 n)).
  - pose proof (transpS (fun X => f γ ∈ X) (el_piTy HA HB Hγ) (Hf γ Hγ)) as H. apply ZFincomp in H. now destruct H.
  - pose proof (transpS (fun X => g γ ∈ X) (el_piTy HA HB Hγ) (Hg γ Hγ)) as H. apply ZFincomp in H. now destruct H.
  - intros a Ha. assert (⟨ γ ; a ⟩ ∈ ctxExt n Γ A) as Hγa.
    { apply setMkSigma_typing ; try assumption. intros γ' Hγ'. apply 𝕌el_typing. now apply HA. }
    specialize (He _ Hγa). apply prop_true_if in He. refine (trans (sym _) (trans He _)).
    + refine (fequal2 (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (f X) Y) _ _).
      * now apply ctxExtβ1.
      * now apply ctxExtβ2.
    + refine (fequal2 (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (g X) Y) _ _).
      * now apply ctxExtβ1.
      * now apply ctxExtβ2.
Qed.
 
(* Proposition extensionality *)

Definition propextTm_HO (P Q e f : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma propextTm_HO_typing {Γ : ZFSet} {P Q e f : ZFSet -> ZFSet}
  (HP : ∀ γ ∈ Γ, P γ ∈ Ω) (HQ : ∀ γ ∈ Γ, Q γ ∈ Ω) (He : ∀ γ ∈ Γ, e γ ∈ implTy_HO P Q γ)
  (Hf : ∀ γ ∈ Γ, f γ ∈ implTy_HO Q P γ) : ∀ γ ∈ Γ, propextTm_HO P Q e f γ ∈ eqTy_HO propTy_HO P Q γ.
Proof.
  intros γ Hγ. cbn. unfold propextTm_HO. unfold eqTy_HO. apply prop_true_iff. apply ZFext.
  - unfold implTy_HO in He. specialize (He γ Hγ). apply ZFincomp in He. now destruct He.
  - unfold implTy_HO in Hf. specialize (Hf γ Hγ). apply ZFincomp in Hf. now destruct Hf.
Qed.
  
(* Injectivity of Pi-types *)

(* Computation rules for cast *)

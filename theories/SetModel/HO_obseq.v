Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_prop HO_univ HO_forall HO_nat HO_pi.

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

Definition piinj1Tm_HO (A A' B B' e : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma piinj1Tm_HO_typing {n : nat} {Γ : ZFSet} {A A' B B' e : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (He : ∀ γ ∈ Γ, e γ ∈ eqTy_HO (univTy_HO n) (piTy_HO n A B) (piTy_HO n A' B') γ)
  : ∀ γ ∈ Γ, piinj1Tm_HO A A' B B' e γ ∈ eqTy_HO (univTy_HO n) A' A γ.
Proof.
  intros γ Hγ. cbn. unfold eqTy_HO. unfold piinj1Tm_HO. apply prop_true_iff. apply sym.
  apply (piTy_HO_inj1 HA HB HA' HB' Hγ). specialize (He γ Hγ). unfold eqTy_HO in He.
  now apply prop_true_if in He.
Qed.

Definition piinj2Tm_HO (A A' B B' e a : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma piinj2Tm_HO_typing {n : nat} {Γ : ZFSet} {A A' B B' e a : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (He : ∀ γ ∈ Γ, e γ ∈ eqTy_HO (univTy_HO n) (piTy_HO n A B) (piTy_HO n A' B') γ)
  (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A' γ)) (a0 := castTm_HO A' A (piinj1Tm_HO A A' B B' e) a)
  : ∀ γ ∈ Γ, piinj2Tm_HO A A' B B' e a γ ∈ eqTy_HO (univTy_HO n) (fun γ => B ⟨ γ ; a0 γ ⟩) (fun γ => B' ⟨ γ ; a γ ⟩) γ.
Proof.
  intros γ Hγ. cbn. unfold piinj2Tm_HO. unfold eqTy_HO. apply prop_true_iff.
  unfold castTm_HO in a0. unfold a0. clear a0. specialize (He γ Hγ). unfold eqTy_HO in He.
  apply prop_true_if in He. assert (a γ ∈ 𝕌el n (A γ)).
  { refine (transpS (fun X => a γ ∈ 𝕌el n X) _ (Ha γ Hγ)). apply sym.
    now apply (piTy_HO_inj1 HA HB HA' HB' Hγ). }
  apply (piTy_HO_inj2 HA HB HA' HB' Hγ He H).
Qed.

(* Computation rule for cast on pi
   Since cast is the identity, this rule is just η, modulo a bit of transport *)

Lemma castTm_HO_pi {n : nat} {Γ : ZFSet} {A A' B B' e f : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ 𝕌 n)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 n) (HB' : ∀ γa ∈ ctxExt n Γ A', B' γa ∈ 𝕌 n)
  (He : ∀ γ ∈ Γ, e γ ∈ eqTy_HO (univTy_HO n) (piTy_HO n A B) (piTy_HO n A' B') γ)
  (Hf : ∀ γ ∈ Γ, f γ ∈ 𝕌el n (piTy_HO n A B γ))
  (Au := fun γa => A (ctx_wk n Γ A' γa)) (A'u := fun γa => A' (ctx_wk n Γ A' γa))
  (Bu := fun γaa => B ⟨ ctx_wk n Γ A' (ctx_wk n (ctxExt n Γ A') Au γaa) ; ctx_var0 n (ctxExt n Γ A') Au γaa ⟩)
  (B'u := fun γaa => B' ⟨ ctx_wk n Γ A' (ctx_wk n (ctxExt n Γ A') A'u γaa) ; ctx_var0 n (ctxExt n Γ A') A'u γaa ⟩)
  (t1 := castTm_HO A'u Au (piinj1Tm_HO Au A'u Bu B'u (fun γa => e (ctx_wk n Γ A' γa))) (fun γa => ctx_var0 n Γ A' γa))
  (t2 := appTm_HO n Au (fun γa => f (ctx_wk n Γ A' γa)) t1)
  (t3 := castTm_HO (fun γa => B ⟨ ctx_wk n Γ A' γa ; t1 γa ⟩) B'
           (piinj2Tm_HO Au A'u Bu B'u (fun γa => e (ctx_wk n Γ A' γa)) (fun γa => ctx_var0 n Γ A' γa)) t2)
  (t4 := lamTm_HO n A' t3) : ∀ γ ∈ Γ, castTm_HO (piTy_HO n A B) (piTy_HO n A' B') e f γ ≡ t4 γ.
Proof.
  intros γ Hγ. unfold castTm_HO in *. unfold t4. unfold t3. unfold t2. unfold t1. unfold Au.
  clear t1 t2 t3 t4. unfold lamTm_HO. unfold appTm_HO.
  specialize (He γ Hγ). unfold eqTy_HO in He. apply prop_true_if in He.
  assert (A γ ≡ A' γ) as HAA'. { now apply (piTy_HO_inj1 HA HB HA' HB' Hγ). }
  assert (f γ ∈ setPi n (𝕌el n (A' γ)) (fun a => 𝕌el n (B' ⟨ γ ; a ⟩))) as Hf'.
  { refine (transpS (fun X => f γ ∈ X) (el_piTy HA' HB' Hγ) _).
    refine (transpS (fun X => f γ ∈ 𝕌el n X) He _). now apply Hf. }
  apply ZFincomp in Hf'. destruct Hf' as [ Hf' _ ].
  apply (setArr_funext (A := 𝕌el n (A' γ)) (B := 𝕍 n)).
  - exact Hf'.
  - apply relToGraph_typing. apply HO_rel_typing. intros a Ha.
    refine (transp2S (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (f X) Y ∈ 𝕍 n)
              (sym (ctxExtβ1 HA' Hγ Ha)) (sym (ctxExtβ2 HA' Hγ Ha)) _).
    refine (transpS (fun X => setAppArr (𝕌el n X) (𝕍 n) (f γ) a ∈ 𝕍 n) (sym HAA') _).
    apply setAppArr_typing. 2:assumption. exact Hf'.
  - intros a Ha. refine (sym _). refine (trans _ _). apply setAppArr_HO. 2:assumption.
    + clear a Ha. intros a Ha. 
      refine (transp2S (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (f X) Y ∈ 𝕍 n)
                (sym (ctxExtβ1 HA' Hγ Ha)) (sym (ctxExtβ2 HA' Hγ Ha)) _).
      refine (transpS (fun X => setAppArr (𝕌el n X) (𝕍 n) (f γ) a ∈ 𝕍 n) (sym HAA') _).
      apply setAppArr_typing. 2:assumption. exact Hf'.
    + refine (fequal2 (fun X Y => setAppArr (𝕌el n (A X)) (𝕍 n) (f X) Y)
                ((ctxExtβ1 HA' Hγ Ha)) ((ctxExtβ2 HA' Hγ Ha))).
Qed.

(* No-confusion theorems. Copy and paste for all type formers if necessary *)

Lemma nat_neq_pi {n : nat} {Γ : ZFSet} {A B e : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ ⋆, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n ⋆ A, B γa ∈ 𝕌 n)
  (He : ∀ γ ∈ ⋆, e γ ∈ eqTy_HO (univTy_HO n) natTy_HO (piTy_HO n A B) γ) : FalseS.
Proof.
  assert (∅ ∈ ⋆) as H. { now apply inSetSingl. }
  specialize (He _ H). cbn in He. unfold eqTy_HO in He. apply prop_true_if in He.
  assert (ZFzero ≡ ZFone).
  { refine (trans (sym _) (trans (fequal (𝕌hd n) He) _)).
    - now apply hd_natTy.
    - now apply (hd_piTy HA HB H). }
  now apply (zero_ne_suc ∅).
Qed.


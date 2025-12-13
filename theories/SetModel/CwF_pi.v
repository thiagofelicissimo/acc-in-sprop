Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO HO_pi.
Require Import CwF CwF_library.

(* Pi types *)

Definition piTy (n : nat) (Γ : ZFSet) (A : ZFSet) (B : ZFSet) : ZFSet :=
  HO_to_cwfTy n Γ (piTy_HO n (cwfTy_to_HO n Γ A) (cwfTy_to_HO2 n Γ A B)).

Lemma cwfPi {n : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) :
  piTy n Γ A B ∈ cwfTy n Γ.
Proof.
  apply relToGraph_typing. apply HO_rel_typing. apply piTy_HO_typing.
  - now apply cwfTy_to_HO_typing.
  - intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
Qed.

Lemma cwfPi_to_HO {n : nat} {Γ A B : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A)) :
  ∀ γ ∈ Γ, cwfTy_to_HO n Γ (piTy n Γ A B) γ ≡ piTy_HO n (cwfTy_to_HO n Γ A) (cwfTy_to_HO2 n Γ A B) γ.
Proof.
  intros γ Hγ. cbn. unfold piTy. apply setAppArr_HO.
  intros γ' Hγ'. apply (piTy_HO_typing n (Γ := Γ)). now apply cwfTy_to_HO_typing.
  intros γ'' Hγ'' a Ha. now apply cwfTy_to_HO2_typing. assumption. assumption.
Qed.

(* Injectivity of Pi types *)

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

Definition lamTm (n : nat) (Γ : ZFSet) (A : ZFSet) (t : ZFSet) : ZFSet :=
  HO_to_cwfTm n Γ (lamTm_HO n (cwfTy_to_HO n Γ A) (cwfTm_to_HO2 n Γ A t)).

Lemma cwfLam {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A))
  (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) : lamTm n Γ A t ∈ cwfTm n Γ (piTy n Γ A B).
Proof.
  apply HO_to_cwfTm_typing.
  - apply piTy_HO_typing.
    + now apply cwfTy_to_HO_typing.
    + intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
  - intros γ Hγ. apply (lamTm_HO_typing n (Γ := Γ)).
    + now apply cwfTy_to_HO_typing.
    + intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
    + intros γ' Hγ' a Ha. now apply cwfTm_to_HO2_typing.
    + assumption.
Qed.

Lemma cwfLam_to_HO {n : nat} {Γ A B t : ZFSet} (HA : A ∈ cwfTy n Γ) (HB : B ∈ cwfTy n (ctxExt n Γ A))
  (Ht : t ∈ cwfTm n (ctxExt n Γ A) B) :
  ∀ γ ∈ Γ, cwfTm_to_HO n Γ (lamTm n Γ A t) γ ≡ lamTm_HO n (cwfTy_to_HO n Γ A) (cwfTm_to_HO2 n Γ A t) γ.
Proof.
  intros γ Hγ. apply setAppArr_HO. 2:assumption. clear γ Hγ.
  intros γ Hγ. eapply ZFuniv_trans. apply (lamTm_HO_typing n (Γ := Γ) (B := (cwfTy_to_HO2 n Γ A B))). 
  - intros γ' Hγ'. now apply cwfTy_to_HO_typing.
  - intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
  - intros γ' Hγ' a Ha. now apply cwfTm_to_HO2_typing.
  - assumption.
  - apply 𝕌el_typing. apply (piTy_HO_typing n (Γ := Γ)).
    + intros γ' Hγ'. now apply cwfTy_to_HO_typing.
    + intros γ' Hγ' a Ha. now apply cwfTy_to_HO2_typing.
    + assumption.
Qed.

(* Application *)

Definition appTm (n : nat) (Γ : ZFSet) (A : ZFSet) (t : ZFSet) (u : ZFSet) : ZFSet :=
  HO_to_cwfTm n Γ (appTm_HO n (cwfTy_to_HO n Γ A) (cwfTm_to_HO n Γ t) (cwfTm_to_HO n Γ u)).

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
      - clear γ Hγ. apply (appTm_HO_typing n (Γ := Γ) (B := (cwfTy_to_HO2 n Γ A B))).
        + intros γ Hγ. now apply cwfTy_to_HO_typing.
        + intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
        + intros γ Hγ. refine (transpS (fun X => X ∈ _) (sym (cwfLam_to_HO HA HB Ht γ Hγ)) _).
          apply (lamTm_HO_typing n (Γ := Γ)) ; try assumption ; clear γ Hγ.
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
      intros γ Hγ. eapply ZFuniv_trans. apply (lamTm_HO_typing n (Γ := Γ) (B := (cwfTy_to_HO2 n Γ A B))) ; try assumption ; clear γ Hγ.
      - intros γ Hγ. now apply cwfTy_to_HO_typing.
      - intros γ Hγ a Ha. now apply cwfTy_to_HO2_typing.
      - intros γ Hγ a Ha. apply cwfTm_to_HO2_typing ; try assumption. now apply cwfPiη_aux.
      - apply 𝕌el_typing. apply (piTy_HO_typing n (Γ := Γ)).
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

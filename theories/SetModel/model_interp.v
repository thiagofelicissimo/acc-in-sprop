From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_acc HO_obseq HO_forall.

Open Scope subst_scope.

(* Interpretation of the syntax in the model *)

Inductive interp_ctx : forall (Γ : ctx), ZFSet -> Prop :=

| interp_empty : interp_ctx ∙ ⋆

| interp_cons_rel : forall Γ l A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty l)) A iA
                    -> interp_ctx (Γ ,, (ty l , A)) (ctxExt l iΓ iA)

| interp_cons_irr : forall Γ A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA
                    -> interp_ctx (Γ ,, (prop , A)) (ctxExt 0 iΓ (boxTy_HO iA))

with nth_proj : forall (Γ : ctx) (l : level) (x : nat), (ZFSet -> ZFSet) -> Prop :=

| here_rel : forall Γ l A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty l)) A iA
             -> nth_proj (Γ ,, (ty l , A)) (ty l) 0 (setSndSigma l iΓ (fun γ => 𝕌el l (iA γ)))

| there_rel : forall Γ l lA A x iΓ iA ix, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty lA)) A iA -> nth_proj Γ l x ix
              -> nth_proj (Γ ,, (ty lA , A)) l (S x) (fun γa => ix (setFstSigma lA iΓ (fun γ => 𝕌el lA (iA γ)) γa))

| here_irr : forall Γ A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA
             -> nth_proj (Γ ,, (prop , A)) prop 0 (setSndSigma 0 iΓ iA)

| there_irr : forall Γ l A x iΓ iA ix, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA -> nth_proj Γ l x ix
              -> nth_proj (Γ ,, (prop , A)) l (S x) (fun γa => ix (setFstSigma 0 iΓ (fun γ => 𝕌el 0 (boxTy_HO iA γ)) γa))

with interp_tm : forall (Γ : ctx) (l : level) (A : term), (ZFSet -> ZFSet) -> Prop :=

| interp_var : forall Γ l x ix, nth_proj Γ l x ix
               -> interp_tm Γ l (var x) ix

| interp_type : forall Γ l, 
                interp_tm Γ (Ax (Ax (ty l))) (Sort (ty l)) (univTy_HO l)

| interp_prop : forall Γ, 
                interp_tm Γ (ty 1) (Sort prop) propTy_HO

| interp_pi_rr : forall Γ lA lB A B iA iB, interp_tm Γ (Ax (ty lA)) A iA
                 -> interp_tm (Γ ,, (ty lA , A)) (Ax (ty lB)) B iB
                 -> interp_tm Γ (Ax (Ru (ty lA) (ty lB))) (Pi (ty lA) (ty lB) A B) 
                              (piTy_HO lA lB iA iB)

| interp_pi_ir : forall Γ lB A B iA iB, interp_tm Γ (Ax prop) A iA
                 -> interp_tm (Γ ,, (prop , A)) (Ax (ty lB)) B iB
                 -> interp_tm Γ (Ax (ty lB)) (Pi prop (ty lB) A B)
                              (piTy_HO 0 lB (boxTy_HO iA) iB)

| interp_pi_ri : forall Γ lA A B iA iB, interp_tm Γ (Ax (ty lA)) A iA
                 -> interp_tm (Γ ,, (ty lA , A)) (Ax prop) B iB
                 -> interp_tm Γ (Ax prop) (Pi (ty lA) prop A B) 
                              (forallTy_HO lA iA iB)

| interp_pi_ii : forall Γ A B iA iB, interp_tm Γ (Ax prop) A iA
                 -> interp_tm (Γ ,, (prop , A)) (Ax prop) B iB
                 -> interp_tm Γ (Ax prop) (Pi prop prop A B)
                              (forallTy_HO 0 (boxTy_HO iA) iB)

| interp_lam_rr : forall Γ lA lB A B t iA it, interp_tm Γ (Ax (ty lA)) A iA
                  -> interp_tm (Γ ,, (ty lA , A)) (ty lB) t it
                  -> interp_tm Γ (Ru (ty lA) (ty lB)) (lam (ty lA) (ty lB) A B t) (lamTm_HO lA lB iA it)

| interp_lam_ir : forall Γ lB A B t iA it, interp_tm Γ (Ax prop) A iA
                  -> interp_tm (Γ ,, (prop , A)) (ty lB) t it
                  -> interp_tm Γ (ty lB) (lam prop (ty lB) A B t) (lamTm_HO 0 lB (boxTy_HO iA) it)

| interp_app_rr : forall Γ lA lB A B t u iA it iu, interp_tm Γ (Ax (ty lA)) A iA
                  -> interp_tm Γ (Ru (ty lA) (ty lB)) t it
                  -> interp_tm Γ (ty lA) u iu
                  -> interp_tm Γ (ty lB) (app (ty lA) (ty lB) A B t u) (appTm_HO lA lB iA it iu)

| interp_app_ir : forall Γ lB A B t u iA it iu, interp_tm Γ (Ax prop) A iA
                  -> interp_tm Γ (ty lB) t it
                  -> interp_tm Γ prop u iu
                  -> interp_tm Γ (ty lB) (app prop (ty lB) A B t u) (appTm_HO 0 lB (boxTy_HO iA) it iu)

| interp_nat : forall Γ,
               interp_tm Γ (ty 1) Nat natTy_HO

| interp_zero : forall Γ,
                interp_tm Γ (ty 0) zero zeroTm_HO

| interp_succ : forall Γ t it, interp_tm Γ (ty 0) t it
                -> interp_tm Γ (ty 0) (succ t) (sucTm_HO it)

| interp_natrec : forall Γ l P pz ps m iP ipz ips im, interp_tm (Γ ,, (ty 0 , Nat)) (Ax (ty l)) P iP
                  -> interp_tm Γ (ty l) pz ipz
                  -> interp_tm (Γ ,, (ty 0 , Nat) ,, (ty l , P)) (ty l) ps ips
                  -> interp_tm Γ (ty 0) m im
                  -> interp_tm Γ (ty l) (rec (ty l) P pz ps m) (natrecTm_HO l iP ipz ips im)

| interp_acc : forall Γ i A R a iA iR ia, interp_tm Γ (Ax (ty i)) A iA
               -> interp_tm (Γ ,, (ty i, A) ,, (ty i, S ⋅ A)) (Ax prop) R iR
               -> interp_tm Γ (ty i) a ia
               -> interp_tm Γ (Ax prop) (Core.acc (ty i) A R a) (accTy_HO iA iR ia)

| interp_accelim : forall Γ i l A R a q P p iA iR ia iP ip, interp_tm Γ (Ax i) A iA
                   -> interp_tm (Γ ,, (i, A) ,, (i, S ⋅ A)) (Ax prop) R iR
                   -> interp_tm (Γ ,, (i, A)) (Ax (ty l)) P iP
                   -> interp_tm Γ (ty l) p ip
                   -> interp_tm Γ i a ia
                   -> interp_tm Γ (ty l) (accel i (ty l) A R P p a q) (accelimTm_HO l iA iR iP ip ia)

| interp_obseq : forall Γ l A a b iA ia ib, interp_tm Γ (Ax (ty l)) A iA
                   -> interp_tm Γ (ty l) a ia
                   -> interp_tm Γ (ty l) b ib
                   -> interp_tm Γ (Ax prop) (obseq (ty l) A a b) (eqTy_HO iA ia ib)

| interp_cast : forall Γ l A B e a iA iB ia, interp_tm Γ (Ax (ty l)) A iA
                -> interp_tm Γ (Ax (ty l)) B iB
                -> interp_tm Γ (ty l) a ia
                -> interp_tm Γ (ty l) (cast (ty l) A B e a) (castTm_HO iA iB ia).

Scheme interp_tm_mut := Induction for interp_tm Sort Prop
with interp_ctx_mut := Induction for interp_ctx Sort Prop
with nth_proj_mut := Induction for nth_proj Sort Prop.
Combined Scheme interp_mutind from interp_tm_mut, interp_ctx_mut, nth_proj_mut.

(* The interpretation is a partial function *)

Definition is_functional_ctx (Γ : ctx) (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ) : Prop :=
  forall iΓ', interp_ctx Γ iΓ' -> iΓ = iΓ'.

Definition is_functional_tm (Γ : ctx) (l : level) (t : term) (it : ZFSet -> ZFSet) (ft : interp_tm Γ l t it) : Prop :=
  forall it', interp_tm Γ l t it' -> it = it'.

Definition is_functional_proj (Γ : ctx) (l : level) (x : nat) (ix : ZFSet -> ZFSet) (fx : nth_proj Γ l x ix) : Prop :=
  forall ix', nth_proj Γ l x ix' -> ix = ix'.

Lemma functional_interp : (forall Γ l t it ft, is_functional_tm Γ l t it ft)
                          /\ (forall Γ iΓ fΓ, is_functional_ctx Γ iΓ fΓ)
                          /\ (forall Γ l x ix fx, is_functional_proj Γ l x ix fx).
Proof.
  apply interp_mutind.
  - intros Γ l x ix fx IH it ft. inversion ft. subst. now apply IH.
  - intros Γ l it ft. now inversion ft. 
  - intros Γ it ft. now inversion ft.
  - intros Γ lA lB A B iA iB fA IHA fB IHB it ft. inversion ft. subst. f_equal ; auto.
  - intros Γ lB A B iA IB fA IHA fB IHB it ft. inversion ft. subst. f_equal ; auto.
    + f_equal. now apply IHA.
  - intros Γ lA A B iA iB fA IHA fB IHB it ft. inversion ft. subst. f_equal ; auto.
  - intros Γ A B iA iB fA IHA fB IHB it ft. inversion ft. subst. f_equal ; auto.
    + f_equal. now apply IHA.
  - intros Γ lA lB A B t iA it fA IHA ft IHt iu fu. inversion fu. subst. f_equal ; auto.
  - intros Γ lB A B t iA it fA IHA ft IHt iu fu. inversion fu. subst. f_equal ; auto.
    + f_equal. now apply IHA.
  - intros Γ lA lB A B t u iA it iu fA IHA ft IHt fu IHu iv fv. inversion fv. subst. f_equal ; auto.
  - intros Γ lB A B t u iA it iu fA IHA ft IHt fu IHu iv fv. inversion fv. subst. f_equal ; auto.
    + f_equal. now apply IHA.
  - intros Γ iA fA. now inversion fA.
  - intros Γ it ft. now inversion ft.
  - intros Γ t it ft IHt iu fu. inversion fu. subst. f_equal. now apply IHt.
  - intros Γ l P pz ps m iP ipz ips im fP IHP fpz IHpz fps IHps fm IHm it ft.
    inversion ft. subst. clear ft. f_equal ; auto.
  - intros Γ i A R a iA iR ia fA IHA fR IHR fa IHa it ft. inversion ft. subst. f_equal ; auto.
  - intros Γ i l A R a q P p iA iR ia iP ip fA IHA fR IHR fP IHP fp IHp fa IHa it ft.
    inversion ft. subst. f_equal ; auto.
  - intros Γ l A a b iA ia ib fA IHA fa IHa fb IHb iP fP. inversion fP. subst. f_equal ; auto.
  - intros Γ l A B e a iA iB ia fA IHA fB IHB fa IHa it ft.
    inversion ft. subst. f_equal ; auto.
  - intros iΓ fΓ. now inversion fΓ. 
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal ; auto.
  - intros Γ A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal.
    + now apply IHΓ.
    + f_equal. now apply IHA.
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal.
    + now apply IHΓ.
    + refine (f_equal (fun X => (fun γ : ZFSet => 𝕌el l (X γ))) _). now apply IHA.
  - intros Γ l lA A x iΓ iA ix fΓ IHΓ fA IHA fx IHx iy fy. inversion fy. subst.
    refine (f_equal3 (fun X Y Z => (fun γa : ZFSet => X (setFstSigma lA Y (fun γ : ZFSet => 𝕌el lA (Z γ)) γa))) _ _ _) ; auto.
  - intros Γ A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal ; auto.
  - intros Γ l A x iΓ iA ix fΓ IHΓ fA IHA fx IHx iy fy. inversion fy. subst.
    refine (f_equal3 (fun X Y Z => (fun γa : ZFSet => X (setFstSigma 0 Y (fun γ => 𝕌el 0 (boxTy_HO Z γ)) γa))) _ _ _) ; auto.
Qed.

Lemma functional_tm {Γ l} (t : term) {it it'} : interp_tm Γ l t it -> interp_tm Γ l t it' -> it = it'.
Proof.
  intros ft ft'. eapply (proj1 functional_interp). exact ft. exact ft'.
Qed.

Lemma functional_ctx (Γ : ctx) {iΓ iΓ'} : interp_ctx Γ iΓ -> interp_ctx Γ iΓ' -> iΓ = iΓ'.
Proof.
  intros fΓ fΓ'. eapply functional_interp. exact fΓ. exact fΓ'.
Qed.

Lemma functional_nth {Γ l} (x : nat) {ix ix'} : nth_proj Γ l x ix -> nth_proj Γ l x ix' -> ix = ix'.
Proof.
  intros fx fx'. eapply functional_interp. exact fx. exact fx'.
Qed.

(* The interpretation function only depends on the interpretation of the types in Γ, not really on Γ *)
(* This could be trivial if we used graphs instead of higher-order functions -- this is the price to
   pay for a nicer substitution calculus *)

Inductive same_ctx : ctx -> ctx -> Prop :=
| same_empty : same_ctx ∙ ∙

| same_cons : forall Γ1 Γ2 l A1 A2 iΓ iA1 iA2, same_ctx Γ1 Γ2 
                  -> interp_ctx Γ1 iΓ -> interp_tm Γ1 (Ax l) A1 iA1 -> interp_tm Γ2 (Ax l) A2 iA2
                  -> (∀ γ ∈ iΓ, iA1 γ ≡ iA2 γ) -> same_ctx (Γ1 ,, (l , A1)) (Γ2 ,, (l , A2)).

Inductive BoxS (A : SProp) : Prop :=
| boxS : A -> BoxS A.

Definition is_same_ctx_ctx (Γ : ctx) (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ) : Prop :=
  BoxS (forall Γ' iΓ', same_ctx Γ Γ' -> interp_ctx Γ' iΓ' -> iΓ ≡ iΓ').

Definition is_same_ctx_tm (Γ : ctx) (l : level) (t : term) (it : ZFSet -> ZFSet) (ft : interp_tm Γ l t it) : Prop :=
  BoxS (forall Γ' iΓ it', same_ctx Γ Γ' -> interp_ctx Γ iΓ -> interp_tm Γ' l t it' -> forall γ, γ ∈ iΓ -> it γ ≡ it' γ).

Definition is_same_ctx_proj (Γ : ctx) (l : level) (x : nat) (ix : ZFSet -> ZFSet) (fx : nth_proj Γ l x ix) : Prop :=
  BoxS (forall Γ' iΓ ix', same_ctx Γ Γ' -> interp_ctx Γ iΓ -> nth_proj Γ' l x ix' -> forall γ, γ ∈ iΓ -> ix γ ≡ ix' γ).

Lemma is_same_ctx : (forall Γ l t it ft, is_same_ctx_tm Γ l t it ft)
                    /\ (forall Γ iΓ fΓ, is_same_ctx_ctx Γ iΓ fΓ)
                    /\ (forall Γ l x ix fx, is_same_ctx_proj Γ l x ix fx).
Proof.
  apply interp_mutind.
  - intros Γ l x ix fx IHx. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'. inversion ft' ; subst ; clear ft'.
    destruct IHx as [ IHx ]. apply (IHx Γ' iΓ it' HΓΓ' fΓ H2).
  - intros Γ l. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'. inversion ft' ; subst ; clear ft'. easy.
  - intros Γ. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'. inversion ft' ; subst ; clear ft'. easy.
  - intros Γ lA lB A B iA iB fA IHA fB IHB. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHB as [ IHB ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γa ∈ ctxExt lA iΓ iA, iB γa ≡ iB0 γa) as HBB0.
    { refine (IHB (Γ',, (ty lA, A)) (ctxExt lA iΓ iA) iB0 _ _ _).
      - apply (same_cons Γ Γ' (ty lA) A A iΓ iA iA0 HΓΓ' fΓ fA H6 HAA0).
      - now eapply interp_cons_rel.
      - exact H7. }
    now apply piTy_HO_cong.
  - intros Γ lB A B iA iB fA IHA fB IHB. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHB as [ IHB ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γa ∈ ctxExt 0 iΓ (boxTy_HO iA), iB γa ≡ iB0 γa) as HBB0.
    { refine (IHB (Γ',, (prop, A)) (ctxExt 0 iΓ (boxTy_HO iA)) iB0 _ _ _).
      - refine (same_cons Γ Γ' prop A A iΓ iA iA0 HΓΓ' fΓ fA H3 HAA0).
      - now eapply interp_cons_irr.
      - exact H5. }
    apply piTy_HO_cong. unfold boxTy_HO. intros γ Hγ. destruct (HAA0 γ Hγ). reflexivity. exact HBB0.
  - intros Γ lA A B iA iB fA IHA fB IHB. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHB as [ IHB ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γa ∈ ctxExt lA iΓ iA, iB γa ≡ iB0 γa) as HBB0.
    { refine (IHB (Γ',, (ty lA, A)) (ctxExt lA iΓ iA) iB0 _ _ _).
      - apply (same_cons Γ Γ' (ty lA) A A iΓ iA iA0 HΓΓ' fΓ fA H3 HAA0).
      - now eapply interp_cons_rel.
      - exact H5. }
    now apply forallTy_HO_cong. 
  - intros Γ A B iA iB fA IHA fB IHB. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHB as [ IHB ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γa ∈ ctxExt 0 iΓ (boxTy_HO iA), iB γa ≡ iB0 γa) as HBB0.
    { refine (IHB (Γ',, (prop, A)) (ctxExt 0 iΓ (boxTy_HO iA)) iB0 _ _ _).
      - refine (same_cons Γ Γ' prop A A iΓ iA iA0 HΓΓ' fΓ fA H2 HAA0).
      - now eapply interp_cons_irr.
      - exact H3. }
    apply forallTy_HO_cong. unfold boxTy_HO. intros γ Hγ. destruct (HAA0 γ Hγ). reflexivity. exact HBB0.
  - intros Γ lA lB A B t iA it fA IHA ft IHt. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHt as [ IHt ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γa ∈ ctxExt lA iΓ iA, it γa ≡ it0 γa) as Htt0.
    { refine (IHt (Γ',, (ty lA, A)) (ctxExt lA iΓ iA) it0 _ _ _).
      - refine (same_cons Γ Γ' (ty lA) A A iΓ iA iA0 HΓΓ' fΓ fA H7 HAA0).
      - now eapply interp_cons_rel.
      - exact H8. }
    now apply lamTm_HO_cong.
  - intros Γ lB A B t iA it fA IHA ft IHt. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHt as [ IHt ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γa ∈ ctxExt 0 iΓ (boxTy_HO iA), it γa ≡ it0 γa) as Htt0.
    { refine (IHt (Γ',, (prop, A)) (ctxExt 0 iΓ (boxTy_HO iA)) it0 _ _ _).
      - refine (same_cons Γ Γ' prop A A iΓ iA iA0 HΓΓ' fΓ fA H5 HAA0).
      - now eapply interp_cons_irr.
      - exact H6. }
    apply lamTm_HO_cong. unfold boxTy_HO. intros γ Hγ. destruct (HAA0 γ Hγ). reflexivity. exact Htt0.
  - intros Γ lA lB A B t u iA it iu fA IHA ft IHt fu IHu. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHt as [ IHt ]. destruct IHu as [ IHu ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γ ∈ iΓ, it γ ≡ it0 γ) as Htt0. now apply (IHt Γ').
    assert (∀ γ ∈ iΓ, iu γ ≡ iu0 γ) as Huu0. now apply (IHu Γ').
    now apply appTm_HO_cong.
  - intros Γ lB A B t u iA it iu fA IHA ft IHt fu IHu. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHt as [ IHt ]. destruct IHu as [ IHu ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γ ∈ iΓ, it γ ≡ it0 γ) as Htt0. now apply (IHt Γ').
    assert (∀ γ ∈ iΓ, iu γ ≡ iu0 γ) as Huu0. now apply (IHu Γ').
    apply appTm_HO_cong. unfold boxTy_HO. intros γ Hγ. destruct (HAA0 γ Hγ). reflexivity. exact Htt0. exact Huu0.
  - intros Γ. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'. inversion ft' ; subst ; clear ft'. easy.
  - intros Γ. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'. inversion ft' ; subst ; clear ft'. easy.
  - intros Γ t it ft IHt. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'. inversion ft' ; subst ; clear ft'.
    destruct IHt as [ IHt ]. assert (∀ γ ∈ iΓ, it γ ≡ it0 γ) as Htt0. now apply (IHt Γ').
    unfold sucTm_HO. intros γ Hγ. destruct (Htt0 γ Hγ). reflexivity.
  - intros Γ l P pz ps m iP ipz ips im fP IHP fpz IHpz fps IHps fm IHm. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHP as [ IHP ]. destruct IHpz as [ IHpz ]. destruct IHps as [ IHps ]. destruct IHm as [ IHm ].
    inversion ft' ; subst ; clear ft'.
    assert (∀ γa ∈ ctxExt 0 iΓ natTy_HO, iP γa ≡ iP0 γa) as HPP0.
    { refine (IHP (Γ',, (ty 0, Nat)) (ctxExt 0 iΓ natTy_HO) iP0 _ _ _).
      - refine (same_cons Γ Γ' (ty 0) Nat Nat iΓ natTy_HO natTy_HO HΓΓ' fΓ _ _ _).
        + now apply interp_nat.
        + now apply interp_nat.
        + intros ; reflexivity.
      - apply interp_cons_rel. exact fΓ. now apply interp_nat.
      - exact H5. }
    assert (∀ γ ∈ iΓ, ipz γ ≡ ipz0 γ) as Hpzpz0. now apply (IHpz Γ').
    assert (∀ γ ∈ iΓ, im γ ≡ im0 γ) as Hmm0. now apply (IHm Γ').
    assert (∀ γaa ∈ ctxExt l (ctxExt 0 iΓ natTy_HO) iP, ips γaa ≡ ips0 γaa) as Hpsps0.
    { refine (IHps (Γ',, (ty 0, Nat),, (ty l, P)) (ctxExt l (ctxExt 0 iΓ natTy_HO) iP) ips0 _ _ _).
      - refine (same_cons (Γ,, (ty 0, Nat)) (Γ',, (ty 0, Nat)) (ty l) P P _ iP iP0 _ _ _ _ _).
        + refine (same_cons Γ Γ' (ty 0) Nat Nat iΓ natTy_HO natTy_HO HΓΓ' fΓ _ _ _).
          * now apply interp_nat.
          * now apply interp_nat.
          * intros ; reflexivity.
        + apply interp_cons_rel. exact fΓ. now apply interp_nat.
        + exact fP.
        + exact H5.
        + apply HPP0.
      - apply interp_cons_rel.
        + apply interp_cons_rel. exact fΓ. now apply interp_nat.
        + exact fP.
      - exact H8. }
    now apply natrecTm_HO_cong.
  - intros Γ i A R a iA iR ia fA IHA fR IHR fa IHa. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHR as [ IHR ]. destruct IHa as [ IHa ]. 
    inversion ft' ; subst ; clear ft'.
    assert (∀ γ ∈ iΓ, iA γ ≡ iA0 γ) as HAA0. now apply (IHA Γ').
    assert (∀ γ ∈ iΓ, ia γ ≡ ia0 γ) as Haa0. now apply (IHa Γ').
    assert (∀ γaa ∈ ctxExt2 i iΓ iA, iR γaa ≡ iR0 γaa) as HRR0.
    { refine (IHR (Γ',, (ty i, A),, (ty i, S ⋅ A)) (ctxExt2 i iΓ iA) iR0 _ _ _).
      - refine (same_cons (Γ,, (ty i, A)) (Γ',, (ty i, A)) (ty i) (S ⋅ A) (S ⋅ A) _ (fun γa => iA (ctx_wk i iΓ iA γa)) (fun γa => iA0 (ctx_wk i iΓ iA0 γa)) _ _ _ _ _).
        + refine (same_cons Γ Γ' (ty i) A A iΓ iA iA0 HΓΓ' fΓ fA H4 HAA0).
        + apply interp_cons_rel. exact fΓ. exact fA.
        + admit.
        + admit.
        + intros γa Hγa. apply HAA0. unfold ctx_wk. apply setFstSigma_typing.
          * intros ; now apply 𝕌el_typing'.
          * refine (transpS (fun X => γa ∈ X) _ Hγa). apply setSigma_cong.
            intros γ Hγ. refine (fequal (𝕌el i) _). now apply HAA0.
      - apply interp_cons_rel.
        + now apply interp_cons_rel. 
        + admit.
      - exact H6. }
    eapply accTy_HO_cong. exact HAA0. exact HRR0. exact Haa0.
  - admit.
  - intros Γ l A a b iA ia ib fA IHA fa IHa fb IHb. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHA as [ IHA ]. destruct IHa as [ IHa ]. destruct IHb as [ IHb ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, ia γ ≡ ia0 γ) as Haa0. now apply (IHa Γ').
    assert (∀ γ ∈ iΓ, ib γ ≡ ib0 γ) as Hbb0. now apply (IHb Γ').
    now apply eqTy_HO_cong.
  - intros Γ l A B e a iA iB ia fA IHA fB IHB fa IHa. apply boxS. intros Γ' iΓ it' HΓΓ' fΓ ft'.
    destruct IHa as [ IHa ]. inversion ft' ; subst ; clear ft'. 
    assert (∀ γ ∈ iΓ, ia γ ≡ ia0 γ) as Haa0. now apply (IHa Γ').
    exact Haa0.
  - apply boxS. intros Γ' iΓ' HΓΓ' fΓ'. inversion HΓΓ' ; subst ; clear HΓΓ'.
    inversion fΓ' ; subst ; clear fΓ'. reflexivity.
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA. apply boxS. intros Γ' iΓ' HΓΓ' fΓ'.
    destruct IHΓ as [ IHΓ ]. destruct IHA as [ IHA ].
    inversion HΓΓ' ; subst ; clear HΓΓ'. destruct (functional_ctx Γ fΓ H3) ; clear H3.
    destruct (functional_tm A fA H4) ; clear H4. inversion fΓ' ; subst ; clear fΓ'.
    destruct (functional_tm A2 H6 H5) ; clear H5.    
    assert (iΓ ≡ iΓ0) as HΓΓ0. now apply (IHΓ Γ2). destruct HΓΓ0.
    unfold ctxExt. apply setSigma_cong. intros γ Hγ. refine (fequal (𝕌el l) _). now apply H7.
  - intros Γ A iΓ iA fΓ IHΓ fA IHA. apply boxS. intros Γ' iΓ' HΓΓ' fΓ'.
    destruct IHΓ as [ IHΓ ]. destruct IHA as [ IHA ].
    inversion HΓΓ' ; subst ; clear HΓΓ'. destruct (functional_ctx Γ fΓ H3) ; clear H3.
    destruct (functional_tm A fA H4) ; clear H4. inversion fΓ' ; subst ; clear fΓ'.
    destruct (functional_tm A2 H6 H4) ; clear H4.
    assert (iΓ ≡ iΓ0) as HΓΓ0. now apply (IHΓ Γ2). destruct HΓΓ0.
    unfold ctxExt. apply setSigma_cong. intros γ Hγ. unfold boxTy_HO.
    refine (fequal (fun X => 𝕌el 0 ⟨ X ; _ ⟩) _). now apply H7.
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA. apply boxS. intros Γ' iΓ' ix HΓΓ' fΓ' fx.
    destruct IHΓ as [ IHΓ ]. destruct IHA as [ IHA ].
    inversion fx ; subst ; clear fx. inversion HΓΓ' ; subst ; clear HΓΓ'.
    destruct (functional_ctx Γ fΓ H7) ; clear H7. destruct (functional_tm A0 H2 H9) ; clear H9.
    destruct (functional_tm A fA H8) ; clear H8. inversion fΓ' ; subst ; clear fΓ'.
    destruct (functional_ctx Γ fΓ H5) ; clear H5. destruct (functional_tm A fA H7) ; clear H7.
    assert (iΓ ≡ iΓ0) as HΓΓ0. now apply (IHΓ Γ0). destruct HΓΓ0. intros γ Hγ.
    unfold setSndSigma. refine (fequal (fun X => setSndPair iΓ X γ) _). apply setFamUnion_cong.
    clear γ Hγ. intros γ Hγ. refine (fequal (𝕌el l) _). now apply H10.
  - intros Γ l lA A x iΓ iA ix fΓ IHΓ fA IHA fx IHx. apply boxS. intros Γ' iΓ' ix' HΓΓ' fΓ' fx'.
    destruct IHΓ as [ IHΓ ]. destruct IHA as [ IHA ]. destruct IHx as [ IHx ].
    inversion HΓΓ' ; subst ; clear HΓΓ'. inversion fx' ; subst ; clear fx'. 
    destruct (functional_ctx Γ fΓ H3) ; clear H3. destruct (functional_tm A2 H6 H11) ; clear H11.
    destruct (functional_tm A fA H4) ; clear H4. inversion fΓ' ; subst ; clear fΓ'.
    destruct (functional_ctx Γ fΓ H4) ; clear H4. destruct (functional_tm A fA H5) ; clear H5.
    assert (iΓ ≡ iΓ1) as HΓΓ0. now apply (IHΓ Γ2). destruct HΓΓ0.
    assert (∀ γ ∈ iΓ, ix γ ≡ ix0 γ) as Hxx0. now apply (IHx Γ2). intros γ Hγ.
    assert ((setFstSigma lA iΓ (fun γ0 : ZFSet => 𝕌el lA (iA γ0)) γ) ≡ (setFstSigma lA iΓ (fun γ0 : ZFSet => 𝕌el lA (iA2 γ0)) γ)).
    { unfold setFstSigma. refine (fequal (fun X => setFstPair iΓ X γ) _). apply setFamUnion_cong.
      clear γ Hγ. intros γ Hγ. refine (fequal (𝕌el lA) _). now apply H7. } destruct H. apply Hxx0.
    unfold setFstSigma. apply setFstPair_typing. apply ZFincomp in Hγ. now destruct Hγ.
  - intros Γ A iΓ iA fΓ IHΓ fA IHA. apply boxS. intros Γ' iΓ' ix HΓΓ' fΓ' fx.
    destruct IHΓ as [ IHΓ ]. destruct IHA as [ IHA ].
    inversion fx ; subst ; clear fx. inversion HΓΓ' ; subst ; clear HΓΓ'.
    destruct (functional_ctx Γ fΓ H7) ; clear H7. destruct (functional_tm A0 H0 H9) ; clear H9.
    destruct (functional_tm A fA H8) ; clear H8. inversion fΓ' ; subst ; clear fΓ'.
    destruct (functional_ctx Γ fΓ H3) ; clear H3. destruct (functional_tm A fA H5) ; clear H5.
    assert (iΓ ≡ iΓ0) as HΓΓ0. now apply (IHΓ Γ0). destruct HΓΓ0. intros γ Hγ.
    unfold setSndSigma. refine (fequal (fun X => setSndPair iΓ X γ) _). now apply setFamUnion_cong.
  - intros Γ l A x iΓ iA ix fΓ IHΓ fA IHA fx IHx. apply boxS. intros Γ' iΓ' ix' HΓΓ' fΓ' fx'.
    destruct IHΓ as [ IHΓ ]. destruct IHA as [ IHA ]. destruct IHx as [ IHx ].
    inversion HΓΓ' ; subst ; clear HΓΓ'. inversion fx' ; subst ; clear fx'. 
    destruct (functional_ctx Γ fΓ H3) ; clear H3. destruct (functional_tm A2 H6 H9) ; clear H9.
    destruct (functional_tm A fA H4) ; clear H4. inversion fΓ' ; subst ; clear fΓ'.
    destruct (functional_ctx Γ fΓ H1) ; clear H1. destruct (functional_tm A fA H4) ; clear H4.
    assert (iΓ ≡ iΓ1) as HΓΓ0. now apply (IHΓ Γ2). destruct HΓΓ0.
    assert (∀ γ ∈ iΓ, ix γ ≡ ix0 γ) as Hxx0. now apply (IHx Γ2). intros γ Hγ.
    assert ((setFstSigma 0 iΓ iA γ) ≡ (setFstSigma 0 iΓ iA2 γ)).
    { unfold setFstSigma. refine (fequal (fun X => setFstPair iΓ X γ) _). now apply setFamUnion_cong. }
    destruct H. apply Hxx0. unfold setFstSigma. apply setFstPair_typing. apply ZFincomp in Hγ. 
    destruct Hγ as [ Hγ _ ]. refine (transpS (fun X => γ ∈ iΓ × X) _ Hγ). apply setFamUnion_cong.
    clear γ Hγ. intros γ Hγ. unfold 𝕌el. unfold boxTy_HO. now destruct (H7 γ Hγ).
Admitted.    

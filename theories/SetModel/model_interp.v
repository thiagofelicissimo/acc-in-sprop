From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

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
              -> nth_proj (Γ ,, (prop , A)) l (S x) (fun γa => ix (setFstSigma 0 iΓ iA γa))

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

| interp_acc : forall Γ i A R a iA iR ia, interp_tm Γ (Ax i) A iA
               -> interp_tm (Γ ,, (i, A) ,, (i, S ⋅ A)) (Ax prop) R iR
               -> interp_tm Γ i a ia
               -> interp_tm Γ (Ax prop) (Core.acc i A R a) (accTy_HO iA iR ia)

| interp_accelim : forall Γ i l A R a q P p iA iR ia iP ip, interp_tm Γ (Ax i) A iA
                   -> interp_tm (Γ ,, (i, A) ,, (i, S ⋅ A)) (Ax prop) R iR
                   -> interp_tm (Γ ,, (i, A)) (Ax (ty l)) P iP
                   -> interp_tm Γ (ty l) p ip
                   -> interp_tm Γ i a ia
                   -> interp_tm Γ (ty l) (accel i (ty l) A R P p a q) (accelimTm_HO l iA iR iP ip ia)

| interp_obseq_r : forall Γ l A a b iA ia ib, interp_tm Γ (Ax (ty l)) A iA
                   -> interp_tm Γ (ty l) a ia
                   -> interp_tm Γ (ty l) b ib
                   -> interp_tm Γ (Ax prop) (obseq (ty l) A a b) (eqTy_HO iA ia ib)

| interp_obseq_i : forall Γ A a b, interp_tm Γ (Ax prop) (obseq prop A a b) (fun _ => ⋆)

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
  - intros Γ A a b iP fP. now inversion fP. 
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
    refine (f_equal3 (fun X Y Z => (fun γa : ZFSet => X (setFstSigma 0 Y Z γa))) _ _ _) ; auto.
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

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
                    -> interp_ctx (Γ ,, (prop , A)) (ctxExt 0 iΓ (boxTy_cl iΓ iA))

with nth_proj : forall (Γ : ctx) (l : level) (x : nat), (ZFSet -> ZFSet) -> Prop :=

| here_rel : forall Γ l A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty l)) A iA
             -> nth_proj (Γ ,, (ty l , A)) (ty l) 0 (ctx_var0 l iΓ iA)

| there_rel : forall Γ l lA A x iΓ iA ix, interp_ctx Γ iΓ -> interp_tm Γ (Ax (ty lA)) A iA -> nth_proj Γ l x ix
              -> nth_proj (Γ ,, (ty lA , A)) l (S x) (fun γa => ix (ctx_wk lA iΓ iA γa))

| here_irr : forall Γ A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA
             -> nth_proj (Γ ,, (prop , A)) prop 0 (ctx_var0 0 iΓ (boxTy_cl iΓ iA))

| there_irr : forall Γ l A x iΓ iA ix, interp_ctx Γ iΓ -> interp_tm Γ (ty 0) A iA -> nth_proj Γ l x ix
              -> nth_proj (Γ ,, (prop , A)) l (S x) (fun γa => ix (ctx_wk 0 iΓ (boxTy_cl iΓ iA) γa))

with interp_tm : forall (Γ : ctx) (l : level) (A : term), (ZFSet -> ZFSet) -> Prop :=

| interp_var : forall Γ l x ix, nth_proj Γ l x ix
               -> interp_tm Γ l (var x) ix

| interp_type : forall Γ iΓ l, interp_ctx Γ iΓ
                -> interp_tm Γ (Ax (Ax (ty l))) (Sort (ty l)) (univTy_cl l iΓ)

| interp_prop : forall Γ iΓ, interp_ctx Γ iΓ
                -> interp_tm Γ (ty 1) (Sort prop) (propTy_cl iΓ)

| interp_pi_rr : forall Γ iΓ lA lB A B iA iB, interp_ctx Γ iΓ
                 -> interp_tm Γ (Ax (ty lA)) A iA
                 -> interp_tm (Γ ,, (ty lA , A)) (Ax (ty lB)) B iB
                 -> interp_tm Γ (Ax (Ru (ty lA) (ty lB))) (Pi (ty lA) (ty lB) A B) 
                              (piTy_cl iΓ lA lB iA iB)

| interp_pi_ir : forall Γ iΓ lB A B iA iB, interp_ctx Γ iΓ
                 -> interp_tm Γ (Ax prop) A iA
                 -> interp_tm (Γ ,, (prop , A)) (Ax (ty lB)) B iB
                 -> interp_tm Γ (Ax (ty lB)) (Pi prop (ty lB) A B)
                              (piTy_cl iΓ 0 lB (boxTy_cl iΓ iA) iB)

| interp_pi_ri : forall Γ iΓ lA A B iA iB, interp_ctx Γ iΓ
                 -> interp_tm Γ (Ax (ty lA)) A iA
                 -> interp_tm (Γ ,, (ty lA , A)) (Ax prop) B iB
                 -> interp_tm Γ (Ax prop) (Pi (ty lA) prop A B) 
                              (forallTy_cl iΓ lA iA iB)

| interp_pi_ii : forall Γ iΓ A B iA iB, interp_ctx Γ iΓ
                 -> interp_tm Γ (Ax prop) A iA
                 -> interp_tm (Γ ,, (prop , A)) (Ax prop) B iB
                 -> interp_tm Γ (Ax prop) (Pi prop prop A B)
                              (forallTy_cl iΓ 0 (boxTy_cl iΓ iA) iB)

| interp_lam_rr : forall Γ iΓ lA lB A B t iA it, interp_ctx Γ iΓ
                  -> interp_tm Γ (Ax (ty lA)) A iA
                  -> interp_tm (Γ ,, (ty lA , A)) (ty lB) t it
                  -> interp_tm Γ (Ru (ty lA) (ty lB)) (lam (ty lA) (ty lB) A B t) (lamTm_cl iΓ lA lB iA it)

| interp_lam_ir : forall Γ iΓ lB A B t iA it, interp_ctx Γ iΓ
                  -> interp_tm Γ (Ax prop) A iA
                  -> interp_tm (Γ ,, (prop , A)) (ty lB) t it
                  -> interp_tm Γ (ty lB) (lam prop (ty lB) A B t) (lamTm_cl iΓ 0 lB (boxTy_cl iΓ iA) it)

| interp_app_rr : forall Γ iΓ lA lB A B t u iA it iu, interp_ctx Γ iΓ
                  -> interp_tm Γ (Ax (ty lA)) A iA
                  -> interp_tm Γ (Ru (ty lA) (ty lB)) t it
                  -> interp_tm Γ (ty lA) u iu
                  -> interp_tm Γ (ty lB) (app (ty lA) (ty lB) A B t u) (appTm_cl iΓ lA lB iA it iu)

| interp_app_ir : forall Γ iΓ lB A B t u iA it iu, interp_ctx Γ iΓ
                  -> interp_tm Γ (Ax prop) A iA
                  -> interp_tm Γ (ty lB) t it
                  -> interp_tm Γ prop u iu
                  -> interp_tm Γ (ty lB) (app prop (ty lB) A B t u) (appTm_cl iΓ 0 lB (boxTy_cl iΓ iA) it iu)

| interp_nat : forall Γ iΓ, interp_ctx Γ iΓ ->
               interp_tm Γ (ty 1) Nat (natTy_cl iΓ)

| interp_zero : forall Γ iΓ, interp_ctx Γ iΓ ->
                interp_tm Γ (ty 0) zero (zeroTm_cl iΓ)

| interp_succ : forall Γ iΓ t it, interp_ctx Γ iΓ
                -> interp_tm Γ (ty 0) t it
                -> interp_tm Γ (ty 0) (succ t) (sucTm_cl iΓ it)

| interp_natrec : forall Γ iΓ l P pz ps m iP ipz ips im, interp_ctx Γ iΓ
                  -> interp_tm (Γ ,, (ty 0 , Nat)) (Ax (ty l)) P iP
                  -> interp_tm Γ (ty l) pz ipz
                  -> interp_tm (Γ ,, (ty 0 , Nat) ,, (ty l , P)) (ty l) ps ips
                  -> interp_tm Γ (ty 0) m im
                  -> interp_tm Γ (ty l) (rec (ty l) P pz ps m) (natrecTm_cl iΓ l iP ipz ips im)

| interp_acc : forall Γ iΓ i A R a iA iR ia, interp_ctx Γ iΓ
               -> interp_tm Γ (Ax (ty i)) A iA
               -> interp_tm (Γ ,, (ty i, A) ,, (ty i, S ⋅ A)) (Ax prop) R iR
               -> interp_tm Γ (ty i) a ia
               -> interp_tm Γ (Ax prop) (Core.acc (ty i) A R a) (accTy_cl iΓ iA iR ia)

| interp_accelim : forall Γ iΓ i l A R a q P p iA iR ia iP ip, interp_ctx Γ iΓ
                   -> interp_tm Γ (Ax i) A iA
                   -> interp_tm (Γ ,, (i, A) ,, (i, S ⋅ A)) (Ax prop) R iR
                   -> interp_tm (Γ ,, (i, A)) (Ax (ty l)) P iP
                   -> interp_tm Γ (ty l) p ip
                   -> interp_tm Γ i a ia
                   -> interp_tm Γ (ty l) (accel i (ty l) A R P p a q) (accelimTm_cl iΓ l iA iR iP ip ia)

| interp_obseq : forall Γ iΓ l A a b iA ia ib, interp_ctx Γ iΓ
                   -> interp_tm Γ (Ax (ty l)) A iA
                   -> interp_tm Γ (ty l) a ia
                   -> interp_tm Γ (ty l) b ib
                   -> interp_tm Γ (Ax prop) (obseq (ty l) A a b) (eqTy_cl iΓ iA ia ib)

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
  - intros Γ iΓ l fΓ IHΓ it ft. inversion ft ; f_equal ; auto.
  - intros Γ iΓ fΓ IHΓ it ft. inversion ft ; f_equal ; auto.
  - intros Γ iΓ lA lB A B iA iB fΓ IHΓ fA IHA fB IHB it ft. inversion ft ; subst. f_equal ; auto.
  - intros Γ iΓ lB A B iA IB fΓ IHΓ fA IHA fB IHB it ft. inversion ft ; subst. f_equal ; auto.
    + f_equal. now apply IHΓ. now apply IHA.
  - intros Γ iΓ lA A B iA iB fΓ IHΓ fA IHA fB IHB it ft. inversion ft ; subst. f_equal ; auto.
  - intros Γ iΓ A B iA iB fΓ IHΓ fA IHA fB IHB it ft. inversion ft ; subst. f_equal ; auto.
    + f_equal. now apply IHΓ. now apply IHA.
  - intros Γ iΓ lA lB A B t iA it fΓ IHΓ fA IHA ft IHt iu fu. inversion fu ; subst. f_equal ; auto.
  - intros Γ iΓ lB A B t iA it fΓ IHΓ fA IHA ft IHt iu fu. inversion fu ; subst. f_equal ; auto.
    + f_equal. now apply IHΓ. now apply IHA.
  - intros Γ iΓ lA lB A B t u iA it iu fΓ IHΓ fA IHA ft IHt fu IHu iv fv. inversion fv ; subst. f_equal ; auto.
  - intros Γ iΓ lB A B t u iA it iu fΓ IHΓ fA IHA ft IHt fu IHu iv fv. inversion fv ; subst. f_equal ; auto.
    + f_equal. now apply IHΓ. now apply IHA.
  - intros Γ iΓ fΓ IHΓ iA fA. inversion fA ; subst ; clear fA. f_equal ; auto. 
  - intros Γ iΓ fΓ IHΓ it ft. inversion ft ; subst ; clear ft. f_equal ; auto.
  - intros Γ iΓ t it fΓ IHΓ ft IHt iu fu. inversion fu ; subst ; clear fu. f_equal ; auto.
  - intros Γ iΓ l P pz ps m iP ipz ips im fΓ IHΓ fP IHP fpz IHpz fps IHps fm IHm it ft.
    inversion ft. subst. clear ft. f_equal ; auto.
  - intros Γ iΓ i A R a iA iR ia fΓ IHΓ fA IHA fR IHR fa IHa it ft. inversion ft. subst. f_equal ; auto.
  - intros Γ iΓ i l A R a q P p iA iR ia iP ip fΓ IHΓ fA IHA fR IHR fP IHP fp IHp fa IHa it ft.
    inversion ft. subst. f_equal ; auto.
  - intros Γ iΓ l A a b iA ia ib fΓ IHΓ fA IHA fa IHa fb IHb iP fP. inversion fP. subst. f_equal ; auto.
  - intros Γ l A B e a iA iB ia fA IHA fB IHB fa IHa it ft.
    inversion ft. subst. f_equal ; auto.
  - intros iΓ fΓ. now inversion fΓ. 
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal ; auto.
  - intros Γ A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal.
    + now apply IHΓ.
    + f_equal. now apply IHΓ. now apply IHA.
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ ; subst ; clear fΔ. f_equal ; auto.
  - intros Γ l lA A x iΓ iA ix fΓ IHΓ fA IHA fx IHx iy fy. inversion fy. subst.
    refine (f_equal3 (fun X Y Z => (fun γa : ZFSet => X (ctx_wk lA Y Z γa))) _ _ _) ; auto.
  - intros Γ A iΓ iA fΓ IHΓ fA IHA iΔ fΔ. inversion fΔ. subst. f_equal ; auto. f_equal ; auto.
  - intros Γ l A x iΓ iA ix fΓ IHΓ fA IHA fx IHx iy fy. inversion fy. subst.
    refine (f_equal3 (fun X Y Z => (fun γa : ZFSet => X (ctx_wk 0 Y (boxTy_cl Y Z) γa))) _ _ _) ; auto.
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

(* The interpreted terms satisfy "restricted function extensionality", i.e.
   if two interpreted terms in context Γ are equal on all elements of Γ, then
   they are equal on the nose. *)

Inductive is_clipped_ctx (Γ : ctx) (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ) : Prop :=
| mkIsClippedCtx : forall n, iΓ ∈ 𝕍 n -> is_clipped_ctx Γ iΓ fΓ.

Inductive is_clipped_tm (Γ : ctx) (l : level) (t : term) (it : ZFSet -> ZFSet) (ft : interp_tm Γ l t it) : Prop :=
| mkIsClippedTm : (forall iΓ (fΓ : interp_ctx Γ iΓ), is_clipped iΓ it) -> is_clipped_tm Γ l t it ft.

Inductive is_clipped_proj (Γ : ctx) (l : level) (x : nat) (ix : ZFSet -> ZFSet) (fx : nth_proj Γ l x ix) : Prop :=
| mkIsClippedProj : (forall iΓ (fΓ : interp_ctx Γ iΓ), is_clipped iΓ ix) -> is_clipped_proj Γ l x ix fx.

Lemma clipped_interp : (forall Γ l t it ft, is_clipped_tm Γ l t it ft)
                       /\ (forall Γ iΓ fΓ, is_clipped_ctx Γ iΓ fΓ)
                       /\ (forall Γ l x ix fx, is_clipped_proj Γ l x ix fx).
Proof.
  apply interp_mutind.
  - intros Γ l x ix fx IHx. constructor. intros iΓ fΓ. destruct IHx. now apply H.
  - intros ? ? ? fΓ IHΓ. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? fΓ IHΓ. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA fB IHB. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? fΓ IHΓ fA IHA fB IHB. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? fΓ IHΓ fA IHA fB IHB. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? fΓ IHΓ fA IHA fB IHB. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA ft IHt. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA ft IHt. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA ft IHt fu IHu. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA ft IHt fu IHu. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? fΓ IHΓ. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? fΓ IHΓ. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? fΓ IHΓ ft IHt. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? ? ? fΓ IHΓ fP IHP fpz IHpz fps IHps fm IHm. constructor. intros.
    destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0. apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA fR IHR fa IHa. constructor. intros.
    destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0. apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA fR IHR fa IHa fP IHP fp IHp. constructor. intros.
    destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0. apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? fΓ IHΓ fA IHA fa IHa fb IHb. constructor. intros. destruct (functional_ctx Γ fΓ fΓ0) ; clear fΓ0.
    apply clipped_clip.
  - intros ? ? ? ? ? ? ? ? ? fA IHA fB IHB fa IHa. constructor. intros. unfold castTm_HO. now apply IHa.
  - unshelve econstructor. exact 0. apply ZFuniv_pair.
    1,2: eapply ZFuniv_trans. 1,3: apply zero_typing. 1,2:apply ZFuniv_uncountable. 
  - intros Γ l A iΓ iA fΓ IHΓ fA IHA. destruct IHΓ. unshelve econstructor.
    exact (max n l). unfold ctxExt. apply setSigma_typing'. exact H. 
  - intros Γ A iΓ iA fΓ IHΓ fA IHA. destruct IHΓ. unshelve econstructor.
    exact (max n 0). unfold ctxExt. apply setSigma_typing'. exact H. 
  - intros Γ l A iΓ iA fΓ _ fA IHA. constructor. intros iΓ0 fΓ0.
    inversion fΓ0 ; subst ; clear fΓ0. destruct (functional_ctx Γ fΓ H3) ; clear H3.
    destruct (functional_tm A fA H4) ; clear H4. apply clipped_clip.
  - intros Γ l lA A x iΓ iA ix fΓ IHΓ fA IHA fx IHx. constructor. intros iΓ0 fΓ0.
    inversion fΓ0 ; subst ; clear fΓ0. destruct (functional_ctx Γ fΓ H3) ; clear H3.
    destruct (functional_tm A fA H4) ; clear H4. intros γa Hγa. destruct IHx. apply (H iΓ fΓ). unfold ctx_wk.
    destruct (sym (clip_outside (ctxExt lA iΓ iA) (setFstSigma lA iΓ (fun γ : ZFSet => 𝕌el lA (iA γ))) γa Hγa)).
    destruct IHΓ as [ n H1 ]. intro H0. eapply (atom_not_in_univ n). eapply ZFuniv_trans. exact H0. exact H1.
  - intros Γ A iΓ iA fΓ _ fA IHA. constructor. intros iΓ0 fΓ0.
    inversion fΓ0 ; subst ; clear fΓ0. destruct (functional_ctx Γ fΓ H1) ; clear H1.
    destruct (functional_tm A fA H3) ; clear H3. apply clipped_clip.
  - intros Γ l A x iΓ iA ix fΓ IHΓ fA IHA fx IHx. constructor. intros iΓ0 fΓ0.
    inversion fΓ0 ; subst ; clear fΓ0. destruct (functional_ctx Γ fΓ H1) ; clear H1.
    destruct (functional_tm A fA H3) ; clear H3. intros γa Hγa. destruct IHx. apply (H iΓ fΓ). unfold ctx_wk.
    destruct (sym (clip_outside (ctxExt 0 iΓ (boxTy_cl iΓ iA)) (setFstSigma 0 iΓ (fun γ : ZFSet => 𝕌el 0 (boxTy_cl iΓ iA γ))) γa Hγa)).
    destruct IHΓ as [ n H1 ]. intro H0. eapply (atom_not_in_univ n). eapply ZFuniv_trans. exact H0. exact H1.
Qed.

Lemma clipped_interp_tm {Γ : ctx} {l : level} {t : term} {iΓ : ZFSet} {it : ZFSet -> ZFSet}
  (fΓ : interp_ctx Γ iΓ) (ft : interp_tm Γ l t it) : is_clipped iΓ it.
Proof.
  destruct (clipped_interp) as [ H _ ]. specialize (H Γ l t it ft). destruct H. now apply H.
Qed.

Lemma clipped_interp_nth {Γ : ctx} {l : level} {x : nat} {iΓ : ZFSet} {ix : ZFSet -> ZFSet}
  (fΓ : interp_ctx Γ iΓ) (fx : nth_proj Γ l x ix) : is_clipped iΓ ix.
Proof.
  destruct (clipped_interp) as [ _ [ _ H ] ]. specialize (H Γ l x ix fx). destruct H. now apply H.
Qed.

Lemma funext_interp_tm {Γ : ctx} {l : level} {t1 t2 : term} {iΓ : ZFSet} {it1 it2 : ZFSet -> ZFSet}
  (fΓ : interp_ctx Γ iΓ) (ft1 : interp_tm Γ l t1 it1) (ft2 : interp_tm Γ l t2 it2) :
  (∀ γ ∈ iΓ, it1 γ ≡ it2 γ) -> it1 ≡ it2.
Proof.
  intro H. eapply clipped_funext. exact (clipped_interp_tm fΓ ft1).
  exact (clipped_interp_tm fΓ ft2). exact H.
Qed.

Lemma funext_interp_nth {Γ : ctx} {l : level} {x1 x2 : nat} {iΓ : ZFSet} {ix1 ix2 : ZFSet -> ZFSet}
  (fΓ : interp_ctx Γ iΓ) (fx1 : nth_proj Γ l x1 ix1) (fx2 : nth_proj Γ l x2 ix2) :
  (∀ γ ∈ iΓ, ix1 γ ≡ ix2 γ) -> ix1 ≡ ix2.
Proof.
  intro H. eapply clipped_funext. exact (clipped_interp_nth fΓ fx1).
  exact (clipped_interp_nth fΓ fx2). exact H.
Qed.


Inductive interp_ren : forall (Δ : ctx) (Γ : ctx) (ρ : nat -> nat) (iρ : ZFSet -> ZFSet), Prop :=

| interp_ren_empty : forall Δ ρ, interp_ren Δ ∙ ρ (fun γ => ∅)

| interp_ren_cons : forall Γ Δ l A ρ iρ ix, interp_ren Δ Γ (↑ >> ρ) iρ
                    -> nth_proj Δ l (ρ 0) ix
                    -> interp_ren Δ (Γ ,, (l , A)) ρ (fun γ => ⟨ iρ γ ; ix γ ⟩).

Definition has_ren_interp_ctx (Γ : ctx) (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ) : Prop :=
  True.

Inductive has_ren_interp_tm (Γ : ctx) (l : level)
  (t : term) (it : ZFSet -> ZFSet) (ft : interp_tm Γ l t it)
  (Δ : ctx) (iΔ : ZFSet) (fΔ : interp_ctx Δ iΔ)
  (ρ : nat -> nat) (iρ : ZFSet -> ZFSet) (fρ : interp_ren Δ Γ ρ iρ) : Prop :=
| mkHasRenInterpTm : forall (iu : ZFSet -> ZFSet) (fu : interp_tm Δ l (ρ ⋅ t) iu) (vtu : iu ≡ (fun δ => it (iρ δ))),
    has_ren_interp_tm Γ l t it ft Δ iΔ fΔ ρ iρ fρ.

Inductive has_ren_interp_proj (Γ : ctx) (l : level)
  (x : nat) (ix : ZFSet -> ZFSet) (fx : nth_proj Γ l x ix)
  (Δ : ctx) (iΔ : ZFSet) (fΔ : interp_ctx Δ iΔ)
  (ρ : nat -> nat) (iρ : ZFSet -> ZFSet) (fρ : interp_ren Δ Γ ρ iρ) : Prop :=
| mkHasRenInterpProj : forall (iy : ZFSet -> ZFSet) (fy : nth_proj Δ l (ρ x) iy) (vxy : iy ≡ (fun δ => ix (iρ δ))),
    has_ren_interp_proj Γ l x ix fx Δ iΔ fΔ ρ iρ fρ.

Lemma has_ren_interp : (forall Γ l t it ft, (forall Δ iΔ fΔ ρ iρ fρ, has_ren_interp_tm Γ l t it ft Δ iΔ fΔ ρ iρ fρ))
                       /\ (forall Γ iΓ fΓ, has_ren_interp_ctx Γ iΓ fΓ)
                       /\ (forall Γ l x ix fx, (forall Δ iΔ fΔ ρ iρ fρ, has_ren_interp_proj Γ l x ix fx Δ iΔ fΔ ρ iρ fρ)).
Proof.
  apply interp_mutind.
  - intros. specialize (H Δ iΔ fΔ ρ iρ fρ). destruct H as [ iρ' fρ' vρ' ]. econstructor.
    + apply interp_var. exact fρ'.
    + exact vρ'.
  - intros. econstructor.
    + cbn. apply interp_type.
    + easy.
  - intros. econstructor.
    + apply interp_prop.
    + easy.
  - intros. specialize (H Δ iΔ fΔ ρ iρ fρ). destruct H as [ iA' fA' vA' ].
    set (Δ' := Δ,, (ty lA, ρ ⋅ A)).
    assert (interp_ctx Δ' (ctxExt lA iΔ iA')) as fΔ'.
    { apply interp_cons_rel. exact fΔ. exact fA'. }
    set (iρu := (fun γa => ⟨ iρ (ctx_wk lA iΔ iA' γa) ; ctx_var0 lA iΔ iA' γa ⟩)).
    assert (interp_ren Δ' (Γ,, (ty lA, A)) (upRen_term_term ρ) iρu) as fρu.
    { apply interp_ren_cons.
      - asimpl. admit.
      - asimpl. now apply here_rel. }
    specialize (H0 Δ' _ fΔ' (upRen_term_term ρ) iρu fρu). destruct H0 as [ iB' fB' vB' ].
    econstructor.
    + cbn. apply interp_pi_rr. apply fA'. apply fB'.
    + destruct (sym vB'). destruct (sym vA'). unfold piTy_HO. admit.
  - admit.
  - admit.
  - admit.
  - 
Admitted.


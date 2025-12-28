From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp model_def.

Open Scope subst_scope.

Lemma model_pi (Γ : ctx) (i j : level) (A B : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tB : Γ,, (i, A) ⊢< Ax j > B : Sort j) (mB : model_typing (Γ,, (i, A)) (Ax j) B (Sort j)) :
  model_typing Γ (Ax (Ru i j)) (Pi i j A B) (Sort (Ru i j)).
Proof.
  destruct mA as [ iΓ fΓ iS fS iA fA vS vA ]. destruct mB as [ iΓ' fΓ' iT fT iB fB vT vB ].
  inversion fS ; subst ; clear fS. 
  all: inversion fΓ' ; subst ; clear fΓ'.
  1: destruct (functional_ctx Γ fΓ H4) ; clear H4. 2: destruct (functional_ctx Γ fΓ H2) ; clear H2.
  1: destruct (functional_tm A fA H5) ; clear H5. 2: destruct (functional_tm A fA H4) ; clear H4.
  all: inversion fT ; subst ; clear fT.
  (* Pi (relevant relevant) *)
  + econstructor.
    * exact fΓ.
    * apply interp_type.
    * apply interp_pi_rr. exact fA. exact fB.
    * apply univTy_HO_typing.
    * apply piTy_HO_typing'.
      ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_univTy.
      ** intros γa Hγa. refine (transpS (fun X => iB γa ∈ X) _ (vB γa Hγa)). now apply el_univTy.
  (* Pi (relevant irrelevant) *)
  + inversion H1. subst. econstructor.
    * exact fΓ.
    * apply interp_prop.
    * apply interp_pi_ri. exact fA. exact fB.
    * apply propTy_HO_typing.
    * apply forallTy_HO_typing'.
      ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_univTy.
      ** intros γa Hγa. refine (transpS (fun X => iB γa ∈ X) _ (vB γa Hγa)). now apply el_propTy.
  (* Pi (irrelevant relevant) *)
  + econstructor.
    * exact fΓ.
    * apply interp_type.
    * apply interp_pi_ir. exact fA. exact fB.
    * apply univTy_HO_typing.
    * apply piTy_HO_typing_ir'.
      ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_propTy.
      ** intros γa Hγa. refine (transpS (fun X => iB γa ∈ X) _ (vB γa Hγa)). now apply el_univTy.
  (* Pi (irrelevant irrelevant) *)
  + econstructor.
    * exact fΓ.
    * apply interp_prop.
    * apply interp_pi_ii. exact fA. exact fB.
    * apply propTy_HO_typing.
    * apply forallTy_HO_typing'.
      ** apply boxTy_HO_typing. intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_propTy.
      ** intros γa Hγa. refine (transpS (fun X => iB γa ∈ X) _ (vB γa Hγa)). now apply el_propTy.
Qed.

Lemma model_lambda (Γ : ctx) (i j : level) (A B t : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tB : Γ,, (i, A) ⊢< Ax j > B : Sort j) (mB : model_typing (Γ,, (i, A)) (Ax j) B (Sort j))
  (tt : Γ,, (i, A) ⊢< j > t : B) (mt : model_typing (Γ,, (i, A)) j t B) :
  model_typing Γ (Ru i j) (lam i j A B t) (Pi i j A B).
Proof.
  destruct mA as [ iΓ fΓ iS fS iA fA vS vA ]. destruct j as [ j | ].
  - destruct mt as [ iΓ' fΓ' iB fB it ft vB vt ]. inversion fΓ' ; subst ; clear fΓ'.
    all: destruct (functional_ctx Γ fΓ H3) ; clear H3. 
    all: destruct (functional_tm A fA H4) ; clear H4. 
    all: inversion fS ; subst ; clear fS.
    (* lambda (relevant relevant) *)
    + econstructor.
      * exact fΓ.
      * apply interp_pi_rr. exact fA. exact fB.
      * apply interp_lam_rr. exact fA. exact ft.
      * apply piTy_HO_typing.
        ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_univTy.
        ** intros γa Hγa. apply (vB γa Hγa).
      * unfold ru. apply lamTm_HO_typing.
        ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_univTy.
        ** intros γa Hγa. apply (vB γa Hγa).
        ** intros γa Hγa. apply (vt γa Hγa).
    (* lambda (irrelevant relevant) *)
    + econstructor.
      * exact fΓ.
      * apply interp_pi_ir. exact fA. exact fB.
      * apply interp_lam_ir. exact fA. exact ft.
      * apply piTy_HO_typing_ir.
        ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_propTy.
        ** intros γa Hγa. apply (vB γa Hγa).
      * unfold ru. apply lamTm_HO_typing_ir.
        ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_propTy.
        ** intros γa Hγa. apply (vB γa Hγa).
        ** intros γa Hγa. apply (vt γa Hγa).
  - destruct mt as [ iΓ' fΓ' iB fB vB vt ]. inversion fΓ' ; subst ; clear fΓ'.
    all: destruct (functional_ctx Γ fΓ H3) ; clear H3. 
    all: destruct (functional_tm A fA H4) ; clear H4. 
    all: inversion fS ; subst ; clear fS.
    (* lambda (relevant irrelevant) *)
    + econstructor.
      * exact fΓ.
      * apply interp_pi_ri. exact fA. exact fB.
      * apply forallTy_HO_typing.
        ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_univTy.
        ** intros γa Hγa. apply (vB γa Hγa).
      * apply ilamTm_HO_typing.
        ** intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_univTy.
        ** intros γa Hγa. apply (vB γa Hγa).
        ** intros γa Hγa. apply (vt γa Hγa).
    (* lambda (irrelevant irrelevant) *)
    + econstructor.
      * exact fΓ.
      * apply interp_pi_ii. exact fA. exact fB.
      * apply forallTy_HO_typing.
        ** apply boxTy_HO_typing. intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_propTy.
        ** intros γa Hγa. apply (vB γa Hγa).
      * apply ilamTm_HO_typing.
        ** apply boxTy_HO_typing. intros γ Hγ. refine (transpS (fun X => iA γ ∈ X) _ (vA γ Hγ)). now apply el_propTy.
        ** intros γa Hγa. apply (vB γa Hγa).
        ** intros γa Hγa. apply (vt γa Hγa).
Qed.

Lemma model_app (Γ : ctx) (i j : level) (A B t u : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tB : Γ,, (i, A) ⊢< Ax j > B : Sort j) (mB : model_typing (Γ,, (i, A)) (Ax j) B (Sort j))
  (tt : Γ ⊢< Ru i j > t : Pi i j A B) (mt : model_typing Γ (Ru i j) t (Pi i j A B))
  (tu : Γ ⊢< i > u : A) (mu : model_typing Γ i u A) :
  model_typing Γ j (app i j A B t u) (B <[ u..]).
Proof.
Admitted.

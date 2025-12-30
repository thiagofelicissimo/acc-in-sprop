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
  apply of_model_univ in mA. apply of_model_univ in mB.
  destruct i as [ i | ] ; destruct j as [ j | ]. all: destruct mA ; destruct mB.
  all: inversion fΓ0 ; subst ; clear fΓ0.
  1,2: destruct (functional_ctx Γ fΓ H3) ; clear H3. 3,4: destruct (functional_ctx Γ fΓ H1) ; clear H1.
  1,2: destruct (functional_tm A fA H4) ; clear H4. 3,4: destruct (functional_tm A fA H3) ; clear H3.
  (* Pi (relevant relevant) *)
  + apply to_model_univ. econstructor.
    * exact fΓ.
    * apply interp_pi_rr. exact fA. exact fA0.
    * apply piTy_HO_typing. exact vA. exact vA0. 
  (* Pi (relevant irrelevant) *)
  + apply to_model_univ. econstructor.
    * exact fΓ.
    * apply interp_pi_ri. exact fA. exact fA0.
    * apply forallTy_HO_typing. exact vA. exact vA0.
  (* Pi (irrelevant relevant) *)
  + apply to_model_univ. econstructor.
    * exact fΓ.
    * apply interp_pi_ir. exact fA. exact fA0.
    * apply piTy_HO_typing_ir. exact vA. exact vA0.
  (* Pi (irrelevant irrelevant) *)
  + apply to_model_univ. econstructor.
    * exact fΓ.
    * apply interp_pi_ii. exact fA. exact fA0.
    * apply forallTy_HO_typing. 
      ** apply boxTy_HO_typing. exact vA. 
      ** exact vA0. 
Qed.

Lemma model_lambda (Γ : ctx) (i j : level) (A B t : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tB : Γ,, (i, A) ⊢< Ax j > B : Sort j) (mB : model_typing (Γ,, (i, A)) (Ax j) B (Sort j))
  (tt : Γ,, (i, A) ⊢< j > t : B) (mt : model_typing (Γ,, (i, A)) j t B) :
  model_typing Γ (Ru i j) (lam i j A B t) (Pi i j A B).
Proof.
  apply of_model_univ in mA. destruct j as [ j | ]. 
  - destruct mt as [ iΓ' fΓ' iB fB it ft vB vt ]. destruct i as [ i | ] ; destruct mA as [ iΓ fΓ iA fA vA ].
    all: inversion fΓ' ; subst ; clear fΓ'.
    (* lambda (relevant relevant) *)
    + destruct (functional_ctx Γ fΓ H3) ; clear H3. destruct (functional_tm A fA H4) ; clear H4. econstructor.
      * exact fΓ.
      * apply interp_pi_rr. exact fA. exact fB.
      * apply interp_lam_rr. exact fA. exact ft.
      * apply piTy_HO_typing. exact vA. exact vB. 
      * unfold ru. apply lamTm_HO_typing. exact vA. exact vB. exact vt. 
    (* lambda (irrelevant relevant) *)
    + destruct (functional_ctx Γ fΓ H1) ; clear H1. destruct (functional_tm A fA H3) ; clear H3. econstructor.
      * exact fΓ.
      * apply interp_pi_ir. exact fA. exact fB.
      * apply interp_lam_ir. exact fA. exact ft.
      * apply piTy_HO_typing_ir. exact vA. exact vB.
      * unfold ru. apply lamTm_HO_typing_ir. exact vA. exact vB. exact vt.
  - destruct mt as [ iΓ' fΓ' iB fB vB vt ]. destruct i as [ i | ] ; destruct mA as [ iΓ fΓ iA fA vA ].
    all: inversion fΓ' ; subst ; clear fΓ'.
    (* lambda (relevant irrelevant) *)
    + destruct (functional_ctx Γ fΓ H3) ; clear H3. destruct (functional_tm A fA H4) ; clear H4. econstructor.
      * exact fΓ.
      * apply interp_pi_ri. exact fA. exact fB.
      * apply forallTy_HO_typing. exact vA. exact vB.
      * apply ilamTm_HO_typing. exact vA. exact vB. exact vt.
    (* lambda (irrelevant irrelevant) *)
    + destruct (functional_ctx Γ fΓ H1) ; clear H1. destruct (functional_tm A fA H3) ; clear H3. econstructor. 
      * exact fΓ.
      * apply interp_pi_ii. exact fA. exact fB.
      * apply forallTy_HO_typing. 
        ** apply boxTy_HO_typing. exact vA. 
        ** exact vB.
      * apply ilamTm_HO_typing.
        ** apply boxTy_HO_typing. exact vA.
        ** exact vB.
        ** exact vt.
Qed.

Lemma model_app (Γ : ctx) (i j : level) (A B t u : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tB : Γ,, (i, A) ⊢< Ax j > B : Sort j) (mB : model_typing (Γ,, (i, A)) (Ax j) B (Sort j))
  (tt : Γ ⊢< Ru i j > t : Pi i j A B) (mt : model_typing Γ (Ru i j) t (Pi i j A B))
  (tu : Γ ⊢< i > u : A) (mu : model_typing Γ i u A) :
  model_typing Γ j (app i j A B t u) (B <[ u..]).
Proof.
Admitted.

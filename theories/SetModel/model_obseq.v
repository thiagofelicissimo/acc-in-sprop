From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_acc HO_obseq HO_forall.
Require Import model_interp model_def.

Lemma model_obseq (Γ : ctx) (i : nat) (A a b : term)
  (tA : Γ ⊢< Ax (ty i) > A : Sort (ty i)) (mA : model_typing Γ (Ax (ty i)) A (Sort (ty i)))
  (ta : Γ ⊢< ty i > a : A) (ma : model_typing Γ (ty i) a A)
  (tb : Γ ⊢< ty i > b : A) (mb : model_typing Γ (ty i) b A) :
  model_typing Γ (Ax prop) (obseq (ty i) A a b) (Sort prop).
Proof.
  apply to_model_prop.
  destruct ma as [ iΓ fΓ iA fA ia fa vA va ]. destruct mb as [ iΓ' fΓ' iA' fA' ib fb vA' vb ].
  destruct (functional_ctx Γ fΓ fΓ'). destruct (functional_tm A fA fA'). clear fΓ' fA' vA'. econstructor.
  + exact fΓ.
  + apply interp_obseq_r. exact fA. exact fa. exact fb.
  + eapply eqTy_HO_typing. exact vA. exact va. exact vb.
Qed.

Lemma model_obsrefl (l : nat) (Γ : ctx) (A a : term)
  (tA : Γ ⊢< Ax (ty l) > A : Sort (ty l)) (mA : model_typing Γ (Ax (ty l)) A (Sort (ty l)))
  (ta : Γ ⊢< ty l > a : A) (ma : model_typing Γ (ty l) a A) :
  model_typing Γ prop (obsrefl (ty l) A a) (obseq (ty l) A a a).
Proof.
  destruct ma as [ iΓ fΓ iA fA ia fa vA va ]. econstructor.
  - exact fΓ.
  - apply interp_obseq_r. exact fA. exact fa. exact fa.
  - eapply eqTy_HO_typing. exact vA. exact va. exact va.
  - eapply reflTm_HO_typing. exact vA. exact va.
Qed.

Lemma model_J (Γ : ctx) (l : nat) (A a P p b e : term)
  (tA : Γ ⊢< Ax (ty l) > A : Sort (ty l)) (mA : model_typing Γ (Ax (ty l)) A (Sort (ty l)))
  (ta : Γ ⊢< ty l > a : A) (ma : model_typing Γ (ty l) a A)
  (tP : Γ,, (ty l, A) ⊢< Ax prop > P : Sort prop) (mP : model_typing (Γ,, (ty l, A)) (Ax prop) P (Sort prop))
  (tp : Γ ⊢< prop > p : P <[ a..]) (mp : model_typing Γ prop p (P <[ a..]))
  (tb : Γ ⊢< ty l > b : A) (mb : model_typing Γ (ty l) b A)
  (te : Γ ⊢< prop > e : obseq (ty l) A a b) (me : model_typing Γ prop e (obseq (ty l) A a b)) :
  model_typing Γ prop (J (ty l) A a P p b e) (P <[ b..]).
Proof.
Admitted.

Lemma model_cast (Γ : ctx) (i : level) (A B e a : term)
  (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tB : Γ ⊢< Ax i > B : Sort i) (mB : model_typing Γ (Ax i) B (Sort i))
  (te : Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B) (me : model_typing Γ prop e (obseq (Ax i) (Sort i) A B))
  (ta : Γ ⊢< i > a : A) (ma : model_typing Γ i a A) :
  model_typing Γ i (cast i A B e a) B.
Proof.
  destruct i as [ i | ].
  (* Proof-relevant cast *)
  - destruct ma as [ iΓ fΓ iA fA ia fa vA va ]. apply of_model_univ in mB. destruct mB as [ iΓ' fΓ' iB fB vB ].
    destruct (functional_ctx Γ fΓ fΓ'). clear fΓ'.
    destruct me as [ iΓ' fΓ' iE fE vE ve ]. destruct (functional_ctx Γ fΓ fΓ'). clear fΓ'.
    inversion fE ; subst ; clear fE.
    inversion H4 ; subst ; clear H4.
    destruct (functional_tm A fA H6). clear H6. destruct (functional_tm B fB H7). clear H7. 
    econstructor.
    + exact fΓ.
    + exact fB.
    + apply interp_cast. exact fA. exact fB. exact fa.
    + exact vB.
    + eapply castTm_HO_typing. exact vA. exact ve. exact va.
  (* Proof-irrelevant cast *)
  - destruct ma as [ iΓ fΓ iA fA vA va ]. apply of_model_univ in mB. destruct mB as [ iΓ' fΓ' iB fB vB ].
    destruct (functional_ctx Γ fΓ fΓ'). clear fΓ'.
    destruct me as [ iΓ' fΓ' iE fE vE ve ]. destruct (functional_ctx Γ fΓ fΓ'). clear fΓ'.
    inversion fE ; subst ; clear fE.
    inversion H4 ; subst ; clear H4.
    destruct (functional_tm A fA H6). clear H6. destruct (functional_tm B fB H7). clear H7. 
    econstructor.
    + exact fΓ.
    + exact fB.
    + exact vB.
    + intros γ Hγ. specialize (ve γ Hγ). apply subsingl_true_if in ve.
      exact (transpS (fun X => ∅ ∈ X) ve (va γ Hγ)).
Qed.

Lemma model_injpi1 (Γ : ctx) (i : level) (j : nat) (A1 A2 B1 B2 e : term)
  (tA1 : Γ ⊢< Ax i > A1 : Sort i) (mA1 : model_typing Γ (Ax i) A1 (Sort i))
  (tB1 : Γ,, (i, A1) ⊢< Ax (ty j) > B1 : Sort (ty j)) (mB1 : model_typing (Γ,, (i, A1)) (Ax (ty j)) B1 (Sort (ty j)))
  (tA2 : Γ ⊢< Ax i > A2 : Sort i) (mA2 : model_typing Γ (Ax i) A2 (Sort i))
  (tB2 : Γ,, (i, A2) ⊢< Ax (ty j) > B2 : Sort (ty j)) (mB2 : model_typing (Γ,, (i, A2)) (Ax (ty j)) B2 (Sort (ty j)))
  (te : Γ ⊢< prop > e : obseq (Ax (Ru i (ty j))) (Sort (Ru i (ty j))) (Pi i (ty j) A1 B1) (Pi i (ty j) A2 B2))
  (me : model_typing Γ prop e (obseq (Ax (Ru i (ty j))) (Sort (Ru i (ty j))) (Pi i (ty j) A1 B1) (Pi i (ty j) A2 B2))) :
  model_typing Γ prop (injpi1 i (ty j) A1 A2 B1 B2 e) (obseq (Ax i) (Sort i) A2 A1).
Proof.
  apply of_model_univ in mA1. apply of_model_univ in mA2. apply of_model_univ in mB1. apply of_model_univ in mB2.
  destruct i as [ i | ].
  (* relevant domain *)
  - destruct mA1 as [ iΓ fΓ iA1 fA1 vA1 ]. destruct mA2 as [ iΓ' fΓ' iA2 fA2 vA2 ].
    destruct (functional_ctx Γ fΓ fΓ') ; clear fΓ'. destruct mB1 as [ iΓ' fΓ' iB1 fB1 vB1 ].
    inversion fΓ' ; subst ; clear fΓ'. destruct (functional_ctx Γ fΓ H3) ; clear H3.
    destruct (functional_tm A1 fA1 H4) ; clear H4. destruct mB2 as [ iΓ' fΓ' iB2 fB2 vB2 ].
    inversion fΓ' ; subst ; clear fΓ'. destruct (functional_ctx Γ fΓ H3) ; clear H3.
    destruct (functional_tm A2 fA2 H4) ; clear H4. destruct me as [ iΓ' fΓ' iE fE vE ve ].
    destruct (functional_ctx Γ fΓ fΓ') ; clear fΓ'. inversion fE ; subst ; clear fE.
    inversion H4 ; subst ; clear H4. inversion H6 ; subst ; clear H6. destruct (functional_tm A1 fA1 H8) ; clear H8.
    destruct (functional_tm B1 fB1 H9) ; clear H9. clear H. inversion H7 ; subst ; clear H7.
    destruct (functional_tm A2 fA2 H6) ; clear H6. destruct (functional_tm B2 fB2 H8) ; clear H8. clear H.
    econstructor.
    + exact fΓ.
    + apply interp_obseq_r. apply interp_type. exact fA2. exact fA1.
    + eapply eqTy_HO_typing.
      * apply univTy_HO_typing.
      * intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA2 γ Hγ)). now apply el_univTy.
      * intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA1 γ Hγ)). now apply el_univTy.
    + apply (piinj1Tm_HO_typing vA1 vB1 vA2 vB2 ve).
  (* irrelevant domain *)
  - destruct mA1 as [ iΓ fΓ iA1 fA1 vA1 ]. destruct mA2 as [ iΓ' fΓ' iA2 fA2 vA2 ].
    destruct (functional_ctx Γ fΓ fΓ') ; clear fΓ'. destruct mB1 as [ iΓ' fΓ' iB1 fB1 vB1 ].
    inversion fΓ' ; subst ; clear fΓ'. destruct (functional_ctx Γ fΓ H1) ; clear H1.
    destruct (functional_tm A1 fA1 H3) ; clear H3. destruct mB2 as [ iΓ' fΓ' iB2 fB2 vB2 ].
    inversion fΓ' ; subst ; clear fΓ'. destruct (functional_ctx Γ fΓ H1) ; clear H1.
    destruct (functional_tm A2 fA2 H3) ; clear H3. destruct me as [ iΓ' fΓ' iE fE vE ve ].
    destruct (functional_ctx Γ fΓ fΓ') ; clear fΓ'. inversion fE ; subst ; clear fE.
    inversion H4 ; subst ; clear H4. inversion H6 ; subst ; clear H6. destruct (functional_tm A1 fA1 H3) ; clear H3.
    destruct (functional_tm B1 fB1 H5) ; clear H5. inversion H7 ; subst ; clear H7.
    destruct (functional_tm A2 fA2 H3) ; clear H3. destruct (functional_tm B2 fB2 H5) ; clear H5. 
    econstructor.
    + exact fΓ.
    + apply interp_obseq_r. apply interp_prop. exact fA2. exact fA1.
    + unshelve eapply eqTy_HO_typing.
      * exact 0.
      * apply propTy_HO_typing.
      * intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA2 γ Hγ)). now apply el_propTy.
      * intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA1 γ Hγ)). now apply el_propTy.
    + apply (piinj1Tm_HO_typing_ir vA1 vB1 vA2 vB2 ve). 
Qed.

Lemma model_injpi2 (Γ : ctx) (i : level) (j : nat) (A1 A2 B1 B2 e a2 : term)
  (tA1 : Γ ⊢< Ax i > A1 : Sort i) (mA1 : model_typing Γ (Ax i) A1 (Sort i))
  (tB1 : Γ,, (i, A1) ⊢< Ax (ty j) > B1 : Sort (ty j)) (mB1 : model_typing (Γ,, (i, A1)) (Ax (ty j)) B1 (Sort (ty j)))
  (tA2 : Γ ⊢< Ax i > A2 : Sort i) (mA2 : model_typing Γ (Ax i) A2 (Sort i))
  (tB2 : Γ,, (i, A2) ⊢< Ax (ty j) > B2 : Sort (ty j)) (mB2 : model_typing (Γ,, (i, A2)) (Ax (ty j)) B2 (Sort (ty j)))
  (te : Γ ⊢< prop > e : obseq (Ax (Ru i (ty j))) (Sort (Ru i (ty j))) (Pi i (ty j) A1 B1) (Pi i (ty j) A2 B2))
  (me : model_typing Γ prop e (obseq (Ax (Ru i (ty j))) (Sort (Ru i (ty j))) (Pi i (ty j) A1 B1) (Pi i (ty j) A2 B2)))
  (ta2 : Γ ⊢< i > a2 : A2) (ma2 : model_typing Γ i a2 A2)
  (a1 := cast i A2 A1 (injpi1 i (ty j) A1 A2 B1 B2 e) a2) :
  model_typing Γ prop (injpi2 i (ty j) A1 A2 B1 B2 e a2) (obseq (Ax (ty j)) (Sort (ty j)) (B1 <[ a1..]) (B2 <[ a2..])).
Proof.
Admitted.

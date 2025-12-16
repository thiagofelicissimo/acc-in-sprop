

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory
    Reduction LRDef LRBasicProps FundamentalAux.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.


Definition meta R t u := ∃ p, ∙ ⊢< prop > p : R <[u .: t ..].

Axiom ob_to_meta : forall t i A R a, ∙ ⊢< prop > t : acc i A R a -> Acc (meta R) a.

Lemma wk1_type Γ i l t t' B B' A :
    Γ ⊢< l > t : B ->
    t' = S ⋅ t ->
    B' = S ⋅ B ->
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢< l > t' : B'.
Proof.
    intros. subst.
    eapply type_ren. all: eauto using WellRen_S.
    constructor. 2: assumption.
    eapply validity_ctx in H. assumption.
Qed.

Lemma wk1_conv Γ i l t t' u u' B B' A :
    Γ ⊢< l > t ≡ u : B ->
    t' = S ⋅ t ->
    u' = S ⋅ u ->
    B' = S ⋅ B ->
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢< l > t' ≡ u' : B'.
Proof.
    intros. subst.
    substify. eapply subst_conv; eauto.
    2:change (S >> var) with (var >> ren_term S).
    2:eapply ConvSubst_weak.
    all: eauto using ctx_typing, validity_ty_ctx, refl_subst, subst_id.
Qed.


Lemma aaux A' R' P' Γ i k A R a q P p r b X Y l:
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ,, (i, A) ⊢< Ax l > P ≡ P' : Sort l ->
    Γ ,, (i, A) ⊢< Ax (ty k) > P : Sort (ty k) ->
    let R_ := (1 .: (0 .: (S >> S))) ⋅ R in
    let P_ := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi i l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
    Γ ⊢< i > a : A ->
    Γ ⊢< i > b : A ->
    Γ ⊢< prop > q : acc i A R a ->
    Γ ⊢< prop > r : R <[a .: b ..] ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv i Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel i (ty k) Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop (ty k) t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i (ty k) A t4 t3 in
    let t2' := R'<[S ⋅ a .: (var 0 .: S >> var)] in
    let t4' := Pi prop l t2' ((1.: (S >> S)) ⋅ P') in
    let t6 := app i (ty k) A' t4' t5 b in
    let t7 := app prop (ty k) (R'<[a .: b ..]) (S ⋅ (P' <[ b ..])) t6 r in
    X = t7 ->
    Y = P <[b..] ->
    l = ty k ->
    Γ ⊢< l > X -->> accel i (ty k) A R P p b (accinv i A R a q b r) : Y.
Proof.
    intros. subst.
    assert (Γ ⊢< Ax prop > R <[ a .: b..] ≡ R' <[a .: b ..] : Sort prop) as R_conv_R'.
    { eapply subst_conv; eauto using validity_ty_ctx. econstructor. econstructor.
      ssimpl. eauto using refl_subst, subst_id, validity_ty_ctx.
      all:ssimpl; eauto using conv_refl. } 

    assert (Γ,, (i, A) ⊢< Ax prop > R <[ S ⋅ a .: (var 0 .: S >> var)] ≡ R' <[ S ⋅ a .: (var 0 .: S >> var)] : Sort prop).
    { eapply subst_conv; eauto using ctx_typing, validity_ty_ctx.
      setoid_rewrite subst_id_reduce1. eapply substs_one.
      eapply conv_refl, type_ren; eauto using validity_ty_ctx, WellRen_S. }

    assert (Γ,, (i, A) ⊢< Ax (ty k) > t4 ≡ t4' : Sort (ty k)).
    { unfold t4, t4', t2, t2', P''.
      eapply meta_conv_conv. eapply meta_lvl_conv.
      econstructor; eauto using validity_conv_left.
      eapply conv_ren; eauto using ctx_typing, validity_conv_left, validity_ty_ctx.
      econstructor. ssimpl. eapply WellRen_weak, WellRen_S.
      eapply varty_meta. econstructor. econstructor.
      all:rasimpl; reflexivity. }


    eapply redd_conv.
    eapply redd_step.

    eapply red_app'; eauto 7 using conv_sym, substs_one_4, conv_refl, subst_conv, type_conv, validity_ty_ctx.
    3:rasimpl; eauto using subst_conv, substs_one_3, conv_refl, conv_sym.
    eapply red_beta'; eauto using conv_sym, type_conv.
    3:unfold t4', t2';rasimpl; reflexivity.
    eauto using conv_sym, conv_ty_in_ctx_conv.
    eapply conv_ty_in_ctx_ty; eauto. eapply type_conv; eauto.
    eapply t3Wt; eauto using validity_conv_left.
    
    eapply red_to_redd.
    unfold t3, t2, P''; rasimpl. eapply red_beta' ; rasimpl ; eauto 7 using conv_sym, substs_one_4, conv_refl, subst_conv, type_conv, ctx_typing, validity_ty_ctx.
    3:{ unfold t1, t0, Awk, Rwk, Pwk, pwk. rasimpl.
        setoid_rewrite subst_id_reduce2.
        setoid_rewrite subst_id_reduce1.
        rasimpl. reflexivity. }
    eapply subst_conv; eauto using conv_sym, ctx_typing, validity_ty_ctx, validity_conv_right.
    3: { eapply subst_conv; eauto using validity_ty_ctx, conv_sym. 
         econstructor; ssimpl; eauto using conv_refl, subst_id, validity_ty_ctx, refl_subst. }
    1:{ econstructor; ssimpl. change (S >> var) with (var >> ren_term S). 
        eapply ConvSubst_weak; eauto using validity_conv_right, validity_ty_ctx, refl_subst, subst_id.
        eapply wk1_conv. eapply conv_refl, H5. all:rasimpl; eauto using validity_conv_right. } 

    eapply conv_ty_in_ctx_ty; eauto.
    assert (forall b, pointwise_relation _ eq (var 0 .: (S ⋅ b .: S >> var)) (up_term (b ..))).
    { unfold pointwise_relation. intros. destruct a0. reflexivity. rasimpl. destruct a0.
      reflexivity. ssimpl. reflexivity. }
    eapply type_conv.
    eapply subst_ty. 3:eapply t1Wt.
    3:eauto using validity_conv_left.
    8:reflexivity.
    all:eauto using ctx_typing, validity_ty_ctx, validity_conv_left.
    rewrite H10.
    eapply WellSubst_up. 2:rasimpl;reflexivity. 2:rasimpl; eauto using validity_conv_left.
    eapply subst_one; eauto. 
    rasimpl.
    eapply subst_conv; eauto using ctx_typing, validity_conv_left, validity_ty_ctx.
    assert (pointwise_relation _ eq (S ⋅ b .: S >> var)  ((b..) >> ren_term S)).
    { unfold pointwise_relation. intro. destruct a0. reflexivity.
      rasimpl. reflexivity. }
    rewrite H11.
    eapply ConvSubst_weak; eauto using validity_conv_left, substs_one, conv_refl.
Qed.

Lemma conv_ty_in_ctx_conv2 Γ l A A' l' t u B :
  Γ ,, (l , A) ,, (l, S ⋅ A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ,, (l, S ⋅ A') ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  econstructor. econstructor. eauto using validity_conv_left, validity_ty_ctx, ctx_conv_refl.
  eauto. eapply conv_ren; eauto using validity_conv_left, WellRen_S.
  eapply validity_ctx in t_eq_u. inversion t_eq_u. assumption.
Qed.



Lemma conv_ty_in_ctx_conv2' Γ l1 l2 l3 A A' t u B B' C :
  Γ ,, (l1 , A) ,, (l2, B) ⊢< l3 > t ≡ u : C ->
  Γ ⊢< Ax l1 > A ≡ A' : Sort l1 ->
  Γ ,, (l1 , A) ⊢< Ax l2 > B ≡ B' : Sort l2 ->
  Γ ,, (l1 , A') ,, (l2, B') ⊢< l3 > t ≡ u : C.
Proof.
  intros t_eq_u A_eq_A' B_eq_B'.
  eapply conv_in_ctx_conv; eauto.
  econstructor; eauto. econstructor; eauto.
  eauto using validity_conv_left, validity_ty_ctx, ctx_conv_refl.
Qed.

Lemma fundamental_accel_aux2 i k C1' C2' A1 A2 R1 R2 P1 P2 a1 a2 l :
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    let R1' := (1 .: (0 .: (S >> S))) ⋅ R1 in
    let P1' := (1 .: (S >> S >> S)) ⋅ P1 in
    let C1 := Pi prop (ty k) R1' P1' in
    let B1 := Pi i (ty k) (S ⋅ A1) C1 in
    let R2' := (1 .: (0 .: (S >> S))) ⋅ R2 in
    let P2' := (1 .: (S >> S >> S)) ⋅ P2 in
    let C2 := Pi prop (ty k) R2' P2' in
    let B2 := Pi i (ty k) (S ⋅ A2) C2 in
    ∙ ⊢< i > a1 ≡ a2 : A1 ->
    C1' = C1 <[ up_term_term a1..] ->
    C2' = C2 <[ up_term_term a2..] ->
    l = Ax (ty k) ->
    ∙,, (i, A1) ⊢< l > C1' ≡ C2' : Sort (ty k).
Proof.
    intros. subst.
    assert (∙,, (i, A1) ⊢< Ax prop >
        R1 <[ ↑ ⋅ a1 .: (var 0 .: ↑ >> var)]
      ≡ R2 <[ ↑ ⋅ a2 .: (var 0 .: ↑ >> var)] : Sort prop).
    { eapply subst_conv; eauto using validity_conv_left, ctx_typing. econstructor. econstructor. econstructor.
      ssimpl. eapply conv_var'; eauto using validity_conv_left, validity_ty_ctx, varty. rasimpl; reflexivity.
      eapply conv_ren; eauto; eauto using ctx_typing, validity_conv_left. eapply WellRen_S. rasimpl. reflexivity. }
    unfold C1, C2, R1', R2', P1', P2'.
    rasimpl. eapply conv_pi'; eauto.
    eapply subst_conv; eauto.
    1:{
      constructor.
      - eapply validity_ctx. eassumption.
      - eapply validity_conv_left. eassumption.
    }
    econstructor. econstructor. rasimpl.
    eapply conv_var'. 1:econstructor. 1:econstructor.
    1:econstructor; eauto using validity_ty_ctx, validity_conv_left.
    rasimpl. reflexivity.
Qed.


Lemma prefundamental_accel A3 R3 P3 i k A1 A2 ϵA R1 R2 a1 a2 q1 q2 P1 P2 ϵP p1 p2 :
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    ∙ ⊢< Ax i > A1 ≡ A3 : Sort i ->
    ⊩< i > A1 ≡ A2 ↓ ϵA ->
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R3 : Sort prop ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P3 : Sort (ty k) ->
    (forall a1 a2 (ϵa : ϵA a1 a2), ⊩< ty k > P1<[a1..] ≡ P2<[a2..] ↓ ϵP a1 a2) ->
    let ϵB a1 a2 f1 f2 := forall b1 b2 (ϵb : ϵA b1 b2) r1 r2 (r_Wt : ∙ ⊢< prop > r1 ≡ r2 : R1 <[a1 .:b1 ..]) t1 t2,
        t1 = app prop (ty k) (R1<[a1 .: b1 ..]) (S ⋅ (P1 <[b1..]))
                (app i (ty k) A1 (Pi prop (ty k) (R1<[(S ⋅ a1) .: (var 0 .: (S >> var))]) ((1 .: S >> S) ⋅ P1)) f1 b1)
            r1 ->
        t2 = app prop (ty k) (R3<[a2 .: b2 ..]) (S ⋅ (P3 <[b2..]))
                (app i (ty k) A3 (Pi prop (ty k) (R3<[(S ⋅ a2) .: (var 0 .: (S >> var))]) ((1 .: S >> S) ⋅ P3)) f2 b2)
            r2 ->
            ϵP b1 b2 t1 t2 in
    let R' := (1 .: (0 .: (S >> S))) ⋅ R1 in
    let P' := (1 .: (S >> S >> S)) ⋅ P1 in
    let B := Pi i (ty k) (S ⋅ A1) (Pi prop (ty k) R' P') in
    (forall a1 a2 (ϵa : ϵA a1 a2) f1 f2 (ϵf : ϵB a1 a2 f1 f2),
        ∙ ⊢< Ru i (ty k)> f1 ≡ f2 : B <[a1..] ->
        ϵP a1 a2 (p1 <[f1.: a1 ..]) (p2<[f2 .: a2 ..])) ->
    (∙ ,, (i, A1)),, (Ru i (ty k), B) ⊢< ty k > p1 ≡ p2 : (1 .: S >> S) ⋅ P1 ->
    ∙ ⊢< i > a1 ≡ a2 : A1 ->
    forall (ϵa : ϵA a1 a2),
    ∙ ⊢< prop > q1 ≡ q2 : acc i A1 R1 a1 ->
    ϵP a1 a2 (accel i (ty k) A1 R1 P1 p1 a1 q1) (accel i (ty k) A2 R2 P2 p2 a2 q2).
Proof.
    intros.
    assert (Acc (meta R1) a1) by eauto using validity_conv_left, ob_to_meta.

    generalize q1 q2 a2 ϵa H9 H10. clear q1 q2 a2 ϵa H9 H10.
    induction H11. rename x into a1. intros.

    assert (∙ ⊢< ty k> accel i (ty k) A2 R2 P2 p2 a2 q2 : P1 <[ a1..]) as temp.
    { eauto using conv_accel, validity_conv_right.  admit. (* Nedd conv_accel' *) }
    eapply type_inv_accel' in temp as (_ & _ & R2Wt & _ & p2Wt & _).

    eapply LR_irred_tm; eauto. 3:eapply H7; eauto. all:clear H7.
    - eapply red_to_redd, red_accel'; eauto using validity_conv_left.
    - eapply red_to_redd; eapply red_conv.
      eapply red_accel'; eauto 7 using validity_conv_right, conv_ty_in_ctx_ty, conv_sym, type_conv, conv_acc, subst_conv, conv_sym, substs_one.
      eapply subst_conv; eauto using ctx_typing, conv_sym, substs_one.
    - unfold ϵB. all:clear ϵB. intros; subst.
      eapply LR_irred_tm; eauto.
      1,2:shelve.
      unshelve eapply H10; clear H10.
      eapply (accinv i A1 R1 a1 q1 b1 r1).
      eapply (accinv i A2 R2 a2 q2 b2 r2).
      unfold meta; eexists; eauto using validity_conv_right.
      eauto.
      eauto using LR_escape_tm.
      { eapply conv_irrel.
        - eauto 8 using type_accinv', LR_escape_tm, validity_conv_left.
        - eapply type_conv. eapply type_accinv'; eauto 8 using type_conv, conv_acc, conv_sym, validity_conv_right, LR_escape_tm, substs_one_4, subst_conv, ctx_typing.
        eauto using conv_acc, conv_sym, conv_ty_in_ctx_conv, conv_ty_in_ctx_conv2, LR_escape_tm, ctx_typing, validity_ty_ctx, validity_conv_left. }
      Unshelve.
      (* + shelve.
      + shelve. *)
      + rasimpl. eapply (aaux A1 R1 P1); eauto using validity_conv_left, LR_escape_tm, conv_refl. substify. rasimpl. reflexivity.

      + eapply redd_conv.
        eapply (aaux A3 R3 P3); eauto 6 using validity_conv_right, conv_sym, conv_trans, LR_escape_tm, conv_ty_in_ctx_conv, conv_ty_in_ctx_conv2, type_conv, conv_acc, substs_one_4, subst_conv.
        2:eapply subst_conv; eauto using ctx_typing, conv_sym, substs_one, LR_escape_tm.
        eapply type_conv; eauto using validity_conv_right.
        eapply subst_conv; eauto using ctx_typing. 
        econstructor. ssimpl. eapply substs_one; eauto using LR_escape_tm.
        ssimpl. eauto using LR_escape_tm.
    -  clear ϵB H10 p2Wt.
    assert (pointwise_relation _ eq ((1 .: S >> S) >> var) (var 1 .: (S >> S) >> var)).
    { unfold pointwise_relation.  intros. destruct a. reflexivity. reflexivity. }
    eapply conv_lam'; eauto.
    + clear H3 H5. eapply fundamental_accel_aux2; eauto. rasimpl. f_equal. substify. setoid_rewrite H7. reflexivity.
      rasimpl. f_equal. substify. setoid_rewrite H7. reflexivity.
    + eapply conv_lam'; eauto.
      1,2:admit.
      admit.
    + unfold B, R', P'. rasimpl. f_equal. substify. setoid_rewrite H7. reflexivity.
Admitted.



Lemma fundamental_accel_aux1 i k C1' C2' A1 A2 R1 R2 P1 P2 f1 f2 s1 s2 a1 a2 T l :
    ∙ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    (∙ ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    ∙ ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    let R1' := (1 .: (0 .: (S >> S))) ⋅ R1 in
    let P1' := (1 .: (S >> S >> S)) ⋅ P1 in
    let C1 := Pi prop (ty k) R1' P1' in
    let B1 := Pi i (ty k) (S ⋅ A1) C1 in
    let R2' := (1 .: (0 .: (S >> S))) ⋅ R2 in
    let P2' := (1 .: (S >> S >> S)) ⋅ P2 in
    let C2 := Pi prop (ty k) R2' P2' in
    let B2 := Pi i (ty k) (S ⋅ A2) C2 in
    ∙ ⊢< Ru i (ty k) > f1 ≡ f2 : B1 <[a1..] ->
    ∙ ⊢< i > s1 ≡ s2 : A1 ->
    ∙ ⊢< i > a1 ≡ a2 : A1 ->
    T = C1 <[s1 .: a1 ..] ->
    (* T = Pi prop (ty k) (R1 <[ a0 .: (s1 .: σ1)])  *)
        (* (P1 <[ ↑ ⋅ s1 .: σ1 >> subst_term (↑ >> var)]) -> *)
    C1' = C1 <[up_term_term (a1 ..)] ->
    C2' = C2 <[up_term_term (a2 ..)] ->
    l = Ru prop (ty k) ->
    ∙ ⊢< l > app i (ty k) A1 C1' f1 s1
        ≡ app i (ty k) A2 C2' f2 s2 : T.
Proof.
    intros. subst.
    eapply conv_app'; eauto.
    2: unfold B1, C1, R1', P1' in *; rasimpl in H2 ; rasimpl; eauto.
    2:rasimpl; reflexivity.
    eauto using fundamental_accel_aux2.
Qed.


Lemma fundamental_accel Γ i k A1 A2 R1 R2 a1 a2 q1 q2 P1 P2 p1 p2 :
    Γ ⊢< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    (Γ,, (i, A1)),, (i, S ⋅ A1) ⊢< Ax prop > R1 ≡ R2 : Sort prop ->
    (Γ,, (i, A1)),, (i, S ⋅ A1) ⊨< Ax prop > R1 ≡ R2 : Sort prop ->
    Γ,, (i, A1) ⊢< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R1 in
    let P' := (1 .: (S >> S >> S)) ⋅ P1 in
    let C := Pi prop (ty k) R' P' in
    let B := Pi i (ty k) (S ⋅ A1) C in
    let P'' := (1.: (S >> S)) ⋅ P1 in
    (Γ,, (i, A1)),, (Ru i (ty k), B) ⊢< ty k > p1 ≡ p2 : P'' ->
    (Γ,, (i, A1)),, (Ru i (ty k), B) ⊨< ty k > p1 ≡ p2 : P'' ->
    Γ ⊢< i > a1 ≡ a2 : A1 ->
    Γ ⊨< i > a1 ≡ a2 : A1 ->
    Γ ⊢< prop > q1 ≡ q2 : acc i A1 R1 a1 ->
    Γ ⊨< prop > q1 ≡ q2 : acc i A1 R1 a1 ->
    Γ ⊨< ty k > accel i (ty k) A1 R1 P1 p1 a1 q1 ≡ accel i (ty k) A2 R2 P2 p2 a2 q2 : P1 <[ a1..].
Proof.
    intros A1_conv_A1 LRv_A12 R1_conv_R2 LRv_R12 P1_conv_P2 LRv_P12 R' P' C B P'' p1_conv_p2 LRv_p12 a1_conv_a2 LRv_a12 q1_conv_q2 LRv_q12.
    unfold LRv. intros σ1 σ2 ϵσ12.

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_A11 as temp; eauto. destruct temp as (ϵA & LR_A11).
    eapply LRv_to_LR_ty_copy in LRv_A12 as LR_A12; eauto.

    assert (Γ ⊨< i > a1 ≡ a1 : A1) as LRv_a11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_tm in LRv_a11 as ϵa11; eauto.
    eapply LRv_to_LR_tm in LRv_a12 as ϵa12; eauto.

    eapply getLR_of_motive in ϵσ12 as temp; eauto.
    destruct temp as (eP & eP_eq & LR_P11 & LR_P12 & LR_P11').
    clear LRv_P12 LRv_a12 LRv_a11 LRv_A11 LRv_A12 LRv_R12 LRv_P12 LRv_q12.

    assert ((∙,, (i, A1 <[ σ1])),, (i, S ⋅ A1 <[ σ1])
        ⊢< Ax prop > R1 <[ var 0 .: (var 1 .: σ1 >> ren_term (↑ >> ↑))]
                ≡    R1 <[ var 0 .: (var 1 .: σ2 >> ren_term (↑ >> ↑))] : Sort prop)
        as R1σ_conv_R2σ.
    { eapply validity_conv_left, conv_refl in R1_conv_R2.
      eapply subst_conv; eauto using conv_refl.
      1:{
        constructor. all: admit.
      }
      eapply lift_subst2; eauto using validity_conv_left, validity_ty_ctx, LR_subst_escape.
      rasimpl. reflexivity.
    }

    assert (∙,, (i, A1 <[ σ1]) ⊢< Ax (ty k) >
        P1 <[ var 0 .: σ1 >> ren_term ↑] ≡
        P1 <[ var 0 .: σ2 >> ren_term ↑] : Sort (ty k)) as P1σ_conv_P2σ.
    { eauto 8 using validity_conv_left, conv_refl, subst_conv, lift_subst, validity_ty_ctx, LR_subst_escape. admit. }



    exists (eP (a1 <[ σ1]) (a2 <[ σ2])).
    split; rasimpl. eauto.
    eapply (prefundamental_accel (A1 <[σ2]) (R1 <[ var 0 .: (var 1 .: σ2 >> ren_term (↑ >> ↑))]) (P1 <[ var 0 .: σ2 >> ren_term ↑]));
    eauto 6 using subst_conv, LR_subst_escape, validity_conv_left, conv_refl, lift_subst, validity_ty_ctx.
    1:eapply subst_conv; eauto using validity_conv_left, conv_refl, ctx_nil. (* eapply conv_scons_alt; eauto using LR_subst_escape, validity_conv_left, validity_ty_ctx; rasimpl; reflexivity.
    intros; rasimpl; eauto.
    3:eapply subst; eauto using LR_subst_escape; rasimpl; reflexivity.
    2:{eapply subst; eauto. 2: unfold P''; rasimpl; substify; reflexivity.
      eapply lift_subst2; eauto using LR_subst_escape, validity_conv_left, validity_ty_ctx. unfold B, C, R', P'. rasimpl. reflexivity. }

    intros.


    pose (ϵC s1 s2 :=
        ϵPi prop (ty k) (R1 <[ a0 .: (s1 .: σ1)]) (R1 <[ a3 .: (s2 .: σ2)])
            (λ t0 u0, ∙ ⊢< prop > t0 ≡ u0 : R1 <[ a0 .: (s1 .: σ1)])
            (P1 <[ ↑ ⋅ s1 .: σ1 >> subst_term (↑ >> var)])
            (P1 <[ ↑ ⋅ s2 .: σ2 >> subst_term (↑ >> var)])
            (λ x x0, eP s1 s2)).

    pose (ϵB := ϵPi i (ty k) (A1 <[ σ1]) (A1 <[ σ2]) ϵA
                    (C <[up_term_term (a0 .:σ1)]) (C <[up_term_term (a3 .:σ2)]) ϵC).

    assert (ϵB f1 f2).
    {
        unfold ϵB. unfold ϵPi.
        split.
        - rasimpl in H. unfold C, P', R'. rasimpl.  eapply H.
        - intros. unfold ϵC. unfold ϵPi. split.
          + eapply fundamental_accel_aux1; eauto using LR_escape_tm, LR_escape_ty.
            all: unfold C, R', P'; rasimpl; reflexivity.
          + intros. rasimpl. eapply (ϵf s1 s2 ϵs s0 s3).
            rasimpl. eauto.
            all: unfold C, P', R'; rasimpl; reflexivity. }

    clear ϵf H. (* removes clutter *)
    assert (⊩< Ru i (ty k) > B <[a0 .: σ1] ≡ B <[ a3 .: σ2] ↓ ϵB).
    {
        unfold B. simpl. unshelve eapply LR_pi'.
        exact ϵA. exact ϵC.
        - rasimpl; eapply fundamental_accel_aux2;
          eauto using LR_escape_tm, LR_escape_ty;
          unfold P', R'; rasimpl; reflexivity.
        - rasimpl. eauto.
        - intros. rasimpl.
          assert (∙ ⊢< Ax (ty k) > P1 <[ s1.: σ1] ≡ P1 <[ s2.: σ2 ] : Sort (ty k))
            by eauto 7 using subst, conv_refl, validity_conv_left, ConvSubst, LR_escape_tm, LR_subst_escape.

          assert (∙ ⊢< Ax prop > R' <[ s1 .: (a0 .: σ1)] ≡ R' <[ s2 .: (a3 .: σ2)] : Sort prop).
          { unfold R'. rasimpl. eapply subst; eauto using validity_conv_left, conv_refl.
            econstructor. econstructor. eauto using LR_subst_escape. eauto using LR_escape_tm. rasimpl. eauto using LR_escape_tm. }
          unshelve eapply LR_pi'.
          exact (fun t u => ∙ ⊢< prop > t ≡ u : R1 <[ a0 .: (s1 .: σ1)]).
          intros; exact (eP s1 s2).
          + eapply wk1_conv. eapply H.
            1,2:unfold P'; rasimpl; reflexivity.
            all : eauto using validity_conv_left.
          + eapply LR_prop; eauto.
            unfold R'; eauto using validity_conv_right. split; unfold R'; rasimpl; eauto.
          + intros. simpl. unfold P'. rasimpl. eauto.
          + unfold ϵC, ϵB, P', R', ϵPi. rasimpl. reflexivity.
          + reflexivity.
        - unfold ϵC, ϵB, C, P', R', ϵPi. intros. ssimpl. reflexivity.
        - reflexivity. }

    assert (⊩s (f1 .: (a0 .: σ1)) ≡ (f2 .: (a3 .: σ2)) : (Γ,, (i, A1)),, (Ru i (ty k), B))
        by eauto using LR_subst.

    eapply LRv_to_LR_tm in LRv_p12 as ϵp; eauto.
    2:unfold P''; rasimpl; eauto.
    rasimpl. eapply ϵp. *)
Admitted.

Lemma fundamental_accel_accin Γ i k A R a q P p :
    Γ ⊢< Ax i > A : Sort i ->
    Γ ⊨< Ax i > A ≡ A : Sort i ->
    (Γ,, (i, A)),, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    (Γ,, (i, A)),, (i, S ⋅ A) ⊨< Ax prop > R ≡ R : Sort prop ->
    Γ,, (i, A) ⊢< Ax (ty k) > P : Sort (ty k) ->
    Γ,, (i, A) ⊨< Ax (ty k) > P ≡ P : Sort (ty k) ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi i (ty k) (S ⋅ A) (Pi prop (ty k) R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    (Γ,, (i, A)),, (Ru i (ty k), B) ⊢< ty k > p : P'' ->
    (Γ,, (i, A)),, (Ru i (ty k), B) ⊨< ty k > p ≡ p : P'' ->
    Γ ⊢< i > a : A ->
    Γ ⊨< i > a ≡ a : A ->
    Γ ⊢< prop > q : acc i A R a ->
    Γ ⊨< prop > q ≡ q : acc i A R a ->
    let Awk := Init.Nat.add 2 ⋅ A in
    let Rwk := up_ren (up_ren (Init.Nat.add 2)) ⋅ R in
    let Pwk := up_ren (Init.Nat.add 2) ⋅ P in
    let pwk := up_ren (up_ren (Init.Nat.add 2)) ⋅ p in
    let t5 := accinv i Awk Rwk (Init.Nat.add 2 ⋅ a) (Init.Nat.add 2 ⋅ q) (var 1) (var 0) in
    let t6 := accel i (ty k) Awk Rwk Pwk pwk (var 1) t5 in
    let t7 := R <[ S ⋅ a .: (var 0 .: S >> var)] in
    let t8 := lam prop (ty k) t7 P'' t6 in
    let t9 := Pi prop (ty k) t7 P'' in
    let t10 := lam i (ty k) A t9 t8 in
    Γ ⊨< ty k > accel i (ty k) A R P p a q ≡ p <[ t10 .: a..] : P <[ a..].
Proof.
    intros. unfold LRv. intros σ1 σ2 ϵσ.
    eapply H8 in ϵσ as temp.
    destruct temp as (ϵA & LR_A & ϵa).
    assert (⊩s (a<[σ1] .: σ1) ≡ (a<[σ2] .: σ2) : Γ,, (i, A)).
    unshelve econstructor. exact ϵA. asimpl. eauto. rasimpl. eauto. rasimpl. eauto.
    eapply H4 in H11 as temp. rewrite <- helper_LR in temp.
    destruct temp as (ϵP & LR_P).

    eapply fundamental_accel in ϵσ as temp; eauto using conv_refl.
    destruct temp as (ϵP' & LR_P' & ϵaccel).
    rasimpl in LR_P'.
    assert (ϵP <~> ϵP') by eauto using LR_irrel.
    rewrite <- H12 in ϵaccel.
    clear ϵP' LR_P' H12.

    (exists ϵP). split; rasimpl; eauto.
    eapply LR_redd_tm; eauto.
    - rasimpl. eapply redd_refl.
      eapply LR_escape_tm in ϵaccel; eauto. rasimpl in ϵaccel.
      eapply validity_conv_left. eauto.
    - eapply LR_escape_tm in ϵaccel; eauto. eapply validity_conv_right in ϵaccel.
      simpl in ϵaccel.
      eapply type_inv_accel' in ϵaccel as (_ & AWt & RWt & PWt & pWt & aWt & qWt & l_eq & conv).
      eapply redd_conv; eauto using conv_sym.
      eapply red_to_redd. simpl. eapply red_accel'; eauto.
      rasimpl. f_equal. unfold t10, t9, t8, t7, t6, t5, pwk, Pwk, Rwk, Awk, P''.
      f_equal. f_equal. rasimpl. reflexivity. f_equal; rasimpl; reflexivity.
Qed.

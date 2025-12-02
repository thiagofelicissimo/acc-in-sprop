

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory 
    Reduction LRDef LRBasicProps FundamentalAux FundamentalNat FundamentalPi.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.


Lemma LR_to_red k A B R : LR (ty k) A B R -> exists A', ∙ ⊢< Ax (ty k) > A -->>! A' : Sort (ty k).
Proof.
    intro. assert (exists l, l = ty k /\ LR l A B R) by eauto.
    clear H. destruct H0 as (l & eq & lr).
    generalize l A B R lr k eq. clear l A B R lr k eq.
    refine (LR_ind _ _ _ _ _); intros; dependent destruction eq; eauto.
Qed.


(* these are consequences of the standard model *)
Axiom nat_neq_sort : forall e, ∙ ⊢< prop > e : obseq (ty 1) (Sort (ty 0)) Nat (Sort prop) -> False.
Axiom nat_neq_pi  : forall i j A B e, ∙ ⊢< prop > e : obseq (ty 1) (Sort (ty 0)) Nat (Pi i j A B) -> False.
Axiom sort_neq_pi  : forall l i j A B e, ∙ ⊢< prop > e : obseq (Ax (Ax l)) (Sort (Ax l)) (Sort l) (Pi i j A B) -> False.
Axiom pi_sort_inj : forall i j i' j' A A' B B' e,
    Ru i j = Ru i' j' ->
    ∙ ⊢< prop > e : obseq (Ax (Ru i j)) (Sort (Ru i j)) (Pi i j A B) (Pi i' j' A' B') -> 
    i = i' /\ j = j'.

(* and the following are definable *)
Axiom obseq_sym : level -> term -> term -> term -> term -> term.
Axiom type_obseq_sym : forall Γ l A a b e, 
    Γ ⊢< prop > e : obseq l A a b -> 
    Γ ⊢< prop > obseq_sym l A a b e : obseq l A b a.    

Lemma nat_neq_sort_red l l' A B e : 
    ∙ ⊢< Ax l' > A -->>! Nat : Sort l' ->
    ∙ ⊢< Ax l' > B -->>! Sort l : Sort l' ->
    ∙ ⊢< prop > e : obseq (Ax l') (Sort l') A B -> 
    False.
Proof.
    intros A_red_nat B_red_sort A_eq_B.
    eapply redd_whnf_to_conv in B_red_sort as temp.
    eapply validity_conv_right, type_inv_sort' in temp as (_ & eq & _).
    eapply Ax_inj in eq. subst.
    eapply redd_whnf_to_conv in A_red_nat as temp.
    eapply validity_conv_right, type_inv_nat' in temp as (_ & eq & _).
    destruct l. inversion eq. clear eq.
    eapply nat_neq_sort. eapply type_conv. eapply A_eq_B.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.



Lemma nat_neq_pi_red l' A B i j S T e : 
    ∙ ⊢< Ax l' > A -->>! Nat : Sort l' ->
    ∙ ⊢< Ax l' > B -->>! Pi i j S T : Sort l' ->
    ∙ ⊢< prop > e : obseq (Ax l') (Sort l') A B -> 
    False.
Proof.
    intros A_red_nat B_red_pi A_eq_B.
    eapply redd_whnf_to_conv in A_red_nat as temp.
    eapply validity_conv_right, type_inv_nat' in temp as (_ & eq' & _).
    destruct l'. 2:inversion eq'. dependent destruction eq'.
    eapply nat_neq_pi. eapply type_conv. eapply A_eq_B.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.


Lemma sort_neq_pi_red l l' A B i j S T e : 
    ∙ ⊢< Ax l' > A -->>! Sort l : Sort l' ->
    ∙ ⊢< Ax l' > B -->>! Pi i j S T : Sort l' ->
    ∙ ⊢< prop > e : obseq (Ax l') (Sort l') A B -> 
    False.
Proof.
    intros A_red_sort B_red_pi A_eq_B.
    eapply redd_whnf_to_conv in A_red_sort as temp.
    eapply validity_conv_right, type_inv_sort' in temp as (_ & eq & _).
    eapply Ax_inj in eq. subst.
    eapply sort_neq_pi. 
    eapply type_conv; eauto.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.







Lemma pi_sort_inj_red l i j i' j' A A' B B' T T' e :
    ∙ ⊢< Ax l > T -->>! Pi i j A B : Sort l ->
    ∙ ⊢< Ax l > T' -->>! Pi i' j' A' B' : Sort l ->
    ∙ ⊢< prop > e : obseq (Ax l) (Sort l) T T' -> 
    i = i' /\ j = j'.
Proof.
    intros T_red T'_red eWt.
    eapply redd_whnf_to_conv in T_red as temp.
    eapply validity_conv_right, type_inv_pi' in temp as (_ & _ & _ & eq & _).
    eapply Ax_inj in eq. subst.
    eapply redd_whnf_to_conv in T'_red as temp.
    eapply validity_conv_right, type_inv_pi' in temp as (_ & _ & _ & eq & _).
    eapply Ax_inj in eq.
    eapply pi_sort_inj; eauto.
    eapply type_conv; eauto.
    eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conv_sort'.
Qed.

    
Lemma redd_cast1 Γ i A A' B e a :
    Γ ⊢< Ax i > A -->> A' : Sort i ->
    Γ ⊢< Ax i > B : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< i > cast i A B e a -->> cast i A' B e a : B.
Proof.
    intros A_redd_A' BWt eWt aWt. 
    dependent induction A_redd_A'.
    - eapply redd_refl; eauto using type_cast.
    - eapply redd_step. eapply red_cast1; eauto.
      eapply IHA_redd_A'; 
      eauto 7 using type_conv, red_to_conv, refl_ty, 
      conv_obseq, conv_sym, conv_sort, validity_ty_ctx.
Qed.

Lemma redd_cast2 Γ i A B B' e a :
    Γ ⊢< Ax i > A : Sort i ->
    val A ->
    Γ ⊢< Ax i > B -->> B' : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< i > cast i A B e a -->> cast i A B' e a : B.
Proof.
    intros AWt val_A B_redd_B' eWt aWt. 
    dependent induction B_redd_B'.
    - eapply redd_refl; eauto using type_cast.
    - eapply redd_step. eapply red_cast2; eauto.
      eapply redd_conv; eauto using red_to_conv, conv_sym.
      eapply IHB_redd_B'; 
      eauto 7 using type_conv, red_to_conv, refl_ty, 
      conv_obseq, conv_sym, conv_sort, validity_ty_ctx.
Qed.

Lemma redd_cast_nat_nat Γ A B e a:
    Γ ⊢< Ax (ty 0) > A -->> Nat : Sort (ty 0) ->
    Γ ⊢< Ax (ty 0) > B -->> Nat : Sort (ty 0) -> 
    Γ ⊢< prop > e : obseq (Ax (ty 0)) (Sort (ty 0)) A B ->
    Γ ⊢< ty 0 > a : A -> 
    Γ ⊢< ty 0 > cast (ty 0) A B e a -->> a : B.
Proof.
    intros A_red B_red eWt aWt.
    eapply redd_trans.
    eapply redd_cast1; 
    eauto using redd_to_conv, validity_conv_left.
    eapply redd_trans.
    eapply redd_cast2; 
    eauto 9 using type_conv, redd_to_conv, conv_obseq, validity_ty_ctx, 
    conv_sort, refl_ty, validity_conv_left, type_nat.
    eapply red_to_redd. eapply red_conv; eauto using redd_to_conv, conv_sym. 
    eapply red_cast_nat; 
    eauto 7 using type_conv, redd_to_conv, 
    conv_sort', validity_ty_ctx, conv_obseq.
Qed.

Lemma redd_cast_sort_sort Γ l A B e a:
    Γ ⊢< Ax (Ax l) > A -->> Sort l : Sort (Ax l) ->
    Γ ⊢< Ax (Ax l) > B -->> Sort l : Sort (Ax l) -> 
    Γ ⊢< prop > e : obseq (Ax (Ax l)) (Sort (Ax l)) A B ->
    Γ ⊢< Ax l > a : A -> 
    Γ ⊢< Ax l > cast (Ax l) A B e a -->> a : B.
Proof.
    intros A_red B_red eWt aWt.
    eapply redd_trans.
    eapply redd_cast1; 
    eauto using redd_to_conv, validity_conv_left.
    eapply redd_trans.
    eapply redd_cast2; 
    eauto 9 using type_conv, redd_to_conv, conv_obseq, validity_ty_ctx, 
    conv_sort, refl_ty, validity_conv_left, type_nat.
    eapply red_to_redd. eapply red_conv; eauto using redd_to_conv, conv_sym. 
    eapply red_cast_sort; 
    eauto 7 using type_conv, redd_to_conv, 
    conv_sort', validity_ty_ctx, conv_obseq.
Qed.

Lemma redd_cast_pi_pi Γ i k A B S T S' T' e s' a :
    Γ ⊢< Ax (Ru i (ty k)) > A -->> Pi i (ty k) S T : Sort (Ru i (ty k)) ->
    Γ ⊢< Ax (Ru i (ty k)) > B -->> Pi i (ty k) S' T' : Sort (ty (ru i k)) ->
    Γ ⊢< prop > e : obseq (Ax (Ru i (ty k))) (Sort (Ru i (ty k))) A B ->
    Γ ⊢< i > s' : S' ->
    Γ ⊢< Ru i (ty k) > a : A ->
    let s := cast i S' S (injpi1 i (ty k) S S' T T' e) s' in
    let app' := app i (ty k) S T a s in
    let res' := cast (ty k) (T <[ s..]) (T' <[ s'..]) (injpi2 i (ty k) S S' T T' e s')  app' in
    Γ ⊢< ty k > app i (ty k) S' T' (cast (Ru i (ty k)) A B e a) s' -->> res' : T' <[s'..].
Proof.
    intros A_red B_red eWt s'Wt aWt s app' res'.
    eapply redd_to_conv in A_red as temp.
    eapply validity_conv_right, type_inv_pi in temp as (SWt & TWt).
    eapply redd_to_conv in B_red as temp.
    eapply validity_conv_right, type_inv_pi in temp as (S'Wt & T'Wt).    

    eassert (Γ ⊢< ty k > app i (ty k) S' T' (cast (Ru i (ty k)) A B e a) s' -->> _ : T' <[ s'..]).
    {
      eapply redd_app; eauto.
      eapply redd_conv.
      eapply redd_trans.
      eapply redd_cast1; eauto using validity_conv_left, redd_to_conv.
      2:eauto using redd_to_conv.
      eapply redd_trans.
      eapply redd_cast2; 
      eauto 9 using validity_conv_right, redd_to_conv, type_conv, conv_obseq, 
        validity_ty_ctx, conv_sort, refl_ty, validity_conv_left.
      eapply red_to_redd.
      eapply red_conv.
      eapply red_cast_pi; eauto 7 using type_conv, redd_to_conv, conv_obseq, validity_ty_ctx, conv_sort.
      eauto using redd_to_conv, conv_sym. }

    eapply redd_trans. eauto.
    eapply red_to_redd.
    eapply redd_to_conv, validity_conv_right, type_inv_app' in H as (_ & _ & _ & H & _).
    eapply type_inv_lam' in H as (_ & _ & _ & H & _).
    eapply red_beta'; eauto using refl_ty.

    unfold res', app', s.
    simpl. f_equal. 
    ssimpl. 2,3:rasimpl.
    all:f_equal; try rewrite subst_id_reduce1; rasimpl; reflexivity.
Qed.






(* Failed factorization attempt: the following lemma does not work,
    because this would imply that any t u with ϵA t u would have both 
    types A1 and B1. But the fact that A1 and B1 are propositionaly
    equal does not imply that they are convertible.
Lemma LR_eq_to_iff_rel k A1 A2 ϵA B1 B2 ϵB e : 
    LR (ty k) A1 A2 ϵA -> 
    LR (ty k) B1 B2 ϵB ->
    ∙ ⊢< prop > e : obseq (Ax (ty k)) (Sort (ty k)) A1 B1 ->
    ϵA <~> ϵB. *)

Lemma prefundamental_cast l A1 A2 ϵA B1 B2 ϵB : 
    LR l A1 A2 ϵA -> 
    LR l B1 B2 ϵB ->
    (forall a1 a2 e1 e2, 
        ϵA a1 a2 -> 
        ∙ ⊢< l > a1 ≡ a2 : A1 -> 
        ∙ ⊢< prop > e1 ≡ e2 : obseq (Ax l) (Sort l) A1 B1 ->
        ϵB (cast l A1 B1 e1 a1) (cast l A2 B2 e2 a2)) /\ 
    (forall b1 b2 e1 e2, 
        ϵB b1 b2 -> 
        ∙ ⊢< l > b1 ≡ b2 : B1 -> 
        ∙ ⊢< prop > e1 ≡ e2 : obseq (Ax l) (Sort l) B1 A1 ->
        ϵA (cast l B1 A1 e1 b1) (cast l B2 A2 e2 b2)).
Proof.
    intros LR_A12 LR_B12. 
    pose proof (LR_A12' := LR_A12). pose proof (LR_B12' := LR_B12).
    generalize l A1 A2 ϵA LR_A12 LR_A12' B1 B2 ϵB LR_B12 LR_B12'.
    clear l A1 A2 ϵA LR_A12 LR_A12' B1 B2 ϵB LR_B12 LR_B12'.
    refine (LR_ind _ _ _ _ _); intros.
    - eapply LR_prop_inv in LR_B12. destruct LR_B12.
      destruct p.
      split; intros; try rewrite H0 in *; try rewrite H2 in *; eapply conv_cast; eauto.
    - eapply LR_to_red in LR_B12 as temp. destruct temp as (B1' & B1_red).
      unshelve eapply LR_ty_inv in LR_B12 ; eauto.
      simpl in LR_B12. destruct B1'.
      1,4,5,7-16:inversion LR_B12.
      + split; intros; eapply nat_neq_sort_red in A1_red_nat; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_nat.
      + split; intros; eapply nat_neq_pi_red in A1_red_nat; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_nat.
      + destruct LR_B12 as (eq' & _ & B2_red & ϵB_iff_ϵNat).
        split; intros; try rewrite H in *; try rewrite ϵB_iff_ϵNat in *.
        ++ eapply LR_irred_tm; eauto. eapply LR_nat; eauto.  
           reflexivity.
           1,2:destruct A1_red_nat, A2_red_nat, B1_red, B2_red.
           eauto 6 using redd_conv, redd_cast_nat_nat, validity_conv_left, LR_escape_ty.
           eauto 11 using redd_cast_nat_nat, validity_conv_right, type_conv, LR_escape_ty,
               conv_obseq, ctx_typing, conv_sort'.
        ++ eapply LR_irred_tm; eauto. eapply LR_nat; eauto.  
           reflexivity.
           1,2:destruct A1_red_nat, A2_red_nat, B1_red, B2_red.
           eapply redd_conv. eapply redd_cast_nat_nat; eauto using validity_conv_left.
           eauto using redd_to_conv, conv_trans, conv_sym.
           eapply redd_conv. eapply redd_cast_nat_nat; 
           eauto 8 using validity_conv_right, LR_escape_ty, type_conv, conv_obseq, ctx_typing, conv_sort'.
           eauto using redd_to_conv, conv_trans, conv_sym.

    - eapply LR_to_red in LR_B12 as temp. destruct temp as (B1' & B1_red).
      unshelve eapply LR_ty_inv in LR_B12 ; eauto.
      simpl in LR_B12. destruct B1'.
      1,4,5,7-16:inversion LR_B12.
      + destruct LR_B12 as (eq' & _ & B2_red & ϵB_iff_ϵsort).
        eapply Ax_inj in eq'. subst.
        split; intros; try rewrite H0 in * ; try rewrite ϵB_iff_ϵsort in *.
        ++ destruct H1. eexists. eapply LR_irred_ty; eauto. 
           1,2:destruct B1_red, B2_red, A1_red_U, A2_red_U.
           eapply redd_conv. eapply redd_cast_sort_sort; eauto using validity_conv_left.
           eauto using redd_to_conv.
           eapply redd_conv. eapply redd_cast_sort_sort; 
           eauto 7 using validity_conv_right, LR_escape_ty, type_conv, conv_obseq, ctx_typing, conv_sort'.
           eauto using redd_to_conv.
        ++ destruct H1. eexists. eapply LR_irred_ty; eauto.
           1,2:destruct B1_red, B2_red, A1_red_U, A2_red_U.
           eapply redd_conv. eapply redd_cast_sort_sort; eauto using validity_conv_left.
           eauto using redd_to_conv.
           eapply redd_conv. eapply redd_cast_sort_sort; 
           eauto 7 using validity_conv_right, LR_escape_ty, type_conv, conv_obseq, ctx_typing, conv_sort'.
           eauto using redd_to_conv.
      + split; intros; eapply sort_neq_pi_red in A1_red_U; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_U.
      + split; intros; eapply nat_neq_sort_red in A1_red_U; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_U.
    - eapply LR_to_red in LR_B12 as temp. destruct temp as (B1' & B1_red).
      unshelve eapply LR_ty_inv in LR_B12 ; eauto.
      simpl in LR_B12. destruct B1'.
      1,4,5,7-16:inversion LR_B12.
      + split; intros; eapply sort_neq_pi_red in A1_red_pi; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_pi.
      + destruct l0. 2:inversion LR_B12.
        rename B1'1 into S1'. rename B1'2 into T1'.
        destruct LR_B12 as (S2' & T2' & ϵS' & ϵT' & eq' & _ & B2_red & T1'_eq_T2' & LR_S12' & LR_T12' & ϵB_iff).
        split; intros; try rewrite ϵB_iff in *; try rewrite H in *.
        ++ eapply pi_sort_inj_red in A1_red_pi as temp; eauto using validity_conv_left, type_obseq_sym.
           destruct temp as (eq1 & eq2). dependent destruction eq2.
           unfold ϵPi. intros. split. 
           eapply conv_conv; eauto using conv_cast, LR_escape_ty, redd_whnf_to_conv.
           (* clear LR_A12' LR_B12'. *)
           intros s1 s2 ϵs.
           eapply H0 in LR_S12' as temp; eauto. clear H0.
           destruct temp as (_ & K2).
           eapply K2 in ϵs as temp; eauto using LR_escape_tm. 
           2:{ eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            destruct H2 as (H2a & H2b).
            eapply H2b in temp as temp'.
            eapply H1 in temp. 2:eapply LR_T; eauto. 2,3:eauto using LR_T12'.
            destruct temp as (K1 & _). eapply LR_irred_tm; eauto. 3:eapply K1; eauto. all:clear K1 K2.
            4:{ eapply conv_injpi2 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            3:{ eapply conv_app'; eauto using LR_escape_ty. eapply conv_cast; eauto using LR_escape_ty, LR_escape_tm.
                eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
                eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            1,2: destruct A1_red_pi, A2_red_pi, B1_red, B2_red.
            * eapply redd_cast_pi_pi; eauto using LR_escape_tm, validity_conv_left.
            * eapply redd_conv. eapply redd_cast_pi_pi; eauto using validity_conv_right, LR_escape_tm, LR_escape_ty, type_conv.
              eapply type_conv; eauto using validity_conv_right, conv_obseq, LR_escape_ty, conv_sort, ctx_typing.
              eapply subst; eauto using conv_sym, aux_subst, LR_escape_tm.
        ++ eapply pi_sort_inj_red in A1_red_pi as temp; eauto using validity_conv_left, type_obseq_sym.
           destruct temp as (eq1 & eq2). dependent destruction eq2.
           unfold ϵPi. intros. split. 
           eapply conv_conv; eauto using conv_cast, LR_escape_ty, redd_whnf_to_conv.
           intros s1 s2 ϵs.
           eapply H0 in LR_S12' as temp; eauto.
           destruct temp as (K2 & _).
           eapply K2 in ϵs as temp; eauto using LR_escape_tm. 
           2:{ eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            destruct H2.
            eapply H5 in temp as temp'.
            eapply H1 in ϵs as _temp. 2:eapply LR_T; eauto.  2,3:eauto using LR_T12'.
            destruct _temp as (_ & K1). eapply LR_irred_tm; eauto. 3:eapply K1; eauto. all:clear K1 K2.
            4:{ eapply conv_injpi2 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
               eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            3:{ eapply conv_app'; eauto using LR_escape_ty. eapply conv_cast; eauto using LR_escape_ty, LR_escape_tm.
                eapply conv_injpi1 ; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty.
                eapply conv_conv; eauto using validity_conv_left. eapply conv_obseq; eauto using redd_whnf_to_conv, ctx_typing, conversion. }
            1,2: destruct A1_red_pi, A2_red_pi, B1_red, B2_red.
            * eapply redd_cast_pi_pi; eauto using LR_escape_tm, validity_conv_left.
            * eapply redd_conv. eapply redd_cast_pi_pi; eauto using validity_conv_right, LR_escape_tm, LR_escape_ty, type_conv.
              eapply type_conv; eauto using validity_conv_right, conv_obseq, LR_escape_ty, conv_sort, ctx_typing.
              eapply subst; eauto using conv_sym, aux_subst, LR_escape_tm.
      + split; intros; eapply nat_neq_pi_red in A1_red_pi; 
        eauto using validity_conv_left, type_obseq_sym; inversion A1_red_pi.
Qed.


Lemma fundamental_cast Γ k A1 A2 B1 B2 e1 e2 a1 a2 :
    Γ ⊢< Ax (ty k) > A1 ≡ A2 : Sort (ty k) ->
    Γ ⊨< Ax (ty k) > A1 ≡ A2 : Sort (ty k) ->
    Γ ⊢< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊢< prop > e1 ≡ e2 : obseq (Ax (ty k)) (Sort (ty k)) A1 B1 ->
    Γ ⊨< prop > e1 ≡ e2 : obseq (Ax (ty k)) (Sort (ty k)) A1 B1 ->
    Γ ⊢< ty k > a1 ≡ a2 : A1 ->
    Γ ⊨< ty k > a1 ≡ a2 : A1 ->
    Γ ⊨< ty k > cast (ty k) A1 B1 e1 a1 ≡ cast (ty k) A2 B2 e2 a2 : B1.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 e1_conv_e2 _ a1_conv_a2 LRv_a12.
    unfold LRv. intros σ1 σ2 ϵσ.
    assert (Γ ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_A12 as temp; eauto. destruct temp as (ϵA & LR_A12).
    eapply LRv_to_LR_ty in LRv_B12 as temp; eauto. destruct temp as (ϵB & LR_B12).
    eapply LRv_to_LR_ty_copy in LRv_B11 as LR_B11; eauto.
    eapply LRv_to_LR_tm in LRv_a12 as LR_a12; eauto.
    clear LRv_A12 LRv_B11 LRv_B12 LRv_a12.
    eexists. split; eauto. rasimpl.
    eapply prefundamental_cast; eauto using subst, LR_subst_escape.
Qed.

Lemma prefundamental_cast_refl l A B ϵA a e : 
    LR l A B ϵA -> 
    ϵA a a ->
    ∙ ⊢< prop > e : obseq (Ax l) (Sort l) A B ->
    ϵA (cast l A B e a) a.
Proof.
    intros LR_AB.
    pose proof (LR_AB' := LR_AB).
    generalize l A B ϵA LR_AB LR_AB' e a.
    clear l A B ϵA LR_AB LR_AB' e a.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. rewrite H2 in *. 
      eapply conv_conv; eauto using conv_sym.
      eapply conv_cast_refl; eauto using validity_conv_left.
    - rewrite H in *. 
      eapply LR_irred_tm; eauto using prefundamental_nat.
      2:eapply redd_refl; eauto using LR_escape_tm, prefundamental_nat, validity_conv_right.
      destruct A1_red_nat, A2_red_nat.
      eapply redd_conv. eapply redd_cast_nat_nat; 
      eauto 6 using LR_escape_tm, prefundamental_nat, type_conv, 
        redd_to_conv, conv_sym, validity_conv_left.
      eauto using redd_to_conv.
    - rewrite H0 in *. 
      destruct H1 as (R' & lr). exists R'. 
      eapply LR_irred_ty; eauto. 
      2:eapply redd_refl; eauto using LR_escape_ty, validity_conv_right. 
      destruct A1_red_U, A2_red_U.
      eapply redd_conv. eapply redd_cast_sort_sort; 
      eauto 6 using LR_escape_ty, type_conv, 
        redd_to_conv, conv_sym, validity_conv_left.
      eauto using redd_to_conv.

    - eapply LR_escape_tm in H2 as a1_conv_a2; eauto.
      eapply LR_escape_ty in LR_AB' as A1_conv_A2.
      rewrite H in *. unfold ϵPi. split. 
      eapply conv_conv; eauto  using conv_cast_refl, LR_escape_tm, validity_conv_left, redd_whnf_to_conv, conv_sym, conv_trans.

      intros s1 s2 ϵs.
      assert (ϵS s1 s1) as ϵs11 by eauto using (LR_sym_tm LR_S), (LR_trans_tm LR_S).
      destruct H2. eapply H4 in ϵs as ϵs'. eapply LR_trans_tm; eauto.
      assert (ϵT s1 s2 <~> ϵT s1 s1) by eauto using LR_irrel.
      rewrite H5. clear ϵs ϵs' H5 s2.

      assert (∙ ⊢< prop > injpi1 i (ty k) S1 S2 T1 T2 e : obseq (Ax i) (Sort i) S1 S2) as injpi1Wt.
      { eapply type_conv. eapply type_injpi1; eauto using LR_escape_ty, validity_conv_left, validity_conv_right, conv_ty_in_ctx_conv.
      eapply type_conv; eauto. eapply conv_obseq; eauto using ctx_typing, conv_sort, redd_whnf_to_conv.
      eapply conv_obseq; eauto using conv_sym, LR_escape_ty, ctx_typing, conv_sort. }

      eassert (∙ ⊢< prop > injpi2 i (ty k) S1 S2 T1 T2 e s1 : _) as injpi2Wt.
      { eapply type_injpi2; eauto using LR_escape_ty, validity_conv_left, validity_conv_right, conv_ty_in_ctx_conv, LR_escape_tm, type_conv.
        eapply type_conv; eauto. eapply conv_obseq; eauto using ctx_typing, conv_sort, redd_whnf_to_conv. }

      eapply H0 in LR_S as ϵs11'; eauto.

      assert (ϵS (cast i S2 S1 (injpi1 i (ty k) S1 S2 T1 T2 e) s1) s1).
      { eapply LR_trans_tm  in ϵs11'; eauto.
        eapply LR_sym_tm; eauto. 
        eapply prefundamental_cast; eauto using LR_escape_tm, LR_sym, refl_ty. }
      clear ϵs11'. rename H5 into ϵs11'.

      eapply H4 in ϵs11' as ϵs11''. 
      assert (ϵT (cast i S2 S1 (injpi1 i (ty k) S1 S2 T1 T2 e) s1) s1 <~> ϵT s1 s1) by eauto 6 using LR_irrel, LR_sym. 

      eassert (ϵT (cast _ _ _ _ _) _ (app i (ty k) S1 T1 a _) (app i (ty k) S1 T1 a (cast i S2 S1 (injpi1 i (ty k) S1 S2 T1 T2 e) s1))) 
        by eauto using (LR_sym_tm (LR_T _ _ _)), (LR_trans_tm (LR_T _ _ _)).

      eapply H1 in H6; eauto. 

      eapply LR_trans_tm in ϵs11''; eauto.
      eapply LR_app_ann_left. 4:eauto using conv_sym, LR_escape_ty. 3:eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_ty.
      eauto.
      eapply LR_sym_tm; eauto.
      eapply LR_app_ann_left.  4:eauto using conv_sym, LR_escape_ty. 3:eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_ty.
      eauto.
      eapply LR_sym_tm; eauto.

      rewrite H5 in *.
      eapply LR_irred_tm. eauto. 3:exact ϵs11''.
      destruct A1_red_pi, A2_red_pi.
      eapply redd_conv. eapply redd_cast_pi_pi; eauto using LR_escape_tm, validity_conv_left, LR_escape_ty, type_conv.
      eapply subst; eauto using conv_sym, aux_subst, LR_escape_tm.
      eapply redd_refl. eapply type_app'; intros; eauto using LR_escape_tm, validity_conv_left, type_conv, LR_escape_ty, redd_whnf_to_conv.
Qed.


Lemma fundamental_cast_refl Γ k A B e a :
    Γ ⊢< Ax (ty k) > A ≡ B : Sort (ty k) ->
    Γ ⊨< Ax (ty k) > A ≡ B : Sort (ty k) ->
    Γ ⊢< prop > e : obseq (Ax (ty k)) (Sort (ty k)) A B ->
    Γ ⊨< prop > e ≡ e : obseq (Ax (ty k)) (Sort (ty k)) A B ->
    Γ ⊢< ty k > a : A ->
    Γ ⊨< ty k > a ≡ a : A ->
    Γ ⊨< ty k > cast (ty k) A B e a ≡ a : B.
Proof.
    intros A_conv_B LRv_AB eWt LRv_e aWt LRv_a.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply LRv_to_LR_ty in LRv_AB as temp; eauto. destruct temp as (ϵA & LR_AB).
    eapply LRv_to_LR_tm in LRv_a as LR_a; eauto.
    assert (⊩s σ1 ≡ σ1 : Γ) as ϵσ11 by eauto using LR_subst_sym, LR_subst_trans.
    eapply LRv_to_LR_ty_copy in ϵσ11 as LR_AB'; eauto. clear ϵσ11.
    assert (Γ ⊨< Ax (ty k) > B ≡ B : Sort (ty k)) as LRv_BB by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_BB as temp; eauto. destruct temp as (ϵB & LR_B).
    assert (ϵB <~> ϵA) by eauto using LR_irrel, LR_sym. eapply LR_iff_rel in LR_B; eauto.
    clear ϵB H LRv_AB LRv_BB LRv_a.
    eexists. split; eauto.
    rasimpl. eapply LR_trans_tm; eauto.
    unshelve eapply prefundamental_cast_refl; eauto.
    eapply LR_sym_tm in LR_a as temp; eauto. eapply LR_trans_tm in temp; eauto.
    eapply validity_conv_left, subst; eauto using refl_ty, LR_subst_escape.
Qed.


Lemma red_cast_pi' Γ i j A1 A2 B1 B2 e f X Y l :
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax j > B1 : Sort j ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax j > B2 : Sort j ->
    Γ ⊢< prop > e : obseq (Ax (Ru i j)) (Sort (Ru i j)) (Pi i j A1 B1) (Pi i j A2 B2) ->
    Γ ⊢< Ru i j > f : Pi i j A1 B1 -> 
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in 
    let B1' := (up_ren S) ⋅ B1 in 
    let B2' := (up_ren S) ⋅ B2 in
    let t1 := cast i A2' A1' (injpi1 i j A1' A2' B1' B2' (S ⋅ e)) (var 0) in
    let t2 := app i j A1' B1' (S ⋅ f) t1 in 
    let t3 := cast j (B1 <[t1.: S >> var]) B2 (injpi2 i j A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in 
    let t4 := lam i j A2 B2 t3 in 
    X = Pi i j A2 B2 ->
    Y = t4 ->
    l = Ru i j ->
    Γ ⊢< l > cast l (Pi i j A1 B1) (Pi i j A2 B2) e f --> Y : X.
Proof.
    intros. subst. eauto using red_cast_pi.
Qed.
    

Lemma type_inv_cast' Γ i A B e a l T :
    Γ ⊢< l > cast i A B e a : T ->
    Γ ⊢< l > cast i A B e a : T /\
    Γ ⊢< Ax i > A : Sort i /\
    Γ ⊢< Ax i > B : Sort i /\
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B /\ 
    Γ ⊢< i > a : A /\
    l = i /\
    Γ ⊢< Ax i > T ≡ B : Sort l.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (AWt & BWt & eWt & aWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma fundamental_cast_pi Γ i n A1 A2 B1 B2 e f :
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A1 : Sort i ->
    Γ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ,, (i, A1) ⊨< Ax (ty n) > B1 ≡ B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ⊨< Ax i > A2 ≡ A2 : Sort i ->
    Γ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ,, (i, A2) ⊨< Ax (ty n) > B2 ≡ B2 : Sort (ty n) ->
    Γ ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊨< prop > e ≡ e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< Ru i (ty n) > f : Pi i (ty n) A1 B1 ->
    Γ ⊨< Ru i (ty n) > f ≡ f : Pi i (ty n) A1 B1 ->
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let B1' := up_ren S ⋅ B1 in
    let B2' := up_ren S ⋅ B2 in
    let t5 := cast i A2' A1' (injpi1 i (ty n) A1' A2' B1' B2' (S ⋅ e)) (var 0) in
    let t6 := app i (ty n) A1' B1' (S ⋅ f) t5 in
    let t7 := cast (ty n) (B1 <[ t5 .: S >> var]) B2 (injpi2 i (ty n) A1' A2' B1' B2' (S ⋅ e) (var 0)) t6 in
    let t8 := lam i (ty n) A2 B2 t7 in
    Γ ⊨< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f ≡ t8 : Pi i (ty n) A2 B2.
Proof.
    intros A1Wt LRv_A1 B1Wt LRv_B1 A2Wt LRv_A2 B2Wt LRv_B2 eWt LRv_e fWt LRv_f A1' A2' B1' B2' t5 t6 t7 t8.
    unfold LRv. intros σ1 σ2 ϵσ.
    assert (Γ ⊨< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f 
            ≡ cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f : (Pi i (ty n) A2 B2)).
    eapply fundamental_cast; eauto using refl_ty, conv_pi'.
    1,2:eapply fundamental_pi; eauto using refl_ty.
    eapply H in ϵσ as temp.
    destruct temp as (LR_pi & lr & ϵcast).
    eexists. split. eauto.
    eapply LR_redd; eauto.
    eauto using redd_refl, validity_conv_left, LR_escape_tm.
    eapply red_to_redd.
    simpl in ϵcast. eapply LR_escape_tm, validity_conv_right, type_inv_cast' in ϵcast as temp; eauto.
    destruct temp as (_ & pi1 & pi2 & e'Wt & f'Wt & _).
    eapply type_inv_pi' in pi1 as (_ & A1'Wt & B1'Wt & _).
    eapply type_inv_pi' in pi2 as (_ & A2'Wt & B2'Wt & _).
    eapply red_conv.
    simpl.
    eapply red_cast_pi'; eauto.
    1:{unfold t5, A1', A2', B1', B2'.
        f_equal. f_equal;rasimpl.
        1:f_equal; f_equal; rasimpl. 
        all:reflexivity. }
    assert (Pi i (ty n) (A2 <[ σ2]) (B2 <[ up_term_term σ2]) = (Pi i (ty n) A2 B2) <[ σ2]) by (rasimpl; reflexivity).
    rewrite H0.
    eapply subst; eauto using conv_pi, refl_ty, LR_subst_escape, LR_subst_sym.
Qed.

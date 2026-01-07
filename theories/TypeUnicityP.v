From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


Theorem var_unicity Γ l x A l' A' :
  Γ ∋< l > x : A ->
  Γ ∋< l' > x : A' ->
  l = l' /\ A = A'.
Proof.
  generalize Γ l l' A A'. clear Γ l l' A A'.
  induction x; intros.
  - dependent destruction H. dependent destruction H0. split; eauto.
  - dependent destruction H. dependent destruction H0.
    eapply IHx in H as (HA & HB); eauto. subst. split; eauto.
Qed.

Inductive type_inv_data : ctx -> level -> term -> term -> Prop :=
  | inv_data_var Γ l x A T
    (var_in_ctx : Γ ∋< l > x : A)
    (conv_ty : Γ ⊢< Ax l > T ≡ A : Sort l)
    : type_inv_data Γ l (var x) T
  | inv_data_sort Γ l i T
    (lvl_eq : l = Ax (Ax i))
    (conv_ty : Γ ⊢< Ax (Ax (Ax i)) > T ≡ Sort (Ax i) : Sort (Ax (Ax i)))
    : type_inv_data Γ l (Sort i) T
  | inv_data_assm Γ c A l T 
    (assm_in_sig : nth_error assm_sig c = Some A)
    (A_Wt : ∙ ⊢< Ax prop > A : Sort prop)
    (lvl_eq : l = prop)
    (conv_ty : Γ ⊢< Ax prop > T ≡ A : Sort prop)
    : type_inv_data Γ l (assm c) T
  | inv_data_pi Γ l A B i j T
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ⊢< Ax j > B : Sort j)
    (lvl_eq : l = Ax (Ru i j))
    (conv_ty : Γ ⊢< Ax (Ax (Ru i j)) > T ≡ Sort (Ru i j) : Sort (Ax (Ru i j)))
    : type_inv_data Γ l (Pi i j A B) T
  | inv_data_lam Γ l A B t i j T
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ⊢< Ax j > B : Sort j)
    (t_Wt : Γ ,, (i , A) ⊢< j > t : B)
    (lvl_eq : l = Ru i j)
    (conv_ty : Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A B : Sort (Ru i j))
    : type_inv_data Γ l (lam i j A B t) T
  | inv_data_app Γ A B t u i j T l
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ⊢< Ax j > B : Sort j)
    (t_Wt : Γ ⊢< Ru i j > t : Pi i j A B)
    (u_Wt : Γ ⊢< i > u : A)
    (lvl_eq : l = j)
    (conv_ty : Γ ⊢< Ax j > T ≡ B <[ u.. ] : Sort j)
    : type_inv_data Γ l (app i j A B t u) T
  | inv_data_Nat Γ l T
    (lvl_eq : l = ty 1)
    (conv_ty : Γ ⊢< ty 2 > T ≡ Sort (ty 0) : Sort (ty 1))
    : type_inv_data Γ l Nat T
  | type_inv_zero l Γ T
    (lvl_eq : l = ty 0)
    (conv_ty : Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0))
    : type_inv_data Γ l zero T
  | type_inv_succ Γ l t T
    (t_Wt : Γ ⊢< ty 0 > t : Nat)
    (lvl_eq : l = ty 0)
    (conv_ty : Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0))
    : type_inv_data Γ l (succ t) T
  | type_inv_rec Γ l i P p_zero p_succ t T
    (P_Wt : Γ ,, (ty 0 , Nat) ⊢< Ax i > P : Sort i)
    (p_zero_Wt : Γ ⊢< i > p_zero : P <[ zero .. ])
    (p_succ_Wt : Γ ,, (ty 0 , Nat) ,, (i , P) ⊢< i > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ])
    (t_Wt : Γ ⊢< ty 0 > t : Nat)
    (lvl_eq : l = i)
    (conv_ty : Γ ⊢< Ax i > T ≡ P <[ t.. ] : Sort i)
    : type_inv_data Γ l (rec i P p_zero p_succ t) T
  | inv_data_acc Γ n A R a l T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop)
    (a_Wt : Γ ⊢< ty n > a : A)
    (lvl_eq : l = Ax prop)
    (conv_ty : Γ ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop))
    : type_inv_data Γ l (acc (ty n) A R a) T
  | inv_data_accin Γ n A R a p l T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop)
    (a_Wt : Γ ⊢< ty n > a : A)
    (A_wk := (S >> S) ⋅ A)
    (R_wk := (up_ren (up_ren (S >> S))) ⋅ R)
    (acc_wk := acc (ty n) A_wk R_wk (var 1) )
    (R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))])
    (p_Wt : Γ ⊢< prop > p : Pi (ty n) prop A (Pi prop prop R' acc_wk))
    (lvl_eq : l = prop)
    (conv_ty : Γ ⊢< Ax prop > T ≡ acc (ty n) A R a : Sort prop)
    : type_inv_data Γ l (accin (ty n) A R a p) T
  | inv_data_accinv Γ n A R a p b r l T 
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (R_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop)
    (a_Wt : Γ ⊢< ty n > a : A)
    (p_Wt : Γ ⊢< prop > p : acc (ty n) A R a)
    (b_Wt : Γ ⊢< ty n > b : A)
    (r_Wt : Γ ⊢< prop > r : R <[a.:b..])
    (lvl_eq : l = prop)
    (conv_ty : Γ ⊢< Ax prop > T ≡ acc (ty n) A R b : Sort prop)
    : type_inv_data Γ l (accinv (ty n) A R a p b r) T
  | inv_data_accel Γ n l A R a q P p T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (R_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop)
    (P_Wt : Γ ,, (ty n, A) ⊢< Ax l > P : Sort l)
    (R' := (1 .: (0 .: (S >> S))) ⋅ R)
    (P' := (1 .: (S >> S >> S)) ⋅ P)
    (B := Pi (ty n) l (S ⋅ A) (Pi prop l R' P'))
    (P'' := (1.: (S >> S)) ⋅ P)
    (p_Wt : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ⊢< l > p : P'')
    (a_Wt : Γ ⊢< ty n > a : A)
    (q_Wt : Γ ⊢< prop > q : acc (ty n) A R a)
    (conv_ty : Γ ⊢< Ax l > T ≡ P <[a ..] : Sort l)
    : type_inv_data Γ l (accel (ty n) l A R P p a q) T
  | inv_data_accelcomp Γ n m A R a q P p l T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (R_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop)
    (P_Wt : Γ ,, (ty n, A) ⊢< Ax (ty m) > P : Sort (ty m))
    (R' := (1 .: (0 .: (S >> S))) ⋅ R)
    (P' := (1 .: (S >> S >> S)) ⋅ P)
    (B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R' P'))
    (P'' := (1.: (S >> S)) ⋅ P)
    (p_Wt : Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ⊢< ty m > p : P'')
    (a_Wt : Γ ⊢< ty n > a : A)
    (q_Wt : Γ ⊢< prop > q : acc (ty n) A R a)
    (Awk := (S >> S) ⋅ A)
    (Rwk := (up_ren (up_ren (S >> S))) ⋅ R)
    (Pwk := (up_ren (S >> S)) ⋅ P)
    (pwk := (up_ren (up_ren (S >> S))) ⋅ p)
    (t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0))
    (t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0)
    (t2 := R<[S ⋅ a .: (var 0 .: S >> var)])
    (t3 := lam prop (ty m) t2 P'' t1)
    (t4 := Pi prop (ty m) t2 P'')
    (t5 := lam (ty n) (ty m) A t4 t3)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡
         obseq (ty m) (P <[a ..])
           (accel (ty n) (ty m) A R P p a q)
           (p <[ t5 .: a ..]) : Sort prop)
    : type_inv_data Γ l (accelcomp (ty n) (ty m) A R P p a q) T

  | inv_data_obseq Γ n A a b l T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (a_Wt : Γ ⊢< ty n > a : A)
    (b_Wt : Γ ⊢< ty n > b : A)
    (lvl_eq : l = Ax prop)
    (conv_ty :
       Γ ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop))
    : type_inv_data Γ l (obseq (ty n) A a b) T

  | inv_data_obsrefl Γ n A a l T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (a_Wt : Γ ⊢< ty n > a : A)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡ obseq (ty n) A a a : Sort prop)
    : type_inv_data Γ l (obsrefl (ty n) A a) T

  | inv_data_J Γ n A a P p b e l T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (a_Wt : Γ ⊢< ty n > a : A)
    (P_Wt : Γ ,, (ty n , A) ⊢< Ax prop > P : Sort prop)
    (p_Wt : Γ ⊢< prop > p : P <[a..])
    (b_Wt : Γ ⊢< ty n > b : A)
    (e_Wt : Γ ⊢< prop > e : obseq (ty n) A a b)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡ P <[b..] : Sort prop)
    : type_inv_data Γ l (J (ty n) A a P p b e) T

  | inv_data_cast Γ i A B e a l T
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ⊢< Ax i > B : Sort i)
    (e_Wt : Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B)
    (a_Wt : Γ ⊢< i > a : A)
    (lvl_eq : l = i)
    (conv_ty :
       Γ ⊢< Ax i > T ≡ B : Sort i)
    : type_inv_data Γ l (cast i A B e a) T

  | inv_data_injpi1 Γ i n A1 A2 B1 B2 e l T
    (A1_Wt : Γ ⊢< Ax i > A1 : Sort i)
    (B1_Wt : Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n))
    (A2_Wt : Γ ⊢< Ax i > A2 : Sort i)
    (B2_Wt : Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n))
    (e_Wt :
       Γ ⊢< prop >
         e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n)))
             (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2))
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡ obseq (Ax i) (Sort i) A2 A1 : Sort prop)
    : type_inv_data Γ l (injpi1 i (ty n) A1 A2 B1 B2 e) T

  | inv_data_injpi2 Γ i n A1 A2 B1 B2 e a2 l T
    (A1_Wt : Γ ⊢< Ax i > A1 : Sort i)
    (B1_Wt : Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n))
    (A2_Wt : Γ ⊢< Ax i > A2 : Sort i)
    (B2_Wt : Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n))
    (e_Wt :
       Γ ⊢< prop >
         e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n)))
             (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2))
    (a2_Wt : Γ ⊢< i > a2 : A2)
    (a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡
         obseq (Ax (ty n)) (Sort (ty n))
           (B1<[ a1 ..]) (B2<[a2..]) : Sort prop)
    : type_inv_data Γ l (injpi2 i (ty n) A1 A2 B1 B2 e a2) T.


Lemma type_inv Γ l t T :
  Γ ⊢< l > t : T ->
  type_inv_data Γ l t T.
Proof.
  intros.
  apply validity_ty_ty in H as T_Wt.
  induction H. 1-20:econstructor; eauto using conv_refl.
  eapply validity_conv_left in H0 as AWt.
  eapply IHtyping in AWt as IH.
  depelim IH; econstructor; subst; eauto using conv_sym, conv_trans.
Qed.

Theorem type_sort_unicity Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ B : Sort l /\ l = l'.
Proof.
  intros.
  induction H.
  2-20:eapply type_inv in H0; dependent destruction H0; subst; eauto 13 using conv_sym.
  - eapply type_inv in H0. dependent destruction H0.
    eapply var_unicity in H1 as (HA & HB); eauto. subst. eauto using conv_sym.
  - rewrite H1 in assm_in_sig. dependent destruction assm_in_sig.
    split; eauto using conv_sym.
  - eapply IHtyping in H0 as (HA & HB). subst. eauto using conv_sym, conv_trans.
Qed.

Corollary type_unicity Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ B : Sort l.
Proof.
  intros. eapply type_sort_unicity in H as (HA & HB); eauto. subst.
  eauto using conv_sym.
Qed.

Corollary sort_unicity Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  l = l'.
Proof.
  intros. eapply type_sort_unicity in H as (HA & HB); eauto.
Qed.

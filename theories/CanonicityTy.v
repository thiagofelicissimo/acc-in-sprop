(* We show hove to derive strong canonicity (with a sig instead of exists)
   from the canonicity result of LogicalRelation.v *)
(* A similar technique could be used for decidability of equality *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory Reduction LogicalRelation.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.

Open Scope subst_scope.

Reserved Notation "Γ ⊢'< l > t : T" (at level 50, l, t, T at next level).
Reserved Notation "Γ ⊢'< l > t ≡ u : T" (at level 50, l, t, u, T at next level).
Reserved Notation "⊢' Γ" (at level 50).

Inductive typing' : ctx -> level -> term → term → Type :=

| type'_var :
    ∀ Γ x l A,
      ⊢' Γ -> 
      nth_error Γ x = Some (l , A) →
      (Γ ⊢'< l > (var x) : ((plus (S x)) ⋅ A))

| type'_sort :
    ∀ Γ l,
      ⊢' Γ -> 
      Γ ⊢'< Ax (Ax l) > Sort l : Sort (Ax l)

| type'_pi :
    ∀ Γ i j A B,
      Γ ⊢'< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B : Sort j →
      Γ ⊢'< Ax (Ru i j) > Pi i j A B : Sort (Ru i j)


| type'_lam :
    ∀ Γ i j A B t,
      Γ ⊢'< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢'< j > t : B →
      Γ ⊢'< Ru i j > lam i j A B t : Pi i j A B

| type'_app :
    ∀ Γ i j A B t u,
      Γ ⊢'< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B : Sort j →
      Γ ⊢'< Ru i j > t : Pi i j A B →
      Γ ⊢'< i > u : A →
      Γ ⊢'< j > app i j A B  t u : B <[ u .. ] 

| type'_nat :
    ∀ Γ,
      ⊢' Γ -> 
      Γ ⊢'< ty 1 > Nat : Sort (ty 0)

| type'_zero : 
    ∀ Γ,
      ⊢' Γ -> 
      Γ ⊢'< ty 0 > zero : Nat

| type'_succ : 
    ∀ Γ t, 
      Γ ⊢'< ty 0 > t : Nat ->
      Γ ⊢'< ty 0 > succ t : Nat

| type'_rec : 
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢'< Ax l > P : Sort l ->
      Γ ⊢'< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢'< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢'< ty 0 > t : Nat ->
      Γ ⊢'< l > rec l P p_zero p_succ t : P <[ t .. ]

| type'_acc : 
    ∀ Γ i A R a,
    Γ ⊢'< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R : Sort prop -> 
    Γ ⊢'< i > a : A -> 
    Γ ⊢'< Ax prop > acc i A R a : Sort prop

| type'_accin : 
    ∀ Γ i A R a p,
    Γ ⊢'< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R : Sort prop -> 
    Γ ⊢'< i > a : A -> 
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc i A_wk R_wk (var 1)  in
    let R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ⊢'< prop > p : Pi i prop A (Pi prop prop R' acc_wk) ->
    Γ ⊢'< prop > accin i A R a p : acc i A R a
  
| type'_accel : 
    ∀ Γ i l A R a q P p,
    Γ ⊢'< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R : Sort prop -> 
    Γ ,, (i, A) ⊢'< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢'< l > p : P'' ->
    Γ ⊢'< i > a : A -> 
    Γ ⊢'< prop > q : acc i A R a -> 
    Γ ⊢'< l > accel i l A R P p a q : P <[a ..]

| type'_conv : 
    ∀ Γ l A B t,
      Γ ⊢'< l > t : A -> 
      Γ ⊢'< Ax l > A ≡ B : Sort l ->
      Γ ⊢'< l > t : B

with ctx_typing' : ctx -> Type :=
| ctx'_nil : 
      ⊢' ∙

| ctx'_cons : 
    ∀ Γ l A, 
      ⊢' Γ -> 
      Γ ⊢'< Ax l > A : Sort l ->
      ⊢' (Γ ,, (l , A))

with conversion' : ctx -> level -> term -> term -> term -> Type :=


| conv'_var :
    ∀ Γ x l A,
      nth_error Γ x = Some (l , A) →
      ⊢' Γ -> 
      (Γ ⊢'< l > (var x) ≡ (var x) : ((plus (S x)) ⋅ A))

| conv'_sort :
    ∀ Γ l,
      ⊢' Γ ->
      Γ ⊢'< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l)

| conv'_pi :
    ∀ Γ i j A B A' B',
      Γ ⊢'< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B ≡ B' : Sort j →
      Γ ⊢'< Ax (Ru i j) > Pi i j A B ≡ Pi i j A' B' : Sort (Ru i j)

| conv'_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢'< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢'< j > t ≡ t' : B →
      Γ ⊢'< Ru i j > lam i j A B t ≡ lam i j A' B' t' : Pi i j A B

| conv'_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ⊢'< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B ≡ B': Sort j →
      Γ ⊢'< Ru i j > t ≡ t' : Pi i j A B →
      Γ ⊢'< i > u ≡ u' : A →
      Γ ⊢'< j > app i j A B t u ≡ app i j A' B' t' u' : B <[ u .. ] 

| conv'_nat :
    ∀ Γ,
      ⊢' Γ ->
      Γ ⊢'< ty 1 > Nat ≡ Nat : Sort (ty 0)

| conv'_zero : 
    ∀ Γ,
      ⊢' Γ ->
      Γ ⊢'< ty 0 > zero ≡ zero : Nat

| conv'_succ : 
    ∀ Γ t t', 
      Γ ⊢'< ty 0 > t ≡ t' : Nat ->
      Γ ⊢'< ty 0 > succ t ≡ succ t' : Nat

| conv'_rec : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢'< Ax l > P ≡ P' : Sort l ->
      Γ ⊢'< l > p_zero ≡ p_zero' : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢'< l > p_succ ≡ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢'< ty 0 > t ≡ t' : Nat ->
      Γ ⊢'< l > rec l P p_zero p_succ t ≡ rec l P' p_zero' p_succ' t' : P <[ t .. ]


| conv'_acc : 
    ∀ Γ i A A' R R' a a',
    Γ ⊢'< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R ≡ R' : Sort prop -> 
    Γ ⊢'< i > a ≡ a' : A -> 
    Γ ⊢'< Ax prop > acc i A R a ≡ acc i A' R' a' : Sort prop

| conv'_accin : 
    ∀ Γ i A A' R R' a a' p p',
    Γ ⊢'< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R ≡ R' : Sort prop -> 
    Γ ⊢'< i > a ≡ a' : A -> 
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc i A_wk R_wk (var 1)  in
    let R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ⊢'< prop > p ≡ p' : Pi i prop A (Pi prop prop R' acc_wk) ->
    Γ ⊢'< prop > accin i A R a p ≡ accin i A' R' a' p' : acc i A R a
  
| conv'_accel : 
    ∀ Γ i l A A' R R' a a' q q' P P' p p',
    Γ ⊢'< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R ≡ R' : Sort prop -> 
    Γ ,, (i, A) ⊢'< Ax l > P ≡ P' : Sort l ->
    let R_ := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P_ := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢'< l > p ≡ p' : P'' ->
    Γ ⊢'< i > a ≡ a': A -> 
    Γ ⊢'< prop > q ≡ q' : acc i A R a -> 
    Γ ⊢'< l > accel i l A R P p a q ≡ accel i l A' R' P' p' a' q' : P <[a ..]
  
| conv'_conv : 
    ∀ Γ l A B t t',
      Γ ⊢'< l > t ≡ t' : A -> 
      Γ ⊢'< Ax l > A ≡ B : Sort l ->
      Γ ⊢'< l > t ≡ t' : B

| conv'_irrel : 
    ∀ Γ A t t',
      Γ ⊢'< prop > t : A -> 
      Γ ⊢'< prop > t' : A ->
      Γ ⊢'< prop > t ≡ t' : A

| conv'_beta : 
    ∀ Γ i j A B t u,
      Γ ⊢'< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢'< j > t : B →
      Γ ⊢'< i > u : A →
      Γ ⊢'< j > app i j A B (lam i j A B t) u ≡ t <[ u .. ] : B <[ u .. ] 


| conv_eta :
    ∀ Γ i j A B t u,
      Γ ⊢'< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢'< Ax j > B : Sort j →
      Γ ⊢'< Ru i j > t : Pi i j A B →
      Γ ⊢'< Ru i j > u : Pi i j A B →
      let t_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B) (S ⋅ t) (var 0) in 
      let u_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B) (S ⋅ u) (var 0) in 
      Γ ,, (i , A) ⊢'< j > t_app_x ≡ u_app_x : B →
      Γ ⊢'< Ru i j > t ≡ u : Pi i j A B

| conv'_rec_zero : 
    ∀ Γ l P p_zero p_succ,
      Γ ,, (ty 0 , Nat) ⊢'< Ax l > P : Sort l ->
      Γ ⊢'< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢'< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢'< l > rec l P p_zero p_succ zero ≡ p_zero : P <[ zero .. ]

| conv'_rec_succ : 
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢'< Ax l > P : Sort l ->
      Γ ⊢'< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢'< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢'< ty 0 > t : Nat ->
      Γ ⊢'< l > rec l P p_zero p_succ (succ t) ≡ 
          p_succ <[(rec l P p_zero p_succ t) .: t ..] : P <[ (succ t) .. ]

| conv'_accel_accin : 
    ∀ Γ i l A R a q P p,
    Γ ⊢'< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢'< Ax prop > R : Sort prop -> 
    Γ ,, (i, A) ⊢'< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢'< l > p : P'' ->
    Γ ⊢'< i > a : A -> 
    Γ ⊢'< prop > q : acc i A R a -> 
    let Awk := (S >> S) ⋅ A in 
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in 
    let Pwk := (up_ren (S >> S)) ⋅ P in 
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv i Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel i l Awk Rwk Pwk pwk (var 1) t0 in 
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in 
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i l A t4 t3 in
    Γ ⊢'< l > accel i l A R P p a q ≡ p <[ t5 .: a ..] : P <[a ..]

| conv'_sym : 
    ∀ Γ l t u A,
      Γ ⊢'< l > t ≡ u : A ->
      Γ ⊢'< l > u ≡ t : A
  
| conv'_trans : 
    ∀ Γ l t u v A,
      Γ ⊢'< l > t ≡ u : A ->
      Γ ⊢'< l > u ≡ v : A ->
      Γ ⊢'< l > t ≡ v : A

where "Γ ⊢'< l > t : A" := (typing' Γ l t A)
and   "⊢' Γ" := (ctx_typing' Γ)
and   "Γ ⊢'< l > t ≡ u : A" := (conversion' Γ l t u A).


Inductive Squash (A : Type) : Prop := 
| sq : A -> Squash A.


Scheme typing__mut := Induction for typing Sort Prop
with conversion__mut := Induction for conversion Sort Prop
with ctx_typing__mut := Induction for ctx_typing Sort Prop.
Combined Scheme typing_conversion__mutind from typing__mut, conversion__mut, ctx_typing__mut.


Scheme typing'__mut := Induction for typing' Sort Prop
with conversion'__mut := Induction for conversion' Sort Prop
with ctx_typing'__mut := Induction for ctx_typing' Sort Prop.
Combined Scheme typing_conversion__mutind' from typing'__mut, conversion'__mut, ctx_typing'__mut.


Theorem ty_to_ty' : 
    (forall Γ l t A, Γ ⊢< l > t : A -> Squash (Γ ⊢'< l > t : A)) /\ 
    (forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> Squash (Γ ⊢'< l > t ≡ u : A)) /\ 
    (forall Γ, ⊢ Γ -> Squash (⊢' Γ)).
Proof.
    eapply typing_conversion__mutind; intros;
    try inversion H4; try inversion H3; 
    try inversion H2; try inversion H1; 
    try inversion H0; try inversion H; 
    eauto using sq, typing', conversion', ctx_typing'.
Qed.

Theorem ty'_to_ty : 
    (forall Γ l t A, Γ ⊢'< l > t : A -> Γ ⊢< l > t : A) /\ 
    (forall Γ l t u A, Γ ⊢'< l > t ≡ u : A -> Γ ⊢< l > t ≡ u : A) /\ 
    (forall Γ, ⊢' Γ -> ⊢ Γ).
Proof.
    eapply typing_conversion__mutind' ; intros; eauto using typing, conversion, ctx_typing.
Qed.


Record totalspace := 
{
    _Γ : ctx  ;
    _l : level ; 
    _t : term ; 
    _u : term ;
    _A : term ;
    deriv : _Γ ⊢'< _l > _t ≡ _u : _A
}.

Arguments Build_totalspace {_} {_} {_} {_} {_}.

Definition well v (X : totalspace * nat) := 
    let Ξ := fst X in 
    let k := snd X in
    _Γ Ξ = ∙ /\ 
    _l Ξ = ty 0 /\ 
    _t Ξ = v /\ 
    _u Ξ = mk_Nat k /\ 
    _A Ξ = Nat.

Axiom delta01 :
    forall
        (P : nat -> Prop) 
        (Pdec: forall n, sum (P n) (not (P n)))
        (ex : exists k, P k), 
            (sig (fun k => P k)).

(* TODO: show that total_space is in bijection with nat *)
Axiom f : nat -> totalspace * nat.
Axiom g : totalspace * nat -> nat.

Axiom gf_id : forall x, f (g x) = x.

(* and that well is decidable *)
Axiom well_dec : forall v X, sum (well v X) (not (well v X)).

(* Question: can we derive the above automatically using some Rocq command? *)

Lemma canonicity_prop_to_ty v :
    (exists k, ∙ ⊢< ty 0 > v ≡ (mk_Nat k) : Nat) ->
    @sig nat (fun k => ∙ ⊢< ty 0 > v ≡ (mk_Nat k) : Nat).
Proof.
    intros. 
    pose (P := fun n => well v (f n)).
    assert (exists n, well v n).
    { destruct H.
      eapply ty_to_ty' in H. inversion H.  
      exists ((Build_totalspace H0), x).
      unfold well. 
      split. reflexivity.  
      split. reflexivity.
      split. reflexivity.
      split. reflexivity. reflexivity. }
    assert (forall n, sum (P n) (not (P n))).
    { intros. destruct (well_dec v (f n)).
      left. eauto. right. eauto. }
    assert (exists k, P k).
    { destruct H0. exists (g x). unfold P. rewrite gf_id. eauto. }
    eapply delta01 in H2; eauto.
    destruct H2. 
    destruct p as (eq1 & eq2 & eq3 & eq4 & eq5).
    exists (snd (f x)).
    pose (H' := deriv (fst (f x))).
    rewrite eq1, eq2, eq3, eq4, eq5 in H'. 
    eapply ty'_to_ty. eauto.
Defined.

Corollary canonicity_ty : 
    forall t,
    ∙ ⊢< ty 0 > t : Nat -> 
    sig (fun k => ∙ ⊢< ty 0 > t ≡ (mk_Nat k) : Nat).
Proof.
    intros. eapply canonicity_conv in H. 
    eapply canonicity_prop_to_ty in H.
    eauto.
Defined.
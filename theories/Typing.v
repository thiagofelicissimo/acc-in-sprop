(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Weakenings. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Definition ax (l : level) :=
  match l with 
  | prop => 0
  | ty i => S i
  end.

Definition ru l j := 
    match l with 
    | prop => j 
    | ty i => max i j 
    end.



Definition Ax (l : level) : level :=
  ty (ax l).

Definition Ru (l1 l2 : level) : level := 
  match l2 with 
  | prop => prop 
  | ty j => ty (ru l1 j)
  end.


Reserved Notation "Γ ⊢< l > t : T" (at level 50, l, t, T at next level).
Reserved Notation "Γ ⊢< l > t ≡ u : T" (at level 50, l, t, u, T at next level).
Reserved Notation "⊢ Γ" (at level 50).


(* see AccInv.v for a justification of this axiom *)
Axiom accinv : level -> term -> term -> term -> term -> term -> term -> term.

Inductive typing : ctx -> level -> term → term → Prop :=

| type_var :
    ∀ Γ x l A,
      ⊢ Γ -> 
      nth_error Γ x = Some (l , A) →
      (Γ ⊢< l > (var x) : ((plus (S x)) ⋅ A))

| type_sort :
    ∀ Γ l,
      ⊢ Γ -> 
      Γ ⊢< Ax (Ax l) > Sort l : Sort (Ax l)

| type_pi :
    ∀ Γ i j A B,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j)


| type_lam :
    ∀ Γ i j A B t,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< Ru i j > lam i j A B t : Pi i j A B

| type_app :
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ru i j > t : Pi i j A B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B  t u : B <[ u .. ] 

| type_nat :
    ∀ Γ,
      ⊢ Γ -> 
      Γ ⊢< ty 1 > Nat : Sort (ty 0)

| type_zero : 
    ∀ Γ,
      ⊢ Γ -> 
      Γ ⊢< ty 0 > zero : Nat

| type_succ : 
    ∀ Γ t, 
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< ty 0 > succ t : Nat

| type_rec : 
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t : P <[ t .. ]

| type_acc : 
    ∀ Γ i A R a,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop -> 
    Γ ⊢< i > a : A -> 
    Γ ⊢< Ax prop > acc i A R a : Sort prop

| type_accin : 
    ∀ Γ i A R a p,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop -> 
    Γ ⊢< i > a : A -> 
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc i A_wk R_wk (var 1)  in
    let R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ⊢< prop > p : Pi i prop A (Pi prop prop R' acc_wk) ->
    Γ ⊢< prop > accin i A R a p : acc i A R a
  
| type_accel : 
    ∀ Γ i l A R a q P p,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop -> 
    Γ ,, (i, A) ⊢< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< prop > q : acc i A R a -> 
    Γ ⊢< l > accel i l A R P p a q : P <[a ..]

| type_conv : 
    ∀ Γ l A B t,
      Γ ⊢< l > t : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t : B

with ctx_typing : ctx -> Prop :=
| ctx_nil : 
      ⊢ ∙

| ctx_cons : 
    ∀ Γ l A, 
      ⊢ Γ -> 
      Γ ⊢< Ax l > A : Sort l ->
      ⊢ (Γ ,, (l , A))

with conversion : ctx -> level -> term -> term -> term -> Prop :=


| conv_var :
    ∀ Γ x l A,
      nth_error Γ x = Some (l , A) →
      ⊢ Γ -> 
      (Γ ⊢< l > (var x) ≡ (var x) : ((plus (S x)) ⋅ A))

| conv_sort :
    ∀ Γ l,
      ⊢ Γ ->
      Γ ⊢< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l)

| conv_pi :
    ∀ Γ i j A B A' B',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ Pi i j A' B' : Sort (Ru i j)

| conv_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≡ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≡ lam i j A' B' t' : Pi i j A B

| conv_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ≡ t' : Pi i j A B →
      Γ ⊢< i > u ≡ u' : A →
      Γ ⊢< j > app i j A B t u ≡ app i j A' B' t' u' : B <[ u .. ] 

| conv_nat :
    ∀ Γ,
      ⊢ Γ ->
      Γ ⊢< ty 1 > Nat ≡ Nat : Sort (ty 0)

| conv_zero : 
    ∀ Γ,
      ⊢ Γ ->
      Γ ⊢< ty 0 > zero ≡ zero : Nat

| conv_succ : 
    ∀ Γ t t', 
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< ty 0 > succ t ≡ succ t' : Nat

| conv_rec : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ≡ P' : Sort l ->
      Γ ⊢< l > p_zero ≡ p_zero' : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ≡ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ≡ rec l P' p_zero' p_succ' t' : P <[ t .. ]


| conv_acc : 
    ∀ Γ i A A' R R' a a',
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop -> 
    Γ ⊢< i > a ≡ a' : A -> 
    Γ ⊢< Ax prop > acc i A R a ≡ acc i A' R' a' : Sort prop

| conv_accin : 
    ∀ Γ i A A' R R' a a' p p',
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop -> 
    Γ ⊢< i > a ≡ a' : A -> 
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc i A_wk R_wk (var 1)  in
    let R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ⊢< prop > p ≡ p' : Pi i prop A (Pi prop prop R' acc_wk) ->
    Γ ⊢< prop > accin i A R a p ≡ accin i A' R' a' p' : acc i A R a
  
| conv_accel : 
    ∀ Γ i l A A' R R' a a' q q' P P' p p',
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop -> 
    Γ ,, (i, A) ⊢< Ax l > P ≡ P' : Sort l ->
    let R_ := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P_ := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p ≡ p' : P'' ->
    Γ ⊢< i > a ≡ a': A -> 
    Γ ⊢< prop > q ≡ q' : acc i A R a -> 
    Γ ⊢< l > accel i l A R P p a q ≡ accel i l A' R' P' p' a' q' : P <[a ..]
  
| conv_conv : 
    ∀ Γ l A B t t',
      Γ ⊢< l > t ≡ t' : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ≡ t' : B

| conv_irrel : 
    ∀ Γ A t t',
      Γ ⊢< prop > t : A -> 
      Γ ⊢< prop > t' : A ->
      Γ ⊢< prop > t ≡ t' : A

| conv_beta : 
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B (lam i j A B t) u ≡ t <[ u .. ] : B <[ u .. ] 

| conv_eta :
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ru i j > t : Pi i j A B →
      Γ ⊢< Ru i j > u : Pi i j A B →
      let t_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B) (S ⋅ t) (var 0) in 
      let u_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B) (S ⋅ u) (var 0) in 
      Γ ,, (i , A) ⊢< j > t_app_x ≡ u_app_x : B →
      Γ ⊢< Ru i j > t ≡ u : Pi i j A B

| conv_rec_zero : 
    ∀ Γ l P p_zero p_succ,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< l > rec l P p_zero p_succ zero ≡ p_zero : P <[ zero .. ]

| conv_rec_succ : 
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ (succ t) ≡ 
          p_succ <[(rec l P p_zero p_succ t) .: t ..] : P <[ (succ t) .. ]

| conv_accel_accin : 
    ∀ Γ i l A R a q P p,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop -> 
    Γ ,, (i, A) ⊢< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< prop > q : acc i A R a -> 
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
    Γ ⊢< l > accel i l A R P p a q ≡ p <[ t5 .: a ..] : P <[a ..]

| conv_sym : 
    ∀ Γ l t u A,
      Γ ⊢< l > t ≡ u : A ->
      Γ ⊢< l > u ≡ t : A
  
| conv_trans : 
    ∀ Γ l t u v A,
      Γ ⊢< l > t ≡ u : A ->
      Γ ⊢< l > u ≡ v : A ->
      Γ ⊢< l > t ≡ v : A

where "Γ ⊢< l > t : A" := (typing Γ l t A)
and   "⊢ Γ" := (ctx_typing Γ)
and   "Γ ⊢< l > t ≡ u : A" := (conversion Γ l t u A).

Scheme typing_mut := Induction for typing Sort Prop
with conversion_mut := Induction for conversion Sort Prop.
Combined Scheme typing_conversion_mutind from typing_mut, conversion_mut.


(* see AccInv.v for a justification of this axiom *)
Axiom type_accinv :
    ∀ Γ i A R a p b r,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop -> 
    Γ ⊢< i > a : A -> 
    Γ ⊢< prop > p : acc i A R a -> 
    Γ ⊢< i > b : A -> 
    Γ ⊢< prop > r : R <[a.:b..] -> 
    Γ ⊢< prop > accinv i A R a p b r : acc i A R b.

Axiom accinv_subst : forall i A R a p b r σ,
  (accinv i A R a p b r) <[ σ ] = accinv i (A <[σ]) (R<[var 0 .: (var 1 .: σ >> (ren_term (S >> S)))]) (a<[σ]) (p<[σ]) (b<[σ]) (r<[σ]).

Reserved Notation "Γ ⊢s σ : Δ" (at level 50, σ, Δ at next level).

Reserved Notation "Γ ⊢s σ ≡ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive WellSubst (Γ : ctx) : ctx -> (nat -> term) -> Prop :=
  | well_sempty (σ : nat -> term) : 
    Γ ⊢s σ : ∙
  | well_scons (σ : nat -> term) (Δ : ctx) l (A : term) :
    Γ ⊢s (↑ >> σ) : Δ ->
    Γ ⊢< l > σ var_zero : A <[↑ >> σ] ->
    Γ ⊢s σ : (Δ ,, (l , A)) 
where "Γ ⊢s σ : Δ" := (WellSubst Γ Δ σ).

Inductive ConvSubst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
| conv_sempty (σ τ : nat -> term) : Γ ⊢s σ ≡ τ : ∙
| conv_scons (σ τ : nat -> term) (Δ : ctx) l A :
  Γ ⊢s (↑ >> σ) ≡ (↑ >> τ) : Δ -> 
  Γ ⊢< l > σ var_zero ≡ τ var_zero: A <[↑ >> σ] ->
  Γ ⊢s σ ≡ τ : Δ ,, (l , A)
where "Γ ⊢s σ ≡ τ : Δ" := (ConvSubst Γ Δ σ τ).

Reserved Notation "⊢ Γ ≡ Δ" (at level 50, Δ at next level).

Inductive ConvCtx : ctx -> ctx -> Type :=
| conv_cempty : ⊢ ∙ ≡ ∙
| conv_ccons Γ A Δ B l : 
  ⊢ Γ ≡ Δ -> 
  Γ ⊢< Ax l > A ≡ B : Sort l -> 
  ⊢ (Γ ,, ( l , A)) ≡ (Δ ,, (l , B))
where "⊢ Γ ≡ Δ" := (ConvCtx Γ Δ).

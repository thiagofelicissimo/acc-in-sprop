(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Parameter assm_sig : list term.

Reserved Notation "Γ ∋< l > x : T" (at level 50, l, x, T at next level).
Reserved Notation "Γ ⊢< l > t : T" (at level 50, l, t, T at next level).
Reserved Notation "Γ ⊢< l > t ≡ u : T" (at level 50, l, t, u, T at next level).
Reserved Notation "⊢ Γ" (at level 50).

Inductive varty : ctx → nat → level → term → Prop :=
| vartyO Γ l A : Γ ,, (l , A) ∋< l > 0 : S ⋅ A
| vartyS Γ i j A B x : Γ ∋< i > x : A → Γ ,, (j, B) ∋< i > S x : S ⋅ A

where "Γ ∋< l > x : T" := (varty Γ x l T).

Inductive typing : ctx -> level -> term → term → Prop :=

| type_var :
    ∀ Γ x l A,
      ⊢ Γ ->
      Γ ∋< l > x : A →
      Γ ⊢< l > (var x) : A

| type_sort :
    ∀ Γ l,
      ⊢ Γ ->
      Γ ⊢< Ax (Ax l) > Sort l : Sort (Ax l)

| type_assm :
    ∀ Γ c A,
      ⊢ Γ ->
      nth_error assm_sig c = Some A ->
      ∙ ⊢< Ax prop > A : Sort prop ->
      Γ ⊢< prop > assm c : A

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
      Γ ⊢< j > app i j A B t u : B <[ u .. ]

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
    ∀ Γ n A R a,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ⊢< ty n > a : A ->
    Γ ⊢< Ax prop > acc (ty n) A R a : Sort prop

| type_accin :
    ∀ Γ n A R a p,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ⊢< ty n > a : A ->
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc (ty n) A_wk R_wk (var 1)  in
    let R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ⊢< prop > p : Pi (ty n) prop A (Pi prop prop R' acc_wk) ->
    Γ ⊢< prop > accin (ty n) A R a p : acc (ty n) A R a

| type_accinv :
    ∀ Γ n A R a p b r,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ⊢< ty n > a : A ->
    Γ ⊢< prop > p : acc (ty n) A R a ->
    Γ ⊢< ty n > b : A ->
    Γ ⊢< prop > r : R <[a.:b..] ->
    Γ ⊢< prop > accinv (ty n) A R a p b r : acc (ty n) A R b

| type_accel :
    ∀ Γ n l A R a q P p,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ⊢< Ax l > P : Sort l ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ⊢< l > p : P'' ->
    Γ ⊢< ty n > a : A ->
    Γ ⊢< prop > q : acc (ty n) A R a ->
    Γ ⊢< l > accel (ty n) l A R P p a q : P <[a ..]

| type_accelcomp :
    ∀ Γ n m A R a q P p,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ⊢< Ax (ty m) > P : Sort (ty m) ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ⊢< ty m > p : P'' ->
    Γ ⊢< ty n > a : A ->
    Γ ⊢< prop > q : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop (ty m) t2 P'' t1 in
    let t4 := Pi prop (ty m) t2 P'' in
    let t5 := lam (ty n) (ty m) A t4 t3 in
    Γ ⊢< prop > accelcomp (ty n) (ty m) A R P p a q : obseq (ty m) (P <[a ..]) (accel (ty n) (ty m) A R P p a q) (p <[ t5 .: a ..])

| type_obseq :
    ∀ Γ n A a b,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ⊢< ty n > a : A ->
    Γ ⊢< ty n > b : A ->
    Γ ⊢< Ax prop > obseq (ty n) A a b : Sort prop

| type_obsrefl :
    ∀ n Γ A a,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ⊢< ty n > a : A ->
      Γ ⊢< prop > obsrefl (ty n) A a : obseq (ty n) A a a

| type_J :
    ∀ Γ n A a P p b e,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ⊢< ty n > a : A ->
      Γ ,, (ty n , A) ⊢< Ax prop > P : Sort prop ->
      Γ ⊢< prop > p : P <[a..] ->
      Γ ⊢< ty n > b : A ->
      Γ ⊢< prop > e : obseq (ty n) A a b ->
      Γ ⊢< prop > J (ty n) A a P p b e : P <[b..]

| type_cast :
  ∀ Γ i A B e a,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ⊢< Ax i > B : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A ->
    Γ ⊢< i > cast i A B e a : B

| type_injpi1 :
  ∀ Γ i n A1 A2 B1 B2 e,
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e : obseq (Ax i) (Sort i) A2 A1

| type_injpi2 :
  ∀ Γ i n A1 A2 B1 B2 e a2,
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > a2 : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 : obseq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..])

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
      Γ ∋< l > x : A →
      ⊢ Γ ->
      Γ ⊢< l > var x ≡ var x : A

| conv_sort :
    ∀ Γ l,
      ⊢ Γ ->
      Γ ⊢< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l)

| conv_assm :
    ∀ Γ c A,
      ⊢ Γ ->
      nth_error assm_sig c = Some A ->
      ∙ ⊢< Ax prop > A : Sort prop ->
      Γ ⊢< prop > assm c ≡ assm c : A


| conv_pi :
    ∀ Γ i j A B A' B',
      Γ ⊢< Ax i > A : Sort i →
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ Pi i j A' B' : Sort (Ru i j)

| conv_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢< Ax i > A : Sort i →
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≡ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≡ lam i j A' B' t' : Pi i j A B

| conv_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ⊢< Ax i > A : Sort i →
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
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ≡ P' : Sort l ->
      Γ ⊢< l > p_zero ≡ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ≡ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ≡ rec l P' p_zero' p_succ' t' : P <[ t .. ]


| conv_acc :
    ∀ Γ n A A' R R' a a',
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< Ax prop > acc (ty n) A R a ≡ acc (ty n) A' R' a' : Sort prop

| conv_accin :
    ∀ Γ n A A' R R' a a' p p',
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ⊢< ty n > a ≡ a' : A ->
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc (ty n) A_wk R_wk (var 1)  in
    let RR := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ⊢< prop > p ≡ p' : Pi (ty n) prop A (Pi prop prop RR acc_wk) ->
    Γ ⊢< prop > accin (ty n) A R a p ≡ accin (ty n) A' R' a' p' : acc (ty n) A R a

| conv_accinv :
    ∀ Γ n A A' R R' a a' p p' b b' r r',
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< prop > p ≡ p' : acc (ty n) A R a ->
    Γ ⊢< ty n > b ≡ b' : A ->
    Γ ⊢< prop > r ≡ r' : R <[a.:b..] ->
    Γ ⊢< prop > accinv (ty n) A R a p b r ≡ accinv (ty n) A' R' a' p' b' r' : acc (ty n) A R b

| conv_accel :
    ∀ Γ n l A A' R R' a a' q q' P P' p p',
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ,, (ty n, A) ⊢< Ax l > P : Sort l ->
    Γ ,, (ty n, A) ⊢< Ax l > P ≡ P' : Sort l ->
    let R_ := (1 .: (0 .: (S >> S))) ⋅ R in
    let P_ := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ⊢< l > p ≡ p' : P'' ->
    Γ ⊢< ty n > a ≡ a': A ->
    Γ ⊢< prop > q ≡ q' : acc (ty n) A R a ->
    Γ ⊢< l > accel (ty n) l A R P p a q ≡ accel (ty n) l A' R' P' p' a' q' : P <[a ..]


| conv_obseq :
    ∀ Γ n A A' a a' b b',
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< ty n > b ≡ b' : A ->
    Γ ⊢< Ax prop > obseq (ty n) A a b ≡ obseq (ty n) A' a' b' : Sort prop

| conv_obsrefl :
  ∀ n Γ A A' a a',
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< prop > obsrefl (ty n) A a ≡ obsrefl (ty n) A' a' : obseq (ty n) A a a

| conv_J :
    ∀ Γ n A A' a a' P P' p p' b b' e e',
      Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
      Γ ⊢< ty n > a ≡ a' : A ->
      Γ ,, (ty n , A) ⊢< Ax prop > P ≡ P' : Sort prop ->
      Γ ⊢< prop > p ≡ p' : P <[a..] ->
      Γ ⊢< ty n > b ≡ b' : A ->
      Γ ⊢< prop > e ≡ e' : obseq (ty n) A a b ->
      Γ ⊢< prop > J (ty n) A a P p b e ≡ J (ty n) A' a' P' p' b' e' : P <[b..]

| conv_cast :
  ∀ Γ i A A' B B' e e' a a',
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ⊢< Ax i > B ≡ B' : Sort i ->
    Γ ⊢< prop > e ≡ e' : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a ≡ a' : A ->
    Γ ⊢< i > cast i A B e a ≡ cast i A' B' e' a' : B

| conv_injpi1 :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e',
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ≡ e' : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e ≡ injpi1 i (ty n) A1' A2' B1' B2' e' : obseq (Ax i) (Sort i) A2 A1

| conv_injpi2 :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2',
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ≡ e' : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > a2 ≡ a2' : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 ≡ injpi2 i (ty n) A1' A2' B1' B2' e' a2' : obseq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..])

| conv_accelcomp :
    ∀ Γ n m A R a q P p A' R' a' q' P' p',
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ⊢< Ax (ty m) > P : Sort (ty m) ->
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ,, (ty n, A) ⊢< Ax (ty m) > P ≡ P' : Sort (ty m) ->
    let R_ := (1 .: (0 .: (S >> S))) ⋅ R in
    let P_ := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R_ P_) in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ⊢< (ty m) > p ≡ p' : P'' ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< prop > q ≡ q' : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop (ty m) t2 P'' t1 in
    let t4 := Pi prop (ty m) t2 P'' in
    let t5 := lam (ty n) (ty m) A t4 t3 in
    Γ ⊢< prop > accelcomp (ty n) (ty m) A R P p a q ≡ accelcomp (ty n) (ty m) A' R' P' p' a' q'
      : obseq (ty m) (P <[a ..]) (accel (ty n) (ty m) A R P p a q) (p <[ t5 .: a ..])

| conv_cast_refl :
    ∀ Γ i A e a,
      Γ ⊢< prop > e : obseq (Ax i) (Sort i) A A ->
      Γ ⊢< Ax i > A : Sort i ->
      Γ ⊢< i > a : A ->
      Γ ⊢< i > cast i A A e a ≡ a : A

| conv_cast_pi :
  ∀ Γ i n A1 A2 B1 B2 e f,
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< Ru i (ty n) > f : Pi i (ty n) A1 B1 ->
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let B1' := (up_ren S) ⋅ B1 in
    let B2' := (up_ren S) ⋅ B2 in
    let t1 := cast i A2' A1' (injpi1 i (ty n) A1' A2' B1' B2' (S ⋅ e)) (var 0) in
    let t2 := app i (ty n) A1' B1' (S ⋅ f) t1 in
    let t3 := cast (ty n) (B1 <[t1.: S >> var]) B2 (injpi2 i (ty n) A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in
    let t4 := lam i (ty n) A2 B2 t3 in
    Γ ⊢< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f ≡ t4 : Pi i (ty n) A2 B2


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
Combined Scheme typing_mutind from typing_mut, conversion_mut.

Reserved Notation "Γ ⊢r ρ : Δ" (at level 50, ρ, Δ at next level).

Inductive WellRen (Γ : ctx) (ρ : nat → nat) : ctx → Prop :=
| well_rempty : Γ ⊢r ρ : ∙
| well_rcons Δ l A :
  Γ ⊢r (↑ >> ρ) : Δ →
  Γ ∋< l > ρ 0 : (S >> ρ) ⋅ A →
  Γ ⊢r ρ : Δ ,, (l , A)
where "Γ ⊢r ρ : Δ" := (WellRen Γ ρ Δ).

Reserved Notation "Γ ⊢s σ : Δ" (at level 50, σ, Δ at next level).

Reserved Notation "Γ ⊢s σ ≡ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive WellSubst (Γ : ctx) : ctx -> (nat -> term) -> Prop :=
| well_sempty (σ : nat -> term) :
  Γ ⊢s σ : ∙
| well_scons (σ : nat -> term) (Δ : ctx) l (A : term) :
  Γ ⊢s (↑ >> σ) : Δ ->
  Γ ⊢< l > σ 0 : A <[↑ >> σ] ->
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

Inductive ConvCtx : ctx -> ctx -> Prop :=
| conv_cempty : ⊢ ∙ ≡ ∙
| conv_ccons Γ A Δ B l :
  ⊢ Γ ≡ Δ ->
  Γ ⊢< Ax l > A ≡ B : Sort l ->
  ⊢ (Γ ,, ( l , A)) ≡ (Δ ,, (l , B))
where "⊢ Γ ≡ Δ" := (ConvCtx Γ Δ).

(* Scoping *)

Fixpoint scoped n t :=
  match t with
  | var m => m <? n
  | Sort _ => true
  | assm c => true
  | Pi i j A B => scoped n A && scoped (S n) B
  | lam i j A B t => scoped n A && scoped (S n) B && scoped (S n) t
  | app i j A B u v => scoped n A && scoped (S n) B && scoped n u && scoped n v
  | Nat => true
  | zero => true
  | succ k => scoped n k
  | rec _ P pz ps t =>
    scoped (S n) P && scoped n pz && scoped (S (S n)) ps && scoped n t
  | acc _ A R a => scoped n A && scoped (S (S n)) R && scoped n a
  | accin i A R a p  =>
    scoped n A && scoped (S (S n)) R && scoped n a && scoped n p
  | accinv i A R a p b r =>
    scoped n A && scoped (S (S n)) R && scoped n a && scoped n p &&
    scoped n b && scoped n r
  | accel _ _ A R a q P p =>
    scoped n A && scoped (S (S n)) R && scoped (S n) a && scoped (S ( S n)) q &&
    scoped n P && scoped n p
  | accelcomp _ _ A R a q P p =>
    scoped n A && scoped (S (S n)) R && scoped (S n) a && scoped (S ( S n)) q &&
    scoped n P && scoped n p
  | obseq _ A a b => scoped n A && scoped n a && scoped n b
  | obsrefl l A a => scoped n A && scoped n a
  | J l A a P p b e =>
    scoped n A && scoped n a && scoped (S n) P && scoped n p && scoped n b &&
    scoped n e
  | cast _ A B e t => scoped n A && scoped n B && scoped n e && scoped n t
  | injpi1 i j A1 A2 B1 B2 e =>
    scoped n A1 && scoped n A2 && scoped (S n) B1 && scoped (S n) B2 &&
    scoped n e
  | injpi2 i j A1 A2 B1 B2 e a2 =>
    scoped n A1 && scoped n A2 && scoped (S n) B1 && scoped (S n) B2 &&
    scoped n e && scoped n a2
  end.

Notation closed t := (scoped 0 t).

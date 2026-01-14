From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Contexts Typing TypingP BasicMetaTheory BasicMetaTheoryP TypeUniquenessP.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.


(* the following axioms are justified in the file HEq.v *)

Axiom heq : level -> term -> term -> term -> term -> term.

Axiom heq_ren : forall ρ l A B a e,
  ρ ⋅ (heq l A B a e) = heq l (ρ ⋅ A) (ρ ⋅ B) (ρ ⋅ a) (ρ ⋅ e).

Axiom heq_subst : forall σ l A B a e,
  (heq l A B a e)<[σ] = heq l (A<[σ]) (B<[σ]) (a<[σ]) (e<[σ]).

Axiom type_heq : forall Γ l A B a b,
  Γ ⊢< Ax l > A : Sort l →
  Γ ⊢< Ax l > B : Sort l →
  Γ ⊢< l > a : A →
  Γ ⊢< l > b : B →
  Γ ⊢< ty 0 > heq l A B a b : Sort prop.

Axiom conv_heq : forall Γ l A B a b A' B' a' b',
  Γ ⊢< Ax l > A ≡ A' : Sort l →
  Γ ⊢< Ax l > B ≡ B' : Sort l →
  Γ ⊢< l > a ≡ a' : A →
  Γ ⊢< l > b ≡ b' : B →
  Γ ⊢< ty 0 > heq l A B a b ≡ heq l A' B' a' b' : Sort prop.


Axiom heq_refl : level -> term -> term -> term.

Axiom ren_heq_refl : forall ρ l A a, ρ ⋅ (heq_refl l A a) = heq_refl l (ρ ⋅ A) (ρ ⋅ a).
(* Axiom subst_heq_refl : forall σ l A a, (heq_refl l A a) <[ σ ] = heq_refl l (A<[σ]) (a<[σ]). *)

Axiom type_heq_refl : forall Γ l A a,
  Γ ⊢< Ax l > A : Sort l →
  Γ ⊢< l > a : A →
  Γ ⊢< prop > heq_refl l A a : heq l A A a a.



(* because heq at l = prop is True, we also have the following *)
Axiom true : term.
Axiom type_true_heq : forall Γ A B a b,
  Γ ⊢< Ax prop > A : Sort prop →
  Γ ⊢< Ax prop > B : Sort prop →
  Γ ⊢< prop > a : A →
  Γ ⊢< prop > b : B →
  Γ ⊢< prop > true : heq prop A B a b.


Axiom heq_pi : level -> level -> term -> term -> term -> term -> term -> term -> term.

Axiom type_heq_pi : forall Γ i j A1 A2 B1 B2 p q,
  Γ ⊢< Ax i > A1 : Sort i ->
  Γ ⊢< Ax i > A2 : Sort i ->
  Γ ,, (i, A1) ⊢< Ax j > B1 : Sort j ->
  Γ ,, (i, A2) ⊢< Ax j > B2 : Sort j ->
  Γ ⊢< prop > p : heq (Ax i) (Sort i) (Sort i) A1 A2 ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq)
    ⊢< prop > q : heq (Ax j) (Sort j) (Sort j) ((S >> S) ⋅ B1) ((up_ren S >> S) ⋅ B2) -> 
  Γ ⊢< prop > heq_pi i j A1 A2 B1 B2 p q 
    : heq (Ax (Ru i j)) (Sort (Ru i j)) (Sort (Ru i j)) (Pi i j A1 B1) (Pi i j A2 B2).

Axiom heq_lam : level -> level -> term -> term -> term -> term -> term -> term -> term -> term -> term.

Axiom type_heq_lam : forall Γ i j A1 A2 B1 B2 t1 t2 p q,
  Γ ,, (i, A1) ⊢< j > t1 : B1 ->
  Γ ,, (i, A2) ⊢< j > t2 : B2 ->
  Γ ⊢< prop > p : heq (Ax i) (Sort i) (Sort i) A1 A2 ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq)
    ⊢< prop > q : heq j ((S >> S) ⋅ B1) ((up_ren S >> S) ⋅ B2) ((S >> S) ⋅ t1) ((up_ren S >> S) ⋅ t2) -> 
  Γ ⊢< prop > heq_lam i j A1 A2 B1 B2 t1 t2 p q 
    : heq (Ru i j) (Pi i j A1 B1) (Pi i j A2 B2) (lam i j A1 B1 t1) (lam i j A2 B2 t2).


Axiom heq_app : level -> level -> term -> term -> term -> term -> term -> term -> term -> term -> term -> term -> term.

Axiom type_heq_app : forall Γ i j A1 A2 B1 B2 f1 f2 a1 a2 p q,
  Γ ⊢< Ru i j > f1 : Pi i j A1 B1 ->
  Γ ⊢< Ru i j > f2 : Pi i j A2 B2 ->
  Γ ⊢< i > a1 : A1 ->
  Γ ⊢< i > a2 : A2 ->
  Γ ⊢< prop > p : heq (Ru i j) (Pi i j A1 B1) (Pi i j A2 B2) f1 f2 -> 
  Γ ⊢< prop > q : heq i A1 A2 a1 a2 ->
  Γ ⊢< prop > heq_app i j A1 A2 B1 B2 f1 f2 a1 a2 p q 
    : heq j (B1 <[a1..]) (B2 <[a2..]) (app i j A1 B1 f1 a1) (app i j A2 B2 f2 a2).


Axiom heq_succ : term -> term -> term -> term.

Axiom type_heq_succ : forall Γ t u e,
  Γ ⊢< ty 0 > t : Nat ->
  Γ ⊢< ty 0 > u : Nat ->
  Γ ⊢< prop > e: heq (ty 0) Nat Nat t u ->
  Γ ⊢< prop > heq_succ t u e : heq (ty 0) Nat Nat (succ t) (succ u).
    
Axiom heq_sym : level -> term -> term -> term -> term -> term -> term.

Axiom type_heq_sym : forall Γ l A B b a e,
  Γ ⊢< l > a : A ->
  Γ ⊢< l > b : B ->
  Γ ⊢< prop > e : heq l A B a b →
  Γ ⊢< prop > heq_sym l A B a b e : heq l B A b a.




Axiom heq_trans : level -> term -> term -> term -> term -> term -> term -> term -> term -> term.

Axiom type_heq_trans : forall Γ l A B C c b a e1 e2,
  Γ ⊢< l > a : A ->
  Γ ⊢< l > b : B ->
  Γ ⊢< l > c : C ->
  Γ ⊢< prop > e1 : heq l A B a b →
  Γ ⊢< prop > e2 : heq l B C b c → 
  Γ ⊢< prop > heq_trans l A B C a b c e1 e2 : heq l A C a c.


Axiom heq_cast : forall (i : level) (A B e a : term), term.

Axiom type_heq_cast : forall Γ l A B e a,
  Γ ⊢< Ax l > A : Sort l →
  Γ ⊢< Ax l > B : Sort l →
  Γ ⊢< prop > e : obseq (Ax l) (Sort l) A B →
  Γ ⊢< l > a : A →
  Γ ⊢< prop > heq_cast l A B e a : heq l A B a (cast l A B e a).

Axiom heq_rec : forall (l:level) (P1 P2 pzero1 pzero2 psucc1 psucc2 t1 t2 e1 e2 e3 e4:term), term.

Axiom type_heq_rec : forall l Γ P1 P2 pzero1 pzero2 psucc1 psucc2 t1 t2 e1 e2 e3 e4,
  Γ ,, (ty 0, Nat) ⊢< Ax l > P1 : Sort l ->
  Γ ,, (ty 0, Nat) ⊢< Ax l > P2 : Sort l ->
  Γ ⊢< l > pzero1 : P1 <[ zero .. ] ->
  Γ ,, (ty 0, Nat) ,, (l, P1) ⊢< l > psucc1 : P1 <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
  Γ ⊢< ty 0 > t1 : Nat ->
  Γ ⊢< l > pzero2 : P2 <[ zero .. ] ->
  Γ ,, (ty 0, Nat) ,, (l, P2) ⊢< l > psucc2 : P2 <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
  Γ ⊢< ty 0 > t2 : Nat ->
  let Aeq := heq (ty 0) Nat Nat (var 1) (var 0) in
  Γ ,, (ty 0, Nat) ,, (ty 0, Nat) ,, (prop, Aeq) ⊢< prop > e1 : heq (Ax l) (Sort l) (Sort l) ((S >> S) ⋅ P1) ((up_ren S >> S) ⋅ P2) ->
  Γ ⊢< prop > e2 : heq l (P1 <[ zero ..]) (P2 <[ zero..]) pzero1 pzero2 ->
  let Peq := heq l ((S >> S >> S >> S) ⋅ P1) ((up_ren S >> S >> S >> S) ⋅ P2) (var 1) (var 0) in
  Γ ,, (ty 0, Nat) ,, (ty 0, Nat) ,, (prop, Aeq) ,, (l, (S >> S) ⋅ P1) ,, (l, (up_ren S >> S >> S) ⋅ P2) ,, (prop, Peq) ⊢< prop > 
    e3 : heq l (((S >> S >> S >> S >> S) ⋅ (P1<[(succ (var 0)).: S >> var]))) (((up_ren S >> S >> S >> S >> S) ⋅ (P2<[(succ (var 0)).: S >> var])))
          ((up_ren (S >> S) >> S >> S) ⋅ psucc1) ((up_ren (up_ren S >> S >> S) >> S) ⋅ psucc2) ->
  Γ ⊢< prop > e4 : heq (ty 0) Nat Nat t1 t2 ->
  Γ ⊢< prop > heq_rec l P1 P2 pzero1 pzero2 psucc1 psucc2 t1 t2 e1 e2 e3 e4 : 
    heq l (P1<[t1..]) (P2<[t2..]) (rec l P1 pzero1 psucc1 t1) (rec l P2 pzero2 psucc2 t2).

Axiom heq_acc : forall (l : level) (A1 A2 R1 R2 a1 a2 e1 e2 : term), term.

Axiom type_heq_acc : forall Γ n A1 A2 R1 R2 a1 a2 e1 e2,
  Γ ,, (ty n, A1) ,, (ty n, S ⋅ A1) ⊢< Ax prop > R1 : Sort prop ->
  Γ ⊢< ty n > a1 : A1 ->
  Γ ,, (ty n, A2) ,, (ty n, S ⋅ A2) ⊢< Ax prop > R2 : Sort prop ->
  Γ ⊢< ty n > a2 : A2 ->
  let Aeq := heq (ty n) ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  let Aeq' := heq (ty n) ((S >> S >> S >> S >> S) ⋅ A1) ((S >> S >> S >> S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (ty n, A1) ,, (ty n, S ⋅ A2) ,, (prop, Aeq) 
    ,, (ty n, (S >> S >> S) ⋅ A1) ,, (ty n, (S >> S >> S >> S) ⋅ A2) ,, (prop, Aeq')
      ⊢< prop > e1 : heq (Ax prop) (Sort prop) (Sort prop) 
        ((up_ren (S >> S) >> S >> S) ⋅ R1) ((up_ren (up_ren S >> S >> S) >> S) ⋅ R2) ->
  Γ ⊢< prop > e2 : heq (ty n) A1 A2 a1 a2 ->
  Γ ⊢< prop > heq_acc (ty n) A1 A2 R1 R2 a1 a2 e1 e2 
    : heq (Ax prop) (Sort prop) (Sort prop) (acc (ty n) A1 R1 a1) (acc (ty n) A2 R2 a2).


Axiom heq_accel : forall (l l' : level) (A1 A2 R1 R2 P1 P2 p1 p2 q1 q2 a1 a2 e1 e2 e3 e4 : term), term.
    
Axiom type_heq_accel : forall Γ l n A1 A2 R1 R2 P1 P2 p1 p2 q1 q2 a1 a2 e1 e2 e3 e4,

  Γ ,, (ty n, A1) ⊢< Ax l > P1 : Sort l ->
  let R1' := (1 .: (0 .: (S >> S))) ⋅ R1 in
  let P1' := (1 .: (S >> S >> S)) ⋅ P1 in
  let B1 := Pi (ty n) l (S ⋅ A1) (Pi prop l R1' P1') in
  let P1'' := (1.: (S >> S)) ⋅ P1 in
  Γ ,, (ty n, A1) ,, (Ru (ty n) l, B1) ⊢< l > p1 : P1'' ->
  Γ ⊢< prop > q1 : acc (ty n) A1 R1 a1 ->

  Γ ,, (ty n, A2) ⊢< Ax l > P2 : Sort l ->
  let R2' := (1 .: (0 .: (S >> S))) ⋅ R2 in
  let P2' := (1 .: (S >> S >> S)) ⋅ P2 in
  let B2 := Pi (ty n) l (S ⋅ A2) (Pi prop l R2' P2') in
  let P2'' := (1.: (S >> S)) ⋅ P2 in
  Γ ,, (ty n, A2) ,, (Ru (ty n) l, B2) ⊢< l > p2 : P2'' ->
  Γ ⊢< prop > q2 : acc (ty n) A2 R2 a2 ->

  let Aeq := heq (ty n) ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  let Aeq' := heq (ty n) ((S >> S >> S >> S >> S) ⋅ A1) ((S >> S >> S >> S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (ty n, A1) ,, (ty n, S ⋅ A2) ,, (prop, Aeq) 
    ,, (ty n, (S >> S >> S) ⋅ A1) ,, (ty n, (S >> S >> S >> S) ⋅ A2) ,, (prop, Aeq')
      ⊢< prop > e1 : heq (Ax prop) (Sort prop) (Sort prop) 
        ((up_ren (S >> S) >> S >> S) ⋅ R1) ((up_ren (up_ren S >> S >> S) >> S) ⋅ R2) ->
  
  Γ ⊢< prop > e2 : heq (ty n) A1 A2 a1 a2 ->
  
  Γ ,, (ty n, A1) ,, (ty n, S ⋅ A2) ,, (prop, Aeq) ⊢< prop >
    e3 : heq (Ax l) (Sort l) (Sort l) ((S >> S) ⋅ P1) ((up_ren S >> S) ⋅ P2) ->

  let Beq := heq (Ru (ty n) l) ((S >> S >> S >> S) ⋅ B1) ((up_ren S >> S >> S >> S) ⋅ B2) (var 1) (var 0) in
  Γ ,, (ty n, A1) ,, (ty n, S ⋅ A2) ,, (prop, Aeq)
    ,, (Ru (ty n) l, (S >> S) ⋅ B1) ,, (Ru (ty n) l, (up_ren S >> S >> S) ⋅ B2) ,, (prop, Beq)
    ⊢< prop > e4 : heq l ((up_ren (S >> S) >> S >> S) ⋅ P1'') ((up_ren (up_ren S >> S >> S) >> S) ⋅ P2'') 
      ((up_ren (S >> S) >> S >> S) ⋅ p1) ((up_ren (up_ren S >> S >> S) >> S) ⋅ p2) ->

  Γ ⊢< prop > heq_accel (ty n) l A1 A2 R1 R2 P1 P2 p1 p2 a1 a2 q1 q2 e1 e2 e3 e4
    : heq l (P1 <[ a1..]) (P2 <[ a2..]) (accel (ty n) l A1 R1 P1 p1 a1 q1) (accel (ty n) l A2 R2 P2 p2 a2 q2).
  

Axiom heq_obseq : forall (l : level) (A1 A2 a1 a2 b1 b2 e1 e2 : term), term.

Axiom type_heq_obseq : forall Γ n A1 a1 b1 A2 a2 b2 e1 e2, 
  Γ ⊢< ty n > a1 : A1 ->
  Γ ⊢< ty n > b1 : A1 ->
  Γ ⊢< ty n > a2 : A2 ->
  Γ ⊢< ty n > b2 : A2 ->
  Γ ⊢< prop > e1 : heq (ty n) A1 A2 a1 a2 ->
  Γ ⊢< prop > e2 : heq (ty n) A1 A2 b1 b2 ->
  Γ ⊢< prop > heq_obseq (ty n) A1 A2 a1 a2 b1 b2 e1 e2 : heq (Ax prop) (Sort prop) (Sort prop) (obseq (ty n) A1 a1 b1) (obseq (ty n) A2 a2 b2).


Axiom hetero_to_homo : forall (l : level) (A t u e : term), term.

Axiom type_hetero_to_homo : forall n Γ t u A e,
  Γ ⊢< ty n > t : A ->
  Γ ⊢< ty n > u : A ->
  Γ ⊢< prop > e : heq (ty n) A A t u ->
  Γ ⊢< prop > hetero_to_homo (ty n) A t u e : obseq (ty n) A t u.


Reserved Notation " t ⊏ t' " (at level 21).

Inductive decoration : term → term → Prop :=
| dec_var x :
    var x ⊏ var x 

| dec_sort l :
    Sort l ⊏ Sort l 

| dec_assm c :
    assm c ⊏ assm c 

| dec_Pi i j A A' B B' :
    A ⊏ A' →
    B ⊏ B' →
    Pi i j A B ⊏ Pi i j A' B'

| dec_lam i j A A' B B' t t' :
    A ⊏ A' →
    B ⊏ B' →
    t ⊏ t' →
    lam i j A B t ⊏ lam i j A' B' t'

| dec_app i j A A' B B' t t' u u' :
    A ⊏ A' →
    B ⊏ B' →
    t ⊏ t' →
    u ⊏ u' →
    app i j A B t u ⊏ app i j A' B' t' u'

| dec_nat : 
    Nat ⊏ Nat 

| dec_zero :
    zero ⊏ zero

| dec_succ t t' :
    t ⊏ t' →
    succ t ⊏ succ t'

| dec_rec l P P' pz pz' ps ps' t t' :
    P ⊏ P' →
    pz ⊏ pz' →
    ps ⊏ ps' →
    t ⊏ t' →
    rec l P pz ps t ⊏ rec l P' pz' ps' t'

| dec_acc i A A' R R' a a' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    acc i A R a ⊏ acc i A' R' a'

| dec_accin i A A' R R' a a' p p' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    p ⊏ p' →
    accin i A R a p ⊏ accin i A' R' a' p'

| dec_accinv i A A' R R' a a' p p' b b' r r' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    p ⊏ p' →
    b ⊏ b' →
    r ⊏ r' →
    accinv i A R a p b r ⊏ accinv i A' R' a' p' b' r'

| dec_accel i l A A' R R' P P' p p' a a' q q' :
    A ⊏ A' →
    R ⊏ R' →
    P ⊏ P' →
    p ⊏ p' →
    a ⊏ a' →
    q ⊏ q' →
    accel i l A R P p a q ⊏ accel i l A' R' P' p' a' q'

| dec_obseq i A A' a a' b b' :
    A ⊏ A' →
    a ⊏ a' →
    b ⊏ b' →
    obseq i A a b ⊏ obseq i A' a' b'

| dec_obsrefl i A A' a a' :
    A ⊏ A' →
    a ⊏ a' →
    obsrefl i A a ⊏ obsrefl i A' a'

| dec_J i A A' a a' P P' p p' b b' e e' :
    A ⊏ A' →
    a ⊏ a' →
    P ⊏ P' →
    p ⊏ p' →
    b ⊏ b' →
    e ⊏ e' →
    J i A a P p b e ⊏ J i A' a' P' p' b' e'

| dec_cast i A A' B B' e e' a a' :
    A ⊏ A' →
    B ⊏ B' →
    e ⊏ e' →
    a ⊏ a' →
    cast i A B e a ⊏ cast i A' B' e' a'

| dec_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ⊏ A1' →
    A2 ⊏ A2' →
    B1 ⊏ B1' →
    B2 ⊏ B2' →
    e ⊏ e' →
    injpi1 i j A1 A2 B1 B2 e ⊏ injpi1 i j A1' A2' B1' B2' e'

| dec_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ⊏ A1' →
    A2 ⊏ A2' →
    B1 ⊏ B1' →
    B2 ⊏ B2' →
    e ⊏ e' →
    a2 ⊏ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ⊏ injpi2 i j A1' A2' B1' B2' e' a2'

(* | dec_refl u :
    u ⊏ u

| dec_trans u v w :
    u ⊏ v →
    v ⊏ w →
    u ⊏ w *)

| add_cast i A B e a b :
    a ⊏ b →
    a ⊏ cast i A B e b

where "u ⊏ v" := (decoration u v).



Reserved Notation " t ~ t' " (at level 19).

Inductive simdec : term → term → Prop :=
| sim_var x :
    var x ~ var x 

| sim_sort l :
    Sort l ~ Sort l 

| sim_assm c :
    assm c ~ assm c 

| sim_Pi i j A A' B B' :
    A ~ A' →
    B ~ B' →
    Pi i j A B ~ Pi i j A' B'

| sim_lam i j A A' B B' t t' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    lam i j A B t ~ lam i j A' B' t'

| sim_app i j A A' B B' t t' u u' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    u ~ u' →
    app i j A B t u ~ app i j A' B' t' u'

| sim_nat : 
    Nat ~ Nat 

| sim_zero :
    zero ~ zero

| sim_succ t t' :
    t ~ t' →
    succ t ~ succ t'

| sim_rec l P P' pz pz' ps ps' t t' :
    P ~ P' →
    pz ~ pz' →
    ps ~ ps' →
    t ~ t' →
    rec l P pz ps t ~ rec l P' pz' ps' t'

| sim_acc i A A' R R' a a' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    acc i A R a ~ acc i A' R' a'

| sim_accin i A A' R R' a a' p p' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    accin i A R a p ~ accin i A' R' a' p'

| sim_accinv i A A' R R' a a' p p' b b' r r' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    b ~ b' →
    r ~ r' →
    accinv i A R a p b r ~ accinv i A' R' a' p' b' r'

| sim_accel i l A A' R R' P P' p p' a a' q q' :
    A ~ A' →
    R ~ R' →
    P ~ P' →
    p ~ p' →
    a ~ a' →
    q ~ q' →
    accel i l A R P p a q ~ accel i l A' R' P' p' a' q'

| sim_obseq i A A' a a' b b' :
    A ~ A' →
    a ~ a' →
    b ~ b' →
    obseq i A a b ~ obseq i A' a' b'

| sim_obsrefl i A A' a a' :
    A ~ A' →
    a ~ a' →
    obsrefl i A a ~ obsrefl i A' a'

| sim_J i A A' a a' P P' p p' b b' e e' :
    A ~ A' →
    a ~ a' →
    P ~ P' →
    p ~ p' →
    b ~ b' →
    e ~ e' →
    J i A a P p b e ~ J i A' a' P' p' b' e'

(* admissible *)
(* | sim_cast i A A' B B' e e' a a' :
    A ~ A' →
    B ~ B' →
    e ~ e' →
    a ~ a' →
    cast i A B e a ~ cast i A' B' e' a' *)

| sim_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    injpi1 i j A1 A2 B1 B2 e ~ injpi1 i j A1' A2' B1' B2' e'

| sim_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    a2 ~ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ~ injpi2 i j A1' A2' B1' B2' e' a2'

| sim_castR i A B e a b :
    b ~ a →
    b ~ cast i A B e a

| sim_castL i A B e a b :
    a ~ b →
    cast i A B e a ~ b

where "u ~ v" := (simdec u v).

Lemma sim_cast i A A' B B' e e' a a' :
    a ~ a' →
    cast i A B e a ~ cast i A' B' e' a'.
Proof.
  intros. eauto using simdec.
Qed.

(* excludes acc_el_comp *)
Inductive dterm : term -> Prop :=
| dvar x : dterm (var x)
| dsort l : dterm (Sort l)
| dassm c : dterm (assm c)
| dpi i j A B : dterm A -> dterm B -> dterm (Pi i j A B)
| dlam i j A B t : dterm A -> dterm B -> dterm t -> dterm (lam i j A B t)
| dapp i j A B t u : dterm A -> dterm B -> dterm t -> dterm u -> dterm (app i j A B t u)
| dnat : dterm Nat 
| dzero : dterm zero 
| dsucc t : dterm t -> dterm (succ t)
| drec l P p0 pS n : dterm P -> dterm p0 -> dterm pS -> dterm n -> dterm (rec l P p0 pS n)
| deq l A a b : dterm A -> dterm a -> dterm b -> dterm (obseq l A a b)
| drefl l A a : dterm A -> dterm a -> dterm (obsrefl l A a)
| dcast l A B e a : dterm A -> dterm B -> dterm e -> dterm a -> dterm (cast l A B e a)
| dJ l A a P p b e : dterm A -> dterm a -> dterm P -> dterm p -> dterm b -> dterm e -> dterm (J l A a P p b e)
| dinjpi1 i j A1 A2 B1 B2 e : dterm A1 -> dterm A2 -> dterm B1 -> dterm B2 -> dterm e -> dterm (injpi1 i j A1 A2 B1 B2 e)
| dinjpi2 i j A1 A2 B1 B2 e a : dterm A1 -> dterm A2 -> dterm B1 -> dterm B2 -> dterm e -> dterm a -> dterm (injpi2 i j A1 A2 B1 B2 e a)
| dacc l A R a : dterm A -> dterm R -> dterm a -> dterm (acc l A R a)
| daccin i A R a p : dterm A -> dterm R -> dterm a -> dterm p -> dterm (accin i A R a p)
| daccinv i A R a p b r : dterm A -> dterm R -> dterm a -> dterm p -> dterm r -> dterm b -> dterm (accinv i A R a p r b)
| daccel i l A R P p a q : dterm A -> dterm R -> dterm P -> dterm p -> dterm a -> dterm p -> dterm q -> dterm (accel i l A R P p a q).


Lemma well_typed_implies_dterm Γ l t A : 
  Typing.typing Γ l t A -> dterm t.
Proof.
  intros. induction H; eauto using dterm.
Qed.


(* does not hold for all t, because we do not have constructors in sim for acc_el_comp *)
Lemma sim_refl t :
  dterm t ->
  t ~ t.
Proof.
  intros.
  induction H. 
  all: eauto using simdec.
Qed.

Lemma sim_sym u v :
  u ~ v -> v ~ u.
Proof.
  intros. induction H; eauto using simdec.
Qed.

Derive Signature for simdec.
Lemma sim_trans t u v :
  t ~ u -> u ~ v -> t ~ v.
Proof.
  intros. rename H0 into h. generalize v h. clear v h. induction H; intros.
  (* in some cases, dependent induction loops/takes a lot of time, so we do it by hand *)
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - assert (exists w, w = app i j A' B' t' u' /\ w ~ v) as (w & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - assert (exists w, w = rec l P' pz' ps' t' /\ w ~ v) as (w & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - dependent induction h; eauto 7 using simdec.
  - assert (exists w, w = accin i A' R' a' p' /\ w ~ v) as (w & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = accinv i A' R' a' p' b' r' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = accel i l A' R' P' p' a' q' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - assert (exists t, t = J i A' a' P' p' b' e'  /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = injpi1 i j A1' A2' B1' B2' e' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = injpi2 i j A1' A2' B1' B2' e' a2' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - apply IHsimdec. dependent induction h; eauto using simdec.
  - eapply IHsimdec in h. eauto using simdec.
Qed.

Lemma dec_refl u : 
  dterm u ->
  u ⊏ u.
Proof.
  intros.
  induction H. 
  all: eauto using decoration.
Qed.

Lemma dec_trans u v w :
  u ⊏ v →
  v ⊏ w →
  u ⊏ w.
Proof.
  intros. generalize w H0. clear w H0. induction H; intros w hw.
  1,2,3,4,5,7,8,9,11,15,16:dependent induction hw; eauto using decoration.
  - assert (exists s, s = app i j A' B' t' u' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto.
  - assert (exists s, s = rec l P' pz' ps' t' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto.
  - assert (exists s, s = accin i A' R' a' p' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto.
  - assert (exists s, s = accinv i A' R' a' p' b' r' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = accel i l A' R' P' p' a' q' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = J i A' a' P' p' b' e' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = cast i A' B' e' a' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = injpi1 i j A1' A2' B1' B2' e' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = injpi2 i j A1' A2' B1' B2' e' a2' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - dependent induction hw; econstructor; eauto.
Qed.

Lemma decoration_is_dterm t u : 
  dterm u ->
  t ⊏ u -> 
  dterm t.
Proof.
  intros. generalize H. clear H.  
  dependent induction H0; intros X; dependent destruction X; eauto 10 using dterm.
Qed.

Lemma dec_to_sim u v :
  u ⊏ v →
  u ~ v.
Proof.
  intros. induction H; eauto using simdec.
Qed.

Lemma rename_dec ρ u v :
  u ⊏ v →
  ρ ⋅ u ⊏ ρ ⋅ v.
Proof.
  induction 1 in ρ |- *.
  all: solve [ cbn ; econstructor ; eauto ].
Qed.

Lemma dterm_ren ρ t :
  dterm t ->
  dterm (ρ ⋅ t).
Proof.
  intros. generalize ρ. clear ρ. induction H; intros; simpl; eauto using dterm.
Qed.

Lemma dterm_subst_upterm σ :
  (forall x, dterm (σ x)) ->
  forall x, dterm ((up_term_term σ) x).
Proof.
  intros. destruct x.
  1:eauto using dterm.
  simpl. unfold ">>". eapply dterm_ren. eauto.
Qed.


Lemma subst_dec σ u v :
  (forall x, dterm (σ x)) ->
  u ⊏ v →
  u <[ σ ] ⊏ v <[ σ ].
Proof.
  intros. generalize σ H. clear σ H.
  induction H0.
  all: try solve [ cbn ; econstructor ; eauto using dterm_subst_upterm ].
  intros. eapply dec_refl. eauto.
Qed.

Definition dec_subst (σ θ : nat → term) :=
  ∀ x, σ x ⊏ θ x.

Lemma dec_subst_up σ θ :
  dec_subst σ θ →
  dec_subst (up_term σ) (up_term θ).
Proof.
  intros h [].
  - cbn. constructor.
  - cbn. unfold ">>". apply rename_dec. apply h.
Qed.

Lemma dec_subst_one u v :
  u ⊏ v →
  dec_subst (u..) (v..).
Proof.
  intros h [].
  - cbn. assumption.
  - cbn. constructor.
Qed.

Lemma dec_subst_scons u v σ σ' :
  u ⊏ v →
  dec_subst σ σ' →
  dec_subst (u .: σ) (v .: σ').
Proof.
  intros hu hs [].
  - cbn. assumption.
  - cbn. apply hs.
Qed.

Lemma dec_subst_refl σ :
  (forall x, dterm (σ x)) ->
  dec_subst σ σ.
Proof.
  intros. intro. apply dec_refl. eauto.
Qed.

Lemma substs_dec σ θ u :
  dterm u ->
  dec_subst σ θ →
  u <[ σ ] ⊏ u <[ θ ].
Proof.
  intros. generalize σ θ H0. clear σ θ H0. induction H.
  all: try solve [ cbn ; econstructor ; eauto using dec_subst_up ].
  intros. eapply H0.
Qed.

Lemma substs_decs σ θ u v :
  dec_subst σ θ →
  u ⊏ v →
  u <[ σ ] ⊏ v <[ θ ].
Proof.
  intros. generalize σ θ H. clear σ θ H.
  induction H0.
  all: try solve [ cbn ; econstructor ; eauto using decoration, dec_subst_up ].
  intros. eapply H.
Qed.

Lemma substs_decs_one u v a b :
  u ⊏ v →
  a ⊏ b →
  u <[ a .. ] ⊏ v <[ b .. ].
Proof.
  intros h1 h2.
  apply substs_decs. 2: auto.
  apply dec_subst_one. assumption.
Qed.

(* Fundamental lemma

  We're going to prove a more general statement with cast substitutions, but
  for now, we'll admit this version.
  I already have a plan in mind so it might not be necessary to have a look at
  it yet.
  In ETT to ITT/WTT, we used the more general version too in the final
  translation so we'll have to check whether it's needed.

*)

Definition renX m := 3 * m.
Definition renR m := 1 + (3 * m).
Definition renL m := 2 + (3 * m).

Fixpoint pack (Γ1 Γ2 : ctx) := 
  match Γ1, Γ2 with 
  | cons (l, A1) Γ1, cons (l', A2) Γ2 => (* invariant: l = l' *)
    let A1' := renL ⋅ A1 in
    let A2' := renR ⋅ A2 in
    let Aeq := heq l ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0) in
    pack Γ1 Γ2 ,, (l, A1') ,, (l, S ⋅ A2') ,, (prop, Aeq)
  | _,_ =>  ∙
  end.

Inductive ctx_compat : ctx -> ctx -> Prop := 
| compat_nil : ctx_compat ∙ ∙
| compat_cons Γ1 l1 A1 Γ2 l2 A2 : 
  l1 = l2 ->
  ctx_compat Γ1 Γ2 ->
  ctx_compat (Γ1 ,, (l1, A1)) (Γ2 ,, (l2, A2)).

Lemma WellRen_renL Γ1 Γ2 (h : ctx_compat Γ1 Γ2):
  pack Γ1 Γ2 ⊢r renL : Γ1.
Proof.
  induction h.
  - econstructor.
  - subst. unfold renL. econstructor.
    * simpl. eapply WellRen_weak,WellRen_weak,WellRen_weak. fold plus.
      eapply autosubst_simpl_WellRen. 2:eauto.
      econstructor. unfold pointwise_relation. intros.
      induction a; eauto.
      unfold renL in *.  simpl in *. rewrite IHa. lia.
    * eapply varty_meta. 1:cbn. 1:econstructor. 1:econstructor. 1:econstructor.
      unfold renL; ssimpl. eapply ren_term_morphism. 2:reflexivity.
      unfold pointwise_relation. intros. induction a.
      all:unfold ">>" in *; simpl in *; lia.
Qed.


Lemma WellRen_renR Γ1 Γ2 (h : ctx_compat Γ1 Γ2):
  pack Γ1 Γ2 ⊢r renR : Γ2.
Proof.
  induction h.
  - econstructor.
  - subst. unfold renR. econstructor. 
    * simpl. eapply WellRen_weak,WellRen_weak. fold plus. 
      eapply autosubst_simpl_WellRen.
      2:eapply WellRen_weak. 2:eapply IHh. unfold renR. simpl.
      econstructor. unfold pointwise_relation. intros.
      unfold ">>". lia. 
    * eapply varty_meta. 1:cbn. 1:econstructor. 1:econstructor.
      unfold renR; ssimpl. eapply ren_term_morphism. 2:reflexivity.
      unfold pointwise_relation. intros. induction a.
      all:unfold ">>" in *; simpl in *; lia.
Qed.


Lemma pack_Wt Γ1 Γ2 :
  ctx_compat Γ1 Γ2 ->
  ⊢ Γ1 -> 
  ⊢ Γ2 -> 
  ⊢ pack Γ1 Γ2.
Proof.
  intro h. induction h.
  1:econstructor. subst.
  intros. dependent destruction H. dependent destruction H0.
  assert (pack Γ1 Γ2 ⊢< Ax l2 > renL ⋅ A1 : Sort l2) by eauto using type_ren, WellRen_renL.
  assert (pack Γ1 Γ2,, (l2, renL ⋅ A1) ⊢< Ax l2 > S ⋅ renR ⋅ A2 : Sort l2) 
    by (rasimpl; eapply type_ren; eauto using ctx_typing, WellRen_weak, WellRen_renR). 
  simpl. econstructor. 1:econstructor. 1:econstructor.
  1:eauto.
  3:unfold Ax;simpl;eapply type_heq.
  1,2:assumption.
  * eapply type_ren; eauto using ctx_typing, WellRen_weak, WellRen_S.
  * rasimpl. rasimpl in H4. eapply type_ren; eauto using ctx_typing, WellRen_weak, WellRen_renR.
  * econstructor; eauto using ctx_typing. eapply varty_meta. 1:econstructor. 1:econstructor.
    rasimpl. reflexivity.
  * econstructor; eauto using ctx_typing. eapply varty_meta. 1:econstructor.
    rasimpl. reflexivity.
Qed.


Lemma sim_var_heq l x A1 A2 Γ1 Γ2 :
  ⊢ Γ1 -> ⊢ Γ2 ->
  ctx_compat Γ1 Γ2 ->
  Γ1 ∋< l > x : A1 ->
  Γ2 ∋< l > x : A2 ->
  ∃ e, pack Γ1 Γ2 ⊢< prop > e : heq l (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ (var x)) (renR ⋅ (var x)).
Proof.
  intros. generalize l x A1 A2 H H0 H2 H3. clear l x A1 A2 H H0 H2 H3. induction H1; intros.
  1:dependent destruction H2.
  subst.
  destruct x.
  - dependent destruction H3. dependent destruction H4.
    simpl. exists (var 0). econstructor.
    1:unshelve eapply (pack_Wt _ _ _ H0 H2); eauto using ctx_compat. 
    eapply varty_meta. 1:econstructor. ssimpl. rewrite heq_ren. unfold renL, renR. ssimpl. f_equal.
    all:eapply ren_term_morphism; eauto.
    all:unfold pointwise_relation; intros; unfold ">>"; lia.
  - dependent destruction H3. dependent destruction H4.
    dependent destruction H0. dependent destruction H2.  
    edestruct (IHctx_compat); eauto.
    eexists. eapply type_ren; eauto.
    1:eapply pack_Wt; eauto using ctx_typing, ctx_compat.
    1:simpl; eauto using WellRen_weak, WellRen_S.
    rewrite heq_ren. unfold renR, renL. rasimpl. unfold ">>". f_equal.
    3,4:eapply f_equal; lia.
    1,2:eapply ren_term_morphism; eauto.
    all:unfold pointwise_relation; intros; unfold ">>"; lia.
Qed.

Lemma sim_heq_ih_aux {u u'}: 
(forall (i : nat) (Γ1 Γ2 : ctx) (A1 A2 : term),
    ctx_compat Γ1 Γ2 → 
    Γ1 ⊢< ty i > u : A1 → 
    Γ2 ⊢< ty i > u' : A2 → 
    ∃ e : term, pack Γ1 Γ2 ⊢< prop > e : heq (ty i) (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ u) (renR ⋅ u')) ->
(forall (l : level) (Γ1 Γ2 : ctx) (A1 A2 : term),
    ctx_compat Γ1 Γ2 → 
    Γ1 ⊢< l > u : A1 → 
    Γ2 ⊢< l > u' : A2 → 
    ∃ e : term, pack Γ1 Γ2 ⊢< prop > e : heq l (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ u) (renR ⋅ u')).
Proof.
  intros. destruct l; eauto. eexists. eapply type_ren in H1, H2.
  3,6:eauto using WellRen_renL, WellRen_renR.
  3,5:reflexivity.
  2,3:eauto using validity_ty_ctx, pack_Wt. 
  eapply type_true_heq; eauto using validity_ty_ty.
Qed.
    

Lemma meta_ctx Γ l A Δ t :
  Γ ⊢< l > t : A ->
  Γ = Δ ->
  Δ ⊢< l > t : A.
Proof.
  intros. subst. assumption.
Qed.

Lemma sim_heq i Γ1 Γ2 t1 t2 A1 A2 :
  ctx_compat Γ1 Γ2 ->
  t1 ~ t2 →
  Γ1 ⊢< ty i > t1 : A1 →
  Γ2 ⊢< ty i > t2 : A2 →
  ∃ e, pack Γ1 Γ2 ⊢< prop > e : heq (ty i) (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ t1) (renR ⋅ t2).
Proof.
  intros hctx hsim h1 h2.
  induction hsim in i, Γ1, Γ2, hctx, A1, A2, h1, h2 |- *.
  all:try solve 
   [ eapply type_inv in h1; dependent destruction h1 ; dependent destruction lvl_eq ].
  all : assert (⊢ pack Γ1 Γ2) by eauto using pack_Wt, validity_ty_ctx.
  - pose proof h1 as h1'. pose proof h2 as h2'.
    eapply type_inv in h1. dependent destruction h1.
    eapply type_inv in h2. dependent destruction h2.
    eapply sim_var_heq in hctx as temp. 2-5:eauto using validity_ty_ctx, validity_conv_left.
    destruct temp.
    eexists. eapply type_conv. 1:eauto.
    eapply conv_heq.
    1,2:eapply conv_ren; eauto using conv_sym, WellRen_renL, WellRen_renR.
    all:eapply conv_refl, type_conv.
    1,3:eapply type_ren. 3:eapply WellRen_renL. 7:eapply WellRen_renR. 
    all: eauto.
    all:eapply conv_ren; eauto using WellRen_renL, WellRen_renR.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2.  
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty. 3:eapply WellRen_renL. all:eauto.
    eapply conv_ren in conv_ty0. 3:eapply WellRen_renR. all:eauto.
    simpl in *.
    eexists. eapply type_conv.
    2:eapply conv_heq.
    1:eapply type_heq_refl.
    all:simpl.
    5,6:eapply conv_refl; econstructor; eauto.
    1,2:eapply meta_lvl. 1:eapply meta_conv.
    1,4:eauto using typing.
    1-3:reflexivity.
    all:eauto using conv_sym.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.
    
    edestruct IHhsim1. 2:eapply A_Wt. 2:eapply A_Wt0. 1:eauto.
    edestruct IHhsim2. 2:eapply B_Wt. 2:eapply B_Wt0. 1:eauto using ctx_compat.
    eexists. eapply type_conv.
    1:eapply type_heq_pi. 
    1,2:eapply type_ren. 1:eapply A_Wt. 4:eapply A_Wt0.
    1-6:eauto using WellRen_renL, WellRen_renR.
    1,2:eapply type_ren.
    1:eapply B_Wt. 4:eapply B_Wt0.
    1,4:eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    1,3:eapply WellRen_up. 1,3:eauto using WellRen_renL,WellRen_renR.
    1-4:rasimpl;reflexivity.
    2:{ simpl in H1. unfold renR, renL in *. eapply meta_conv. 1:eapply H1. f_equal.
        all:ssimpl; substify; eapply subst_term_morphism; eauto.
        all:unfold pointwise_relation; intros; unfold ">>"; simpl.
        * destruct a; eauto. simpl. assert (forall x y, x = y -> var x = var y) by eauto. eapply H2. lia.
        * destruct a; eauto. 1:simpl. assert (forall x y, x = y -> var x = var y) by eauto. eapply H2. lia. }
    1:eauto.   
    eapply conv_heq.
    3,4:simpl; eapply conv_refl; eauto.
    3,4:eapply type_pi. 3-6:eapply type_ren; eauto using ctx_typing, WellRen_renL, WellRen_renR, type_ren.
    3,4:eapply WellRen_up; eauto using WellRen_renL, WellRen_renR.
    1:change (Sort (Ru i0 j)) with (renL ⋅ (Sort (Ru i0 j))).
    2:change (Sort (Ru i0 j)) with (renR ⋅ (Sort (Ru i0 j))).
    1,2:eapply conv_ren; eauto using conv_sym, WellRen_renL, WellRen_renR.
    
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    unfold Ru in lvl_eq. destruct j; dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim1. 2:eapply A_Wt. 2:eapply A_Wt0. 1:eauto.
    edestruct IHhsim3. 2:eapply t_Wt. 2:eapply t_Wt0. 1:eauto using ctx_compat. 
    rasimpl in H0.
    eexists. eapply type_conv.
    1:eapply type_heq_lam. 3:eapply H0. 
    1,2:eapply type_ren. 1:eapply t_Wt. 4:eapply t_Wt0.
    2,5:eapply WellRen_up.
    1-8:eauto using ctx_typing, WellRen_renL, WellRen_renR, type_ren.
    1:eapply meta_conv. 1:eapply H1.
    1:rasimpl;unfold renL, renR,">>";f_equal; eapply ren_term_morphism; eauto.
    1-4:unfold pointwise_relation; intros; destruct a; simpl; lia.
    eapply conv_heq.
    * change (Pi i0 (ty n) (renL ⋅ A) (up_ren renL ⋅ B)) with (renL ⋅ (Pi i0 (ty n) A B)).
      eapply conv_ren; eauto using WellRen_renL, conv_sym.
    * change (Pi i0 (ty n) (renR ⋅ A') (up_ren renR ⋅ B')) with (renR ⋅ (Pi i0 (ty n) A' B')).
      eapply conv_ren; eauto using WellRen_renR, conv_sym.
    * change (lam i0 (ty n) (renL ⋅ A) (up_ren renL ⋅ B) (up_ren renL ⋅ t)) with (renL ⋅ (lam i0 (ty n) A B t)).
      eapply conv_refl.
      1:eapply type_ren; eauto using WellRen_renL.
      1:eapply meta_lvl. 1:econstructor; eauto.
      all: eauto. 
    * change (lam i0 (ty n) (renL ⋅ A) (up_ren renL ⋅ B) (up_ren renL ⋅ t)) with (renL ⋅ (lam i0 (ty n) A B t)).
      eapply conv_refl.
      1:eapply type_ren; eauto using WellRen_renR.
      1:eapply meta_lvl. 1:econstructor; eauto.
      all: eauto.
  
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    unfold Ru in lvl_eq. destruct j; dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim3. 2:eapply t_Wt. 2:eapply t_Wt0. 1:eauto.
    pose proof (sim_heq_ih_aux IHhsim4) as IHhsim4'. 
    edestruct IHhsim4'. 2:eapply u_Wt. 2:eapply u_Wt0. 1:eauto using ctx_compat.
    rasimpl in H0. change (ty (ru i0 i)) with (Ru i0 (ty i)) in H0.
    eexists. eapply type_conv.
    1:eapply type_heq_app.
    5:eapply H0.
    5:eapply H1.
    1-4:eapply type_ren; eauto using WellRen_renL, WellRen_renR.
    eapply conv_heq; asimpl; renamify.
    1:replace (B <[ renL ⋅ u .: renL >> var]) with (renL ⋅ (B <[ u .: var])) by (rasimpl;reflexivity).
    1:eapply conv_ren; eauto using conv_sym, WellRen_renL.
    1:replace (B' <[ renR ⋅ u' .: renR >> var]) with (renR ⋅ (B' <[ u' .: var])) by (rasimpl;reflexivity).
    1:eapply conv_ren; eauto using conv_sym, WellRen_renR.
    1-2:eapply conv_refl. all:eapply meta_conv.
    1,3:eapply meta_lvl. 1,3:econstructor; eapply type_ren; eauto using WellRen_renL, ctx_typing, type_ren.
    1:eapply WellRen_up. all:eauto using WellRen_renL, WellRen_renR, ctx_typing, type_ren.
    2,3:rasimpl;reflexivity. eapply WellRen_up. all:eauto using WellRen_renR.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty, conv_ty0; eauto using WellRen_renL, WellRen_renR.
    eexists.
    eapply type_conv. 1:eapply type_heq_refl.
    3:eapply conv_heq.
    3,4 :eauto using conv_sym.
    3,4:eauto using conv_refl, typing.
    all:eapply meta_lvl;rasimpl;eauto using typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty, conv_ty0; eauto using WellRen_renL, WellRen_renR.
    eexists.
    eapply type_conv. 1:eapply type_heq_refl.
    3:eapply conv_heq.
    3,4 :eauto using conv_sym.
    3,4:eauto using conv_refl, typing.
    all:eapply meta_lvl;rasimpl;eauto using typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim; eauto. rasimpl in H0.
    eapply conv_ren in conv_ty, conv_ty0; eauto using WellRen_renL, WellRen_renR.
    rasimpl in conv_ty. rasimpl in conv_ty0.
    eexists. eapply type_conv.
    1:eapply type_heq_succ. 3:eapply H0. 1,2:eauto using type_ren, WellRen_renL, WellRen_renR.
    eapply conv_heq; eauto using conv_sym.
    all:eapply conv_refl, type_ren; eauto using WellRen_renL, WellRen_renR, typing.

  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    subst. clear lvl_eq0.

    edestruct IHhsim1. 2:exact P_Wt. 2:exact P_Wt0. 1:eauto using ctx_compat.
    edestruct IHhsim2; eauto.
    edestruct IHhsim3. 2:exact p_succ_Wt. 2:exact p_succ_Wt0.
    1:eauto using ctx_compat.
    edestruct IHhsim4; eauto.
    clear IHhsim1 IHhsim2 IHhsim3 IHhsim4.

    eexists. eapply type_conv.
    1:eapply type_heq_rec. 
    1,2:eapply type_ren. 1:exact P_Wt. 4:exact P_Wt0. 
    2,5:eapply WellRen_up. 1-8:eauto using ctx_typing, typing, WellRen_renL, WellRen_renR.
    1,4:eapply type_ren. 1:eapply p_zero_Wt. 4:eapply p_zero_Wt0.
    1-6:eauto using WellRen_renL, WellRen_renR. 1,2:rasimpl; reflexivity.
    1,3:eapply type_ren. 1:exact p_succ_Wt. 4:eapply p_succ_Wt0.
    2,5:eapply WellRen_up. 2,4:eapply WellRen_up; eauto using WellRen_renL, WellRen_renR.
    2,3,4,6:rasimpl;reflexivity.
    1,2:econstructor; eauto using ctx_typing, typing. 
    1,2:eapply type_ren; eauto using WellRen_up, WellRen_renL, WellRen_renR, typing, ctx_typing.
    1,2:eapply type_ren. 1:exact t_Wt. 4:exact t_Wt0. 1-6:eauto using WellRen_renL, WellRen_renR.
    * eapply meta_conv. 1:eapply H0.
      unfold renL, renR; rasimpl. f_equal.
      all:eapply ren_term_morphism; eauto.
      all:unfold pointwise_relation; intros; unfold ">>"; simpl; destruct a; simpl; lia.
    * eapply meta_conv. 1:eapply H1.
      f_equal; rasimpl; eauto.
    * eapply meta_conv. 1:eapply meta_ctx.  1:eapply H2.
      ** simpl. unfold renL, renR. rasimpl. f_equal. 1:f_equal.
        1:f_equal. 1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. 1:f_equal. 1:eapply ren_term_morphism; eauto.
        1:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. f_equal. eapply ren_term_morphism; eauto.
        unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
      ** simpl. unfold renL, renR. rasimpl. f_equal.
        3,4:eapply ren_term_morphism; eauto.
        3,4:unfold pointwise_relation; intros; unfold ">>"; destruct a; try destruct a; simpl; lia.
        1,2:eapply subst_term_morphism; eauto.
        all:unfold pointwise_relation; intros; unfold ">>"; destruct a; try destruct a; simpl; eauto.
        1,2:f_equal;lia.
    * eapply meta_conv. 1:eapply H3. 1:rasimpl; eauto.
    * eapply conv_heq. 
      1,3:replace ((up_ren renL ⋅ P) <[ (renL ⋅ t)..]) with (renL ⋅ (P <[t..])) by (rasimpl;reflexivity).
      3,4:replace ((up_ren renR ⋅ P') <[ (renR ⋅ t')..]) with (renR ⋅ (P' <[t'..])) by (rasimpl;reflexivity).
      2:replace (rec (ty i) (up_ren renL ⋅ P) (renL ⋅ pz) (up_ren (up_ren renL) ⋅ ps) (renL ⋅ t))
        with (renL ⋅ rec (ty i) P pz ps t) by (rasimpl;reflexivity).
      4:replace (rec (ty i) (up_ren renR ⋅ P') (renR ⋅ pz') (up_ren (up_ren renR) ⋅ ps') (renR ⋅ t'))
        with (renR ⋅ rec (ty i) P' pz' ps' t') by (rasimpl;reflexivity).
      all:eauto using conv_refl, conv_sym, type_ren, conv_ren, WellRen_renL, WellRen_renR, typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim2. 2:exact B_Wt. 2:exact B_Wt0. 1:eauto using ctx_compat.
    edestruct IHhsim3; eauto.
    eexists. eapply type_conv.
    1:eapply type_heq_acc.
    1,3:eapply type_ren. 1:eapply B_Wt. 4:eapply B_Wt0.
    2,5:eapply WellRen_up. 2,4:eapply WellRen_up.
    1-10:eauto using WellRen_renL, WellRen_renR.
    2,3:rasimpl; reflexivity.
    1,2:econstructor; eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    1,2:eapply type_ren. 1,5:eapply type_ren. 1,5:eauto. 8,11:eauto using WellRen_S.
    1-10:eauto using WellRen_renL, WellRen_renR, ctx_typing, type_ren.
    1,2:eapply type_ren. 1:eapply a_Wt. 4:eapply a_Wt0.
    1-6:eauto using WellRen_renL, WellRen_renR.
    * eapply meta_conv. 1:eapply meta_ctx. 1:eapply H0.
      ** simpl. unfold renL, renR. rasimpl.
        f_equal. 1:f_equal. 1:f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. 1:f_equal.
        1:eapply ren_term_morphism; eauto.
        1:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. f_equal.
        eapply ren_term_morphism; eauto.
        unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
      ** simpl. unfold renL, renR. rasimpl. f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a0; simpl; try destruct a0; simpl; lia.
    * eapply H1.
    * eapply conv_heq.
      1,3:change (Sort prop) with (renL ⋅ (Sort prop)).
      3,4:change (Sort prop) with (renR ⋅ (Sort prop)).
      2,4:eapply conv_refl.
      all:eauto using type_ren, conv_ren, conv_sym, WellRen_renL, WellRen_renR, typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2.

    clear hsim1 hsim2 hsim3 hsim4 hsim5 hsim6.
    clear IHhsim1.
    edestruct IHhsim2. 2:eapply R_Wt. 2:eapply R_Wt0. 1:eauto using ctx_compat. clear IHhsim2.
    edestruct IHhsim3. 2:eapply P_Wt. 2:eapply P_Wt0. 1:eauto using ctx_compat. clear IHhsim3.
    edestruct IHhsim4. 2:eapply p_Wt. 2:eapply p_Wt0. 1:eauto using ctx_compat. clear IHhsim4.
    edestruct IHhsim5; eauto using ctx_compat. clear IHhsim5 IHhsim6.

    eexists. eapply type_conv.
    1:eapply type_heq_accel.
    (* 3,6:eapply type_ren. 3:eapply q_Wt. 6:eapply q_Wt0.
    3-8:eauto using WellRen_renL, WellRen_renR. 3,4:rasimpl; reflexivity. *)
    1,4:eapply type_ren. 1:eapply P_Wt. 4:eapply P_Wt0. 2,5:eapply WellRen_up.
    1-8:eauto using WellRen_renL, WellRen_renR.
    1,2:eauto using ctx_typing, WellRen_renL, WellRen_renR, type_ren.
    2,4:eapply type_ren. 2:eapply q_Wt. 5:eapply q_Wt0.
    2-7:eauto using WellRen_renL, WellRen_renR. 2,3:rasimpl; reflexivity.
    1,2:eapply type_ren. 1:eapply p_Wt. 4:eapply p_Wt0.
    2:eapply WellRen_up. 2:eapply WellRen_up. 2:eapply WellRen_renL.
    2,3: eauto using ctx_compat.
    2:unfold B, R'0, P'0; rasimpl; reflexivity.
    2:unfold P'';rasimpl;reflexivity.
    3:eapply WellRen_up. 3:eapply WellRen_up; eauto using WellRen_renR.
    3:unfold B0, R'1, P'1; rasimpl; reflexivity.
    3:unfold P''0;rasimpl;reflexivity.
    1,2:econstructor.
    1,3:eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    1:replace (Pi (ty n) (ty i) (S ⋅ renL ⋅ A) (Pi prop (ty i) ((1 .: (0 .: S >> S)) ⋅ (0 .: (1 .: renL >> (S >> S))) ⋅ R) ((1 .: (S >> S) >> S) ⋅ up_ren renL ⋅ P))) with ((up_ren renL) ⋅ B) by (unfold B, R'0, P'0; rasimpl; reflexivity).
    2:replace (Pi (ty n) (ty i) (S ⋅ renR ⋅ A') (Pi prop (ty i) ((1 .: (0 .: S >> S)) ⋅ (0 .: (1 .: renR >> (S >> S))) ⋅ R') ((1 .: (S >> S) >> S) ⋅ up_ren renR ⋅ P'))) with ((up_ren renR) ⋅ B0) by (unfold B0, R'1, P'1; rasimpl; reflexivity).
    1,2:eapply type_ren. 3, 7:eapply WellRen_up. 3,5:eauto using WellRen_renL, WellRen_renR. 3,4:eauto.
    1-6:eapply validity_ty_ctx in p_Wt; eapply validity_ty_ctx in p_Wt0; 
      dependent destruction p_Wt; dependent destruction p_Wt0; eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    * eapply meta_conv. 1:eapply meta_ctx. 1:eapply H0.
      ** simpl. unfold renL, renR. rasimpl.
        f_equal. 1:f_equal. 1:f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. 1:f_equal.
        1:eapply ren_term_morphism; eauto.
        1:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. f_equal.
        eapply ren_term_morphism; eauto.
        unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
      ** simpl. unfold renL, renR. rasimpl. f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a0; simpl; try destruct a0; simpl; lia.
    * eauto.
    * eapply meta_conv. 1:eapply H1. unfold renL, renR; f_equal; rasimpl.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a0; simpl; lia.
    * eapply meta_conv. 1:eapply meta_ctx. 1:eapply  H2.
      ** simpl. unfold renR, renL, P'', B, R'0, P'0, B0, R'1, P'1. f_equal. 1:f_equal.
        *** f_equal. 1:f_equal. 2:f_equal.
            4:f_equal. 5:f_equal. all:rasimpl.
            all:eapply ren_term_morphism; eauto.
            all:unfold pointwise_relation; intros; unfold ">>"; destruct a0; try destruct a0; simpl; lia.
        *** f_equal. 1:f_equal. 1:f_equal. 2:f_equal. 4:f_equal.
            4:f_equal. 4:f_equal. 5:f_equal. all:rasimpl.
            all:eapply ren_term_morphism; eauto.
            all:unfold pointwise_relation; intros; unfold ">>" ; destruct a0 ; try destruct a0; simpl; lia.
      ** unfold P'', P''0, renL, renR. f_equal. all:rasimpl.
        all:eapply ren_term_morphism; eauto.
        all:unfold pointwise_relation; intros; unfold ">>" ; destruct a0 ; try destruct a0; simpl ; lia.
    * eapply conv_heq.
      1:replace ((up_ren renL ⋅ P) <[ (renL ⋅ a)..]) with (renL ⋅ (P <[ a..])) by (rasimpl;reflexivity).
      2:replace ((up_ren renR ⋅ P') <[ (renR ⋅ a')..]) with (renR ⋅ (P' <[ a'..])) by (rasimpl;reflexivity).
      3:replace ((0 .: (1 .: renL >> (S >> S))) ⋅ R) with (up_ren (up_ren renL) ⋅ R) by (rasimpl;reflexivity).
      4:replace ((0 .: (1 .: renR >> (S >> S))) ⋅ R') with (up_ren (up_ren renR) ⋅ R') by (rasimpl;reflexivity).
      3,4:eapply conv_refl.
      3,4:eapply meta_conv.
      1,2,3,5:eauto using type_ren, conv_sym, conv_ren, WellRen_renL, WellRen_renR, typing.
      all:rasimpl;reflexivity.

  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2.
    dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim1; eauto.
    edestruct IHhsim2; eauto.
    edestruct IHhsim3; eauto.

    eexists. eapply type_conv.
    1:eapply type_heq_obseq.
    7:eapply conv_heq. 9,10:rasimpl; eapply conv_refl.
    1-6:eauto using type_ren, WellRen_renL, WellRen_renR.
    1:replace (Sort prop) with (renL ⋅ (Sort prop)) by reflexivity.
    2:replace (Sort prop) with (renR ⋅ (Sort prop)) by reflexivity.
    1-4:eauto 8 using conv_sym, conv_ren, type_ren, typing, WellRen_renL, WellRen_renR.

  - eapply type_inv in h2 as h2'; dependent destruction h2'. subst.
    edestruct (IHhsim _ _ _ _ _ hctx h1 a_Wt).
    eexists. 
    eapply type_heq_trans.
    4:eapply H0.
    all: try solve [ eapply type_ren; 
      eauto using WellRen_renL, WellRen_renR, validity_ty_ctx ].
    eapply type_ren.
    3:eapply WellRen_renR.
    2:eauto using validity_ty_ctx.
    1:eapply type_conv. 2:eapply conv_heq.
    7:rewrite heq_ren; reflexivity.
    1:eapply type_heq_cast. 3:exact e_Wt.
    all:eauto using conv_sym, conv_refl, conversion.
  - eapply type_inv in h1 as h1'; dependent destruction h1'. subst.
    destruct (IHhsim _ _ _ _ _ hctx a_Wt h2).
    eexists. 
    eapply type_heq_trans.
    5:eapply H0.
    all: try solve [ eapply type_ren; 
      eauto using WellRen_renL, WellRen_renR, validity_ty_ctx ].
    eapply type_ren.
    3:eapply WellRen_renL.
    2:eauto using validity_ty_ctx.
    1:eapply type_conv. 2:eapply conv_heq.
    7:rewrite heq_ren; reflexivity.
    1:eapply type_heq_sym, type_heq_cast.
    5:eapply e_Wt.
    all:eauto using conv_sym, conv_refl, typing.
Qed.


Fixpoint get_entry n Γ :=
  match Γ, n with 
  | nil, _ => (prop, Nat) (* junk *)
  | cons (l, A) Γ, 0 => (l, S ⋅ A)
  | cons _ Γ, S n => 
    let (l, A) := get_entry n Γ in
      (l, S ⋅ A)
    end.
  
Definition get_tail Γ : ctx :=
  match Γ with  
  | cons _ Γ => Γ
  | nil => nil (* junk *)
  end.

(* Fixpoint pack_refl Γ n :=
  let X := get_entry (n / 3) Γ in
  (heq_refl (fst X) (snd X) (var 0)) .: (var n) .: (var n) .: (pack_refl (get_tail Γ) (n + 1)). *)

Definition pack_refl Γ n :=
  let X := get_entry (n / 3) Γ in
  match n mod 3 with 
  | 0 => heq_refl (fst X) (snd X) (var (n / 3))
  | _ => var (n / 3)
  end.

Lemma mod_aux0 x : (0 + 3 * x) mod 3 = 0.
Proof.
  rewrite Nat.add_mod by lia. 
  replace (3 * x) with (x * 3) by lia.
  rewrite Nat.mod_mul.
  2:eauto.
  simpl. eauto.
Qed.

Lemma mod_aux1 x : (1 + 3 * x) mod 3 = 1.
Proof.
  rewrite Nat.add_mod by lia. 
  replace (3 * x) with (x * 3) by lia.
  rewrite Nat.mod_mul.
  2:eauto.
  simpl. eauto.
Qed.


Lemma mod_aux2 x : (2 + 3 * x) mod 3 = 2.
Proof.
  rewrite Nat.add_mod by lia. 
  replace (3 * x) with (x * 3) by lia.
  rewrite Nat.mod_mul.
  2:eauto.
  simpl. eauto.
Qed.

Lemma comp_refl_renL' Γ x :
  (pack_refl Γ (renL x)) = var x.
Proof.
  unfold pack_refl, renL. rewrite mod_aux2. 
  replace (2 + 3 * x) with (x * 3 + 2) by lia.
  rewrite Nat.div_add_l by lia.  simpl. replace (x + 0) with x by lia. reflexivity.
Qed.

Lemma comp_refl_renL Γ :
  pointwise_relation _ eq (renL >> pack_refl Γ) var.
Proof.
  unfold pointwise_relation. intros. eapply comp_refl_renL'.
Qed.


Lemma comp_refl_renR' Γ x :
  (pack_refl Γ (renR x)) = var x.
Proof.
  unfold pack_refl, renR. rewrite mod_aux1. 
  replace (1 + 3 * x) with (x * 3 + 1) by lia.
  rewrite Nat.div_add_l by lia.  simpl. replace (x + 0) with x by lia. reflexivity.
Qed.

Lemma comp_refl_renR Γ :
  pointwise_relation _ eq (renR >> pack_refl Γ) var.
Proof.
  unfold pointwise_relation. intros. eapply comp_refl_renR'.
Qed.

Lemma aux_match_nat {A B} (f : A -> B) (n : nat) p0 ps :
  f (match n with 
  | 0 => p0 
  | S n => ps n end)
  = match n with 
  | 0 => f p0 
  | S n => f (ps n) end.
Proof.
  destruct n; reflexivity.
Qed.

Lemma aux_match_nat2 {A} (n : nat) (p0 p0':A) ps ps' :
  p0 = p0' -> 
  (forall x, ps x = ps' x) ->
  match n with 
  | 0 => p0 
  | S n => ps n end
  = match n with 
  | 0 => p0' 
  | S n => ps' n end.
Proof.
  intros. destruct n; eauto.
Qed.

Lemma fun_snd {A B C} (f:B -> C) (t : A * B): 
  f (snd t) = snd (let (a, b) := t in (a, f b)).
Proof.
  destruct t. reflexivity.
Qed.
Lemma fun_fst {A B C} (f:B -> C) (t : A * B): 
  fst t = fst (let (a, b) := t in (a, f b)).
Proof.
  destruct t. reflexivity.
Qed.
Lemma snd_get_entry n Γ l A :
  snd (get_entry (S n) (Γ ,, (l, A))) = S ⋅ (snd (get_entry n Γ)).
Proof.
  simpl. symmetry. eapply fun_snd.
Qed.

Lemma fst_get_entry n Γ l A :
  fst (get_entry (S n) (Γ ,, (l, A))) = fst (get_entry n Γ).
Proof.
  simpl. symmetry. eapply fun_fst.
Qed.

Lemma commute_renL_S A (ρ : nat -> A) : 
  pointwise_relation _ eq (↑ >> (renL >> ρ)) (renL >> (↑ >> (↑ >> (↑ >> ρ)))).
Proof.
  unfold pointwise_relation. intros.
  unfold ">>", "↑", renL. f_equal. lia.
Qed.

Lemma commute_renR_S A (ρ : nat -> A) : 
  pointwise_relation _ eq (↑ >> (renR >> ρ)) (renR >> (↑ >> (↑ >> (↑ >> ρ)))).
Proof.
  unfold pointwise_relation. intros.
  unfold ">>", "↑", renR. f_equal. lia.
Qed.

Lemma pack_refl_Wt Γ : 
  ⊢ Γ -> Γ ⊢s pack_refl Γ : pack Γ Γ.
Proof.
  intros. induction H.
  1:econstructor.
  simpl. econstructor. 1:econstructor. 1:econstructor.
  - rewrite autosubst_simpl_WellSubst.
    1:eapply WellSubst_weak. 1:eapply IHctx_typing.
    1:assumption.
    econstructor. unfold pointwise_relation. intros.
    unfold ">>".
    unfold pack_refl.
    replace (↑ (↑ (↑ a)) mod 3) with (a mod 3).
    2:{ unfold "↑".
        replace (S (S (S a))) with (3 + a) by lia.
        rewrite Nat.add_mod. 2:lia. 
        change (3 mod 3) with (1 * 3 mod 3).
        rewrite Nat.mod_mul. 2:lia.
        symmetry.
        rewrite Nat.mod_small.
        1:lia.
        change (0 + a mod 3) with (a mod 3).
        eapply Nat.mod_upper_bound. lia. }
    rewrite (aux_match_nat (fun x => S ⋅ x)).
    eapply aux_match_nat2.
    * rewrite ren_heq_refl. f_equal.
      3:{ unfold "↑". 
          change (S ⋅ (var (a / 3))) with (var (1 + a / 3)).
          replace (S (S (S a)) / 3) with (1 + a /3). 1:reflexivity.
          change (S (S (S a))) with (1 * 3 + a).
          rewrite Nat.div_add_l. 2:lia.
          reflexivity. }
      ** replace (↑ (↑ (↑ a)) / 3) with (S (a / 3)).
         2:unfold "↑". 2:replace (S (S (S a))) with (1*3 + a) by lia.
         2:rewrite Nat.div_add_l. 2-3:lia.
         rewrite fst_get_entry. reflexivity.
      ** replace (↑ (↑ (↑ a)) / 3) with (S (a / 3)).
         2:unfold "↑". 2:replace (S (S (S a))) with (1*3 + a) by lia.
         2:rewrite Nat.div_add_l. 2-3:lia.
         rewrite snd_get_entry. reflexivity.
    * intros. unfold "↑". change (S ⋅ (var (a /3))) with (var (1 + a /3)).
      replace (S (S (S a)) / 3) with (1 + a / 3). 1:reflexivity.
      replace (S (S (S a))) with (1 * 3 + a) by lia.
      rewrite Nat.div_add_l. 1:reflexivity. lia.
  - ssimpl. setoid_rewrite <- commute_renL_S.
    setoid_rewrite comp_refl_renL.
    change (pack_refl (Γ,, (l, A)) (↑ (↑ 0))) with (var 0).
    econstructor. 1:eauto using ctx_typing.
    1:eapply varty_meta. 1:econstructor. rasimpl. reflexivity.
  - ssimpl. setoid_rewrite <- commute_renR_S.
    setoid_rewrite comp_refl_renR.
    change (pack_refl (Γ,, (l, A)) (↑ (↑ 0))) with (var 0).
    econstructor. 1:eauto using ctx_typing.
    1:eapply varty_meta. 1:econstructor. rasimpl. reflexivity.
  - rewrite  heq_subst. rasimpl.  setoid_rewrite <- commute_renR_S.  setoid_rewrite <- commute_renL_S.
    setoid_rewrite comp_refl_renL. setoid_rewrite comp_refl_renR.
    unfold ">>". unfold pack_refl. simpl. renamify.
    eapply type_heq_refl.
    1:eapply type_ren; eauto using ctx_typing, WellRen_S.
    econstructor; eauto using ctx_typing.
    econstructor.
Qed.



Lemma compat_refl Γ : ctx_compat Γ Γ.
Proof.
  induction Γ.
  1:econstructor.
  destruct a. econstructor; eauto.
Qed.

Corollary sim_heq_same_ctx i Γ t1 t2 A1 A2 :
  t1 ~ t2 →
  Γ ⊢< ty i > t1 : A1 →
  Γ ⊢< ty i > t2 : A2 →
  ∃ e, Γ ⊢< prop > e : heq (ty i) A1 A2 t1 t2.
Proof.
  intros. edestruct sim_heq; eauto using compat_refl.
  eapply subst_ty in H2. 3:eapply pack_refl_Wt.
  2-4:eauto using validity_ty_ctx.
  rewrite heq_subst in H2. rasimpl in H2.
  setoid_rewrite comp_refl_renL in H2.
  setoid_rewrite comp_refl_renR in H2.
  rasimpl in H2.
  eauto.
Qed.



(* Potential translations *)

Definition ctx_dec (Γ Δ : ctx) :=
  Forall2 (λ u v, fst u = fst v ∧ snd u ⊏ snd v) Γ Δ.

Notation " Γ ⊂ Δ " := (ctx_dec Γ Δ) (at level 19).

Definition tr_ctx Γ Δ :=
  ⊢ Δ ∧ Γ ⊂ Δ.

Definition tr_ty_data l t A Γ' t' A' :=
  Γ' ⊢< l > t' : A' ∧ t ⊏ t' ∧ A ⊏ A'.

Notation "D ⊨⟨ l ⟩ t : A ↦ u : B" :=
  (tr_ty_data l t A D u B)
  (at level 50, t, A, u, B at next level).

Definition tr_ty_abs l t A Γ' A' :=
  ∃ t', tr_ty_data l t A Γ' t' A'.

Notation "D ⊨⟨ l ⟩ t : A ⇒ B" :=
  (tr_ty_abs l t A D B)
  (at level 50, t, A, B at next level).

Definition tr_ty l t A Γ' :=
  ∃ A', Γ' ⊨⟨ l ⟩ t : A ⇒ A'.

Notation "D ⊨⟨ l ⟩ t : A" :=
  (tr_ty l t A D)
  (at level 50, t, A at next level).

Definition eqtrans l A u v Γ' A' A'' u' v' e :=
  match l with
  | prop => True
  | ty i =>
    A ⊏ A' ∧
    A ⊏ A'' ∧
    u ⊏ u' ∧
    v ⊏ v' ∧
    Γ' ⊢< prop > e : heq (ty i) A' A'' u' v'
  end.

Definition tr_eq Γ' l A u v :=
  ∃ A' A'' u' v' e, eqtrans l A u v Γ' A' A'' u' v' e.

Notation "D ⊨⟨ l ⟩ u ≡ v : A" :=
  (tr_eq D l A u v)
  (at level 50, u, v, A at next level).

(* Type heads *)

Inductive type_head := hSort (l : level) | hPi | hNat | hacc | hobseq.

Inductive has_type_head : term → type_head → Prop :=
| isSort l : has_type_head (Sort l) (hSort l)
| isPi i j A B : has_type_head (Pi i j A B) hPi
| isNat : has_type_head Nat hNat
| isacc i A R x : has_type_head (acc i A R x) hacc
| isobseq i A u v : has_type_head (obseq i A u v) hobseq.

Lemma keep_head_ty_aux Γ l A t h u :
  t ⊏ u ->
  Γ ⊢< l > u : A -> 
  has_type_head t h ->
  exists B e v, 
    t ⊏ v /\
    has_type_head v h /\
    Γ ⊢< l > v : B /\
    Γ ⊢< prop > e : heq l A B u v.
Proof.
  intros. induction H1.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H0. dependent destruction H0. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx, decoration.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    + eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H1. dependent destruction H1. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx. 
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H0. dependent destruction H0. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    + eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H2. dependent destruction H2. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym. 4,5:eapply conv_refl.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eauto using typing, conv_sym.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H2. dependent destruction H2. subst.
      eexists. eexists. eexists. 
      Unshelve. 4:exact (obseq (ty n) A' a' b'). 2,3:shelve.  
      intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym. 4,5:eapply conv_refl.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eauto using typing, conv_sym.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v' & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
Qed.

Lemma keep_head_ty Γ l A A0 h :
  A0 ⊏ A ->
  Γ ⊢< Ax l > A : Sort l -> 
  has_type_head A0 h ->
  exists B e, 
    A0 ⊏ B /\
    has_type_head B h /\
    Γ ⊢< prop > e : obseq (Ax l) (Sort l) A B.
Proof.
  intros. eapply keep_head_ty_aux in H1; eauto.
  destruct H1 as (B & e & v & refines & has_head & v_Wt & e_Wt).
  dependent destruction has_head;
  eapply type_inv in v_Wt; dependent destruction v_Wt.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - dependent destruction lvl_eq. destruct l; dependent destruction H1.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    4:eapply conv_refl.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo. 3:eapply e_Wt. all:eauto using typing, validity_ty_ctx.
Qed.


Lemma keep_head Γ' l t A h :
  Γ' ⊨⟨ l ⟩ t : A →
  has_type_head A h →
  ∃ A',
    has_type_head A' h ∧
    Γ' ⊨⟨ l ⟩ t : A ⇒ A'.
Proof.
  intros ht hh.
  destruct ht. destruct H. destruct H. destruct H0.
  eapply validity_ty_ty in H as H'.
  eapply keep_head_ty in hh; eauto.
  destruct hh as (B & e & refines & has_head & e_Wt).
  eexists. split; eauto.
  econstructor. econstructor. 
  1:eapply type_cast.
  3:eapply e_Wt.
  3:eauto.
  3:intuition eauto using decoration.
  all:eapply validity_ty_ty, type_inv in e_Wt; dependent destruction e_Wt; eauto.
Qed.

Corollary keep_sort Γ' i j A :
  Γ' ⊨⟨ i ⟩ A : Sort j →
  Γ' ⊨⟨ i ⟩ A : Sort j ⇒ Sort j.
Proof.
  intros h.
  eapply keep_head in h. 2: econstructor.
  destruct h as (A' & h & hA).
  inversion h. subst.
  assumption.
Qed.

Lemma change_type Γ' i t A A' :
  Γ' ⊨⟨ i ⟩ t : A →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ' ⊨⟨ i ⟩ t : A ⇒ A'.
Proof.
  intros.
  destruct H. destruct H. destruct H. destruct H1.
  destruct H0. destruct H3.
  assert (x ~ A') by eauto using dec_to_sim, sim_trans, sim_sym.
  eapply validity_ty_ty in H as x_Wt.
  eapply sim_heq_same_ctx in H5; eauto.
  destruct H5.
  eapply type_hetero_to_homo in H5; eauto.
  eapply type_cast in H. 4:eapply H5.
  2,3:eauto.
  econstructor. econstructor.
  1:eauto.
  split; eauto using decoration.
Qed.

(* New notations for source derivations *)

Notation "Γ ∋< l >× x : T" :=
  (Typing.varty Γ x l T) (at level 50, l, x, T at next level).

Notation "Γ ⊢< l >× t : A" :=
  (Typing.typing Γ l t A) (at level 50, l, t, A at next level).

Notation "Γ ⊢< l >× t ≡ u : T" :=
 (Typing.conversion Γ l t u T) (at level 50, l, t, u, T at next level).

Notation "⊢× Γ" :=
  (Typing.ctx_typing Γ) (at level 50).

(* Translation of derivations *)

Lemma tr_meta Γ' i j t t' A A' B B' :
  Γ' ⊨⟨ i ⟩ t : A ↦ t' : A' →
  i = j →
  A = B →
  A' = B' →
  Γ' ⊨⟨ j ⟩ t : B ↦ t' : B'.
Proof.
  intros h -> -> ->. assumption.
Qed.

Lemma tr_ctx_inv Γ l A Δ :
  tr_ctx (Γ ,, (l, A)) Δ →
  ∃ Γ' A', tr_ctx Γ Γ' ∧ A ⊏ A' ∧ Δ = Γ',, (l, A').
Proof.
  intros [h1 h2].
  eapply Forall2_inv_l in h2 as ((l' & A') & Γ' & ? & (e & ?) & ->).
  cbn in e. subst.
  inversion h1. subst.
  firstorder eauto.
Qed.

Lemma varty_trans Γ Γ' x l A :
  Γ ∋< l >× x : A →
  tr_ctx Γ Γ' →
  ∃ A', Γ' ∋< l > x : A' ∧ A ⊏ A'.
Proof.
  intros hx hc.
  induction hx as [| Γ i j A B x hx ih] in Γ', hc |- *.
  - eapply tr_ctx_inv in hc as (Δ & A' & hc & hA & ->).
    eexists. split.
    + constructor.
    + apply rename_dec. assumption.
  - eapply tr_ctx_inv in hc as (Δ & B' & hc & hB & ->).
    eapply ih in hc. destruct hc as (A' & h & hA).
    eexists. split.
    + econstructor. eassumption.
    + apply rename_dec. assumption.
Qed.

(* TODO MOVE *)
Lemma varty_unique Γ l x A B :
  Γ ∋< l > x : A →
  Γ ∋< l > x : B →
  A = B.
Proof.
  intros hA hB.
  induction hA in B, hB |- *.
  - inversion hB. reflexivity.
  - inversion hB. subst. firstorder congruence.
Qed.

Lemma tr_var_known Γ Γ' x A A' l :
  Γ ∋< l >× x : A →
  Γ' ∋< l > x : A' →
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ l ⟩ var x : A ↦ var x : A'.
Proof.
  intros hx hx1 hc.
  eapply varty_trans in hx as hx2. 2: eassumption.
  destruct hx2 as (A'' & hx2 & hA).
  eapply varty_unique in hx1 as e. 2: eassumption.
  subst.
  split.
  { econstructor. 2: eauto. apply hc. }
  intuition constructor.
Qed.

Lemma tr_var Γ Γ' x A l :
  Γ ∋< l >× x : A →
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ l ⟩ var x : A.
Proof.
  intros hx hc.
  eapply varty_trans in hx as hx'. 2: eassumption.
  destruct hx' as (A' & hx' & hA).
  eexists _,_. split.
  { econstructor. 2: eauto. apply hc. }
  intuition constructor.
Qed.

(* Not ideal, but given circumstances there is not much else we can do. *)

Axiom tr_assm_sig :
  ∀ c A,
    nth_error Typing.assm_sig c = Some A →
    ∃ A',
      nth_error assm_sig c = Some A' ∧ A ⊏ A' ∧ ∙ ⊢< Ax prop > A' : Sort prop.

Lemma tr_ctx_cons Γ Γ' A A' i :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  tr_ctx (Γ ,, (i, A)) (Γ' ,, (i, A')).
Proof.
  intros [hc1 hc2] (? & ? & hs).
  split.
  - econstructor. all: eauto.
  - econstructor. 2: eassumption.
    cbn. intuition auto.
Qed.

Lemma tr_Sort Γ Γ' l :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax (Ax l) ⟩ Sort l : Sort (Ax l) ↦ Sort l : Sort (Ax l).
Proof.
  intros hc.
  split. 2: intuition constructor.
  econstructor. apply hc.
Qed.

Lemma tr_Pi i j Γ' A A' B B' :
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ',, (i, A') ⊨⟨ Ax j ⟩ B : Sort j ↦ B' : Sort j →
  Γ' ⊨⟨ Ax (Ru i j) ⟩ Pi i j A B : Sort (Ru i j) ↦ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros ihA ihB.
  destruct ihA as (? & ? & ?), ihB as (? & ? & ?).
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eauto.
Qed.

Lemma tr_Nat Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 1 ⟩ Nat : Sort (ty 0) ↦ Nat : Sort (ty 0).
Proof.
  intro hc.
  split. 2: intuition constructor.
  constructor.
  apply hc.
Qed.

Lemma tr_zero_full Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat ↦ zero : Nat.
Proof.
  intros hc.
  split. 2: intuition constructor.
  constructor. apply hc.
Qed.

Lemma tr_zero Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat.
Proof.
  intros hc.
  eexists _,_. eapply tr_zero_full. eassumption.
Qed.

Lemma tr_succ_full Γ' t t' :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat ↦ t' : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat ↦ succ t' : Nat.
Proof.
  intros iht.
  destruct iht as (? & ? & ?).
  split. 2: intuition (constructor ; eauto).
  constructor. assumption.
Qed.

Lemma tr_succ Γ' t :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat.
Proof.
  intros iht.
  eapply keep_head in iht. 2: econstructor.
  destruct iht as (? & hh & iht). inversion hh. subst.
  destruct iht as (? & ?).
  eexists _,_. eapply tr_succ_full. eassumption.
Qed.

Definition tr_subst_data Γ' σ σ' Δ' :=
  Γ' ⊢s σ' : Δ' ∧ dec_subst σ σ'.

Notation "Γ ⊨s σ : Δ ⇒ σ'" :=
  (tr_subst_data Γ σ σ' Δ)
  (at level 50, σ, Δ at next level).

Definition tr_subst Γ' σ Δ' :=
  ∃ σ', tr_subst_data Γ' σ σ' Δ'.

Notation "Γ ⊨s σ : Δ" :=
  (tr_subst Γ σ Δ)
  (at level 50, σ, Δ at next level).

#[export] Instance dec_subst_morphism :
  Proper ((`=1`) ==> (`=1`) ==> iff) dec_subst.
Proof.
  intros σ σ' e θ θ' e'.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  intros x. rewrite <- e, <- e'. apply h.
Qed.

#[export] Instance tr_subst_data_morphism :
  Proper (eq ==> (`=1`) ==> (`=1`) ==> eq ==> iff) tr_subst_data.
Proof.
  intros Γ ? <- σ σ' e θ θ' e' Δ ? <-.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  destruct h. split.
  - rewrite <- e'. assumption.
  - rewrite <- e, <- e'. assumption.
Qed.

#[export] Instance tr_subst_morphism :
  Proper (eq ==> (`=1`) ==> eq ==> iff) tr_subst.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  destruct h as [s h]. exists s.
  rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_tr_subst_data :
  ∀ Γ Δ s1 s2 s3 s4,
    SubstSimplification s1 s2 →
    SubstSimplification s3 s4 →
    tr_subst_data Γ s1 s3 Δ ↔ tr_subst_data Γ s2 s4 Δ.
Proof.
  intros * h1 h2.
  apply tr_subst_data_morphism. 1,4: eauto.
  - apply h1.
  - apply h2.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_tr_subst_data : rasimpl_outermost.

Lemma autosubst_simpl_tr_subst :
  ∀ Γ Δ s1 s2,
    SubstSimplification s1 s2 →
    tr_subst Γ s1 Δ ↔ tr_subst Γ s2 Δ.
Proof.
  intros * h.
  apply tr_subst_morphism. 1,3: eauto.
  apply h.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_tr_subst : rasimpl_outermost.

Lemma tr_subst_scons l Γ' Δ' σ σ' A A' u u' :
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ l ⟩ u : A <[ σ ] ↦ u' : A' <[ σ' ] →
  Γ' ⊨s (u .: σ) : Δ' ,, (l, A') ⇒ (u' .: σ').
Proof.
  intros [hs1 hs2] [hu1 hu2].
  split.
  - apply well_scons_alt. all: eauto.
  - apply dec_subst_scons. all: intuition eauto.
Qed.

Lemma tr_subst_ren Γ Γ' Δ' ρ :
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨s (ρ >> var) : Δ' ⇒ (ρ >> var).
Proof.
  intros hc hr.
  split. 2: apply dec_subst_refl.
  2:{intros. unfold ">>". econstructor. }
  apply WellSubst_ren.
  - assumption.
  - apply hc.
Qed.

Lemma tr_subst_one Γ' i A A' u u' :
  Γ' ⊨⟨ i ⟩ u : A ↦ u' : A' →
  Γ' ⊨s u .. : Γ' ,, (i, A') ⇒ (u' ..).
Proof.
  intros hu.
  split.
  - apply subst_one. apply hu.
  - apply dec_subst_one. apply hu.
Qed.

Lemma tr_rename l Γ Γ' Δ' t t' A A' ρ :
  Δ' ⊨⟨ l ⟩ t : A ↦ t' : A' →
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨⟨ l ⟩ ρ ⋅ t : ρ ⋅ A ↦ ρ ⋅ t' : ρ ⋅ A'.
Proof.
  intros ht hc hr.
  destruct ht.
  split.
  - eapply typing_conversion_ren. all: eauto. apply hc.
  - intuition eauto using rename_dec.
Qed.

Lemma tr_rename_sort l Γ Γ' Δ' i A A' ρ :
  Δ' ⊨⟨ l ⟩ A : Sort i ↦ A' : Sort i →
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨⟨ l ⟩ ρ ⋅ A : Sort i ↦ ρ ⋅ A' : Sort i.
Proof.
  intros ht hc hr.
  eapply tr_rename in ht. 2,3: eauto.
  assumption.
Qed.

Lemma tr_substitution i Γ Γ' t t' A A' Δ' σ σ' :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ t : A ↦ t' : A' →
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ i ⟩ t <[ σ ] : A <[ σ ] ↦ t' <[ σ' ] : A' <[ σ' ].
Proof.
  intros hc ht hs.
  destruct ht as (? & ? & ?), hs as (? & ?).
  split. 2: intuition eauto using substs_decs.
  eapply typing_conversion_subst.
  - eassumption.
  - apply hc.
  - assumption.
Qed.

Corollary tr_substitution_sort i Γ Γ' A A' l Δ' σ σ' :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ A : Sort l ↦ A' : Sort l →
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ i ⟩ A <[ σ ] : Sort l ↦ A' <[ σ' ] : Sort l.
Proof.
  intros hc ht hs.
  eapply tr_substitution in hs. 2,3: eassumption.
  assumption.
Qed.

Corollary tr_substitution_one i j Γ Γ' t t' u u' A A' B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ t : A ↦ t' : A' →
  Γ' ⊨⟨ j ⟩ u : B ↦ u' : B' →
  Γ' ⊨⟨ i ⟩ t <[ u .. ] : A <[ u .. ] ↦ t' <[ u' .. ] : A' <[ u' .. ].
Proof.
  intros hc ht hu.
  eapply tr_substitution. 1,2: eassumption.
  eapply tr_subst_one. eassumption.
Qed.

Corollary tr_substitution_one_sort i j Γ Γ' A A' u u' l B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ A : Sort l ↦ A' : Sort l →
  Γ' ⊨⟨ j ⟩ u : B ↦ u' : B' →
  Γ' ⊨⟨ i ⟩ A <[ u .. ] : Sort l ↦ A' <[ u' .. ] : Sort l.
Proof.
  intros hc ht hu.
  eapply tr_substitution_one in hu. 2,3: eassumption.
  assumption.
Qed.

Lemma tr_acc Γ' n A A' R R' a a' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ,, (ty n, A'),, (ty n, S ⋅ A') ⊨⟨ Ax prop ⟩ R : Sort prop ↦ R' : Sort prop →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ Ax prop ⟩ acc (ty n) A R a : Sort prop ↦ acc (ty n) A' R' a' : Sort prop.
Proof.
  intros ihA ihR iha.
  destruct
    ihA as (? & ? & _),
    ihR as (? & ? & _),
    iha as (? & ? & _).
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eauto.
Qed.

Lemma tr_obseq Γ' n A A' a a' b b' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ ty n ⟩ b : A ↦ b' : A' →
  Γ' ⊨⟨ Ax prop ⟩ obseq (ty n) A a b : Sort prop ↦ obseq (ty n) A' a' b' : Sort prop.
Proof.
  intros ihA iha ihb.
  destruct ihA, iha, ihb.
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eassumption.
Qed.

Lemma tr_obsrefl Γ' n A A' a a' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ prop ⟩ obsrefl (ty n) A a : obseq (ty n) A a a ↦ obsrefl (ty n) A' a' : obseq (ty n) A' a' a'.
Proof.
  intros ihA iha.
  destruct ihA, iha.
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eassumption.
Qed.

Lemma typing_conversion_trans :
  (∀ Γ l t A,
    Γ ⊢< l >× t : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      Γ' ⊨⟨ l ⟩ t : A
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l >× u ≡ v : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      Γ ⊨⟨ l ⟩ u ≡ v : A
  ).
Proof.
  apply Typing.typing_mutind.

  (* Typing rules *)

  - intros * ? hx ? hc.
    eapply tr_var. all: eassumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_Sort. eassumption.
  - intros * ? e ? ih ? hc.
    eapply tr_assm_sig in e as e'. destruct e' as (A' & e' & ? & ?).
    eexists _, (assm _). split.
    { econstructor. 2,3: eassumption. apply hc. }
    intuition constructor.
  - intros * ? ihA ? ihB ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    eexists _,_. eapply tr_Pi. all: eassumption.
  - intros * ? ihA ? ihB ? iht ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    specialize iht with (1 := hca).
    eapply change_type in iht. 2: eassumption.
    destruct iht as (t' & iht).
    destruct ihA as (? & ? & _), ihB as (? & ? & _), iht as (? & ? & _).
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihB ? iht ? ihu ? hc.
    specialize ihA with (1 := hc).
    eapply keep_sort in ihA. destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca).
    eapply keep_sort in ihB. destruct ihB as (B' & ihB).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Pi. all: eassumption. }
    destruct iht as (t' & iht).
    specialize ihu with (1 := hc).
    eapply change_type in ihu. 2: eassumption.
    destruct ihu as (u' & ihu).
    destruct
      ihA as (? & ? & _),
      ihB as (? & ? & _),
      iht as (? & ? & _),
      ihu as (? & ? & _).
    eexists _,_. split. 2: split. 2: constructor ; eauto.
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: assumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_Nat. eassumption.
  - intros * ?? hc. eapply tr_zero. eassumption.
  - intros * ? iht ? hc.
    specialize iht with (1 := hc).
    eapply tr_succ. assumption.
  - intros * ? ihP ? ihz ? ihs ? iht ? hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Nat. eassumption. }
    destruct iht as (?t' & iht).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _),
      iht as (? & ? & _).
    eexists _,_. split. 2: split. 2: constructor ; eauto.
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: assumption.
  - intros * ? ihA ? ihR ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct ihR as [R' ihR], iha as [a' iha].
    eexists _,_.
    eapply tr_acc. all: eassumption.
  - intros * ? ihA ? ihR ? iha. cbn zeta. intros ? ihp ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    eapply tr_ctx_cons in hca as hcar.
    2:{
      eapply tr_substitution_sort. 1,2: eauto.
      eapply tr_subst_scons with (A := S ⋅ A).
      1: eapply tr_subst_scons with (A := A).
      - eapply tr_subst_ren. 1: eassumption.
        apply WellRen_S.
      - rasimpl. eapply tr_var_known. 3: eassumption.
        + eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        + eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      - rasimpl. eapply tr_rename. 1,2: eassumption.
        apply WellRen_S.
    }
    eapply tr_ctx_cons with (A := (S >> S) ⋅ A) in hcar as hcara.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply WellRen_weak. apply WellRen_S.
    }
    specialize ihp with (1 := hc).
    eapply change_type in ihp.
    2:{
      eapply tr_meta.
      { eapply tr_Pi. 1: eassumption.
        eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_substitution_sort. 1,2: eauto.
            eapply tr_subst_scons with (A := S ⋅ A).
            + eapply tr_subst_scons with (A := A).
              * eapply tr_subst_ren. 1: eassumption.
                apply WellRen_S.
              * {
                eapply tr_var_known. 3: eassumption.
                - eapply BasicMetaTheory.varty_meta.
                  { repeat econstructor. }
                  rasimpl. reflexivity.
                - eapply varty_meta.
                  { repeat econstructor. }
                  rasimpl. reflexivity.
              }
            + rasimpl. eapply tr_rename. 1,2: eauto.
              apply WellRen_S.
          - eapply tr_acc.
            + eapply tr_rename_sort. 1,2: eassumption.
              apply WellRen_weak. apply WellRen_S.
            + eapply tr_rename_sort. 1: eauto.
              * eapply tr_ctx_cons. 1: eassumption.
                rasimpl. eapply tr_rename_sort. 1,2: eassumption.
                do 2 apply WellRen_weak. apply WellRen_S.
              * apply WellRen_up. 2:{ rasimpl. reflexivity. }
                apply WellRen_up. 2: reflexivity.
                apply WellRen_weak. apply WellRen_S.
            + eapply tr_var_known. 3: eassumption.
              * eapply BasicMetaTheory.varty_meta.
                { repeat econstructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat econstructor. }
                rasimpl. reflexivity.
        }
        all: reflexivity.
      }
      all: reflexivity.
    }
    destruct ihp as [p' ihp].
    destruct ihA, ihR, iha, ihp.
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihR ? iha ? ihp ? ihb ? ihr ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihp with (1 := hc).
    eapply change_type in ihp. 2:{ eapply tr_acc. all: eauto. }
    destruct ihp as [p' ihp].
    specialize ihb with (1 := hc).
    eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    specialize ihr with (1 := hc).
    eapply change_type in ihr.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply tr_subst_scons with (A := S ⋅ A).
      - eapply tr_subst_one. eassumption.
      - rasimpl. eassumption.
    }
    destruct ihr as [r' ihr].
    destruct ihA, ihR, iha, ihp, ihb, ihr.
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros ?? l * ? ihA ? ihR ? ihP. cbn zeta. intros ? ihp ? iha ? ihq ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    lazymatch type of ihp with
    | ∀ G', tr_ctx ?G G' → _ => eassert (hcap : tr_ctx G _)
    end.
    { eapply tr_ctx_cons. 1: eassumption.
      eapply tr_Pi.
      - eapply tr_rename_sort. 1,2: eassumption.
        apply WellRen_S.
      - eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_rename_sort. 1,2: eassumption.
            apply well_rcons_alt. 1: apply well_rcons_alt.
            + apply WellRen_weak. apply WellRen_S.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
          - eapply tr_rename_sort. 1: eassumption.
            + eapply tr_ctx_cons. 1: eassumption.
              eapply tr_rename_sort. 1,2: eassumption.
              apply well_rcons_alt. 1: apply well_rcons_alt.
              * apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
            + apply well_rcons_alt.
              * do 2 apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
        }
        all: destruct l ; reflexivity.
    }
    specialize ihp with (1 := hcap).
    eapply change_type in ihp.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply well_rcons_alt.
      - apply WellRen_weak. apply WellRen_S.
      - eapply varty_meta.
        { repeat constructor. }
        rasimpl. reflexivity.
    }
    destruct ihp as [p' ihp].
    specialize ihq with (1 := hc).
    eapply change_type in ihq. 2:{ eapply tr_acc. all: eauto. }
    destruct ihq as [q' ihq].
    destruct ihA, ihR, ihP, iha, ihp, ihq.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: intuition assumption.
  - intros * ? ihA ? iha ? ihb ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihb with (1 := hc). eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    eexists _,_. eapply tr_obseq. all: eassumption.
  - intros * ? ihA ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    eexists _,_. eapply tr_obsrefl. all: eassumption.
  - intros * ? ihA ? iha ? ihP ? ihp ? ihb ? ihe ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihb with (1 := hc). eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize ihp with (1 := hc).
    eapply change_type in ihp.
    2:{ eapply tr_substitution_one_sort. all: eassumption. }
    destruct ihp as [p' ihp].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{ eapply tr_obseq. all: eassumption. }
    destruct ihe as [e' ihe].
    destruct ihA, iha, ihP, ihp, ihb, ihe.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: intuition assumption.
  - intros * ? ihA ? ihB ? ihe ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize ihB with (1 := hc). eapply keep_sort in ihB.
    destruct ihB as [B' ihB].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq. 2,3: eassumption.
      eapply tr_Sort. eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    destruct ihA, ihB, ihe, iha.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition eauto.
  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? hc.
    specialize ihA1 with (1 := hc). eapply keep_sort in ihA1.
    destruct ihA1 as [A1' ihA1].
    eapply tr_ctx_cons in hc as hca1. 2: eassumption.
    specialize ihB1 with (1 := hca1). eapply keep_sort in ihB1.
    destruct ihB1 as [B1' ihB1].
    specialize ihA2 with (1 := hc). eapply keep_sort in ihA2.
    destruct ihA2 as [A2' ihA2].
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2). eapply keep_sort in ihB2.
    destruct ihB2 as [B2' ihB2].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq.
      - eapply tr_Sort. eassumption.
      - eapply tr_Pi. all: eassumption.
      - eapply tr_Pi. all: eassumption.
    }
    destruct ihe as [e' ihe].
    destruct ihA1, ihB1, ihA2, ihB2, ihe.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition (constructor ; eauto).
  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? iha2. cbn zeta. intros ? hc.
    specialize ihA1 with (1 := hc). eapply keep_sort in ihA1.
    destruct ihA1 as [A1' ihA1].
    eapply tr_ctx_cons in hc as hca1. 2: eassumption.
    specialize ihB1 with (1 := hca1). eapply keep_sort in ihB1.
    destruct ihB1 as [B1' ihB1].
    specialize ihA2 with (1 := hc). eapply keep_sort in ihA2.
    destruct ihA2 as [A2' ihA2].
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2). eapply keep_sort in ihB2.
    destruct ihB2 as [B2' ihB2].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq.
      - eapply tr_Sort. eassumption.
      - eapply tr_Pi. all: eassumption.
      - eapply tr_Pi. all: eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha2 with (1 := hc). eapply change_type in iha2. 2: eassumption.
    destruct iha2 as [a2' iha2].
    destruct ihA1, ihB1, ihA2, ihB2, ihe, iha2.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + constructor.
      * constructor.
      * eapply substs_decs_one. all: intuition (repeat constructor ; eauto).
      * eapply substs_decs_one. all: intuition eauto.
  - intros * ? iht ? ihAB ? hc.
    admit.

  (* Conversion rules *)

  - intros * ??? hc. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

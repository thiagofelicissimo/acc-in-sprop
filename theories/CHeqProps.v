From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Contexts Typing TypingP BasicMetaTheory BasicMetaTheoryP TypeUniquenessP Fundamental.
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

Axiom homo_to_hetero : forall (l : level) (A t u e : term), term.

Axiom type_homo_to_hetero : forall n Γ t u A e,
  Γ ⊢< ty n > t : A ->
  Γ ⊢< ty n > u : A ->
  Γ ⊢< prop > e : obseq (ty n) A t u ->
  Γ ⊢< prop > homo_to_hetero (ty n) A t u e : heq (ty n) A A t u.  

Axiom type_hetero_to_type : forall n Γ t u A B e,
  Γ ⊢< ty n > t : A ->
  Γ ⊢< ty n > u : B ->
  Γ ⊢< prop > e : heq (ty n) A B t u ->
  exists e', Γ ⊢< prop > e' : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) A B.

Axiom heq_funext : forall (i j : level) (A B1 B2 t u e : term), term.

Axiom type_heq_funext : forall Γ i j A B1 B2 t u e,
  Γ ⊢< Ru i j > t : Pi i j A B1 →
  Γ ⊢< Ru i j > u : Pi i j A B2 →
  let t_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B1) (S ⋅ t) (var 0) in
  let u_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B2) (S ⋅ u) (var 0) in
  Γ ,, (i , A) ⊢< prop > e : heq j B1 B2 t_app_x u_app_x ->
  Γ ⊢< prop > heq_funext i j A B1 B2 t u e : heq (Ru i j) (Pi i j A B1) (Pi i j A B2) t u.
(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.


(* I first tried to defined ⊢ t -->>! u by |t| -->>! |u| and ⊢ t ≡ u.
   The problem is that if ⊢ A -->>! Pi S T and ⊢ A -->>! A', then we know that
   A' = Pi S' T' with |S| = |S'| and |T| = |T'| and ⊢ Pi S T ≡ Pi S' T',
   but we cannot conclude that S ≡ S' and T ≡ T'. This poses problems
   when showing irrelevance of the logical relation, because we can only
   exchange types which are convertible and equal wrt |-| *)


Reserved Notation "Γ ⊢< l > t --> u : T" (at level 50, l, t, u, T at next level).
    
Definition val t := 
    match t with 
    | app i j A B t u => False
    | rec i P pzero psucc n => False 
    | accel _ _ A R a q P p => False
    | cast _ _ _ _ _ => False
    | _ => True 
    end.

Inductive red  : ctx -> level -> term -> term -> term -> Prop :=
| red_app Γ t t' u i j A B :
    Γ ⊢< Ax i > A : Sort i -> 
    Γ ,, (i, A) ⊢< Ax j > B : Sort j -> 
    Γ ⊢< Ru i j > t --> t' : Pi i j A B -> 
    Γ ⊢< i > u : A ->
    Γ ⊢< j > app i j A B t u --> app i j A B t' u : B <[ u..]

| red_beta Γ t u i j A B A' B' : 
    Γ ⊢< Ax i > A ≡ A' : Sort i -> 
    Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j -> 
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< i > u : A →
    Γ ⊢< j > app i j A B (lam i j A' B' t) u --> t <[ u.. ] : B <[ u..]

| red_rec Γ l P p_zero p_succ n n' :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->    
    Γ ⊢< ty 0 > n --> n' : Nat -> 
    Γ ⊢< l > rec l P p_zero p_succ n --> rec l P p_zero p_succ n' : P <[ n.. ]

| red_rec_zero Γ l P p_zero p_succ :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< l > rec l P p_zero p_succ zero --> p_zero : P <[ zero .. ]

| red_rec_succ Γ l P p_zero p_succ n :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< ty 0 > n : Nat ->
    Γ ⊢< l > rec l P p_zero p_succ (succ n) --> p_succ <[  (rec l P p_zero p_succ n) .: n ..] : P <[ (succ n) .. ]

| red_accel Γ i l A R a q P p : 
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
    Γ ⊢< l > accel i l A R P p a q --> p <[ t5 .: a ..] : P <[a ..]

| red_conv Γ l t u A B :
    Γ ⊢< l > t --> u : A ->
    Γ ⊢< Ax l > A ≡ B : Sort l -> 
    Γ ⊢< l > t --> u : B

| red_cast1 Γ i A A' B e a :
    Γ ⊢< Ax i > A --> A' : Sort i ->
    Γ ⊢< Ax i > B : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< i > cast i A B e a --> cast i A' B e a : B

| red_cast2 Γ i A B B' e a :
    Γ ⊢< Ax i > A : Sort i ->
    val A ->
    Γ ⊢< Ax i > B --> B' : Sort i ->
    Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A -> 
    Γ ⊢< i > cast i A B e a --> cast i A B' e a : B

| red_cast_nat Γ e t : 
    Γ ⊢< prop > e : obseq (ty 1) (Sort (ty 0)) Nat Nat -> 
    Γ ⊢< ty 0 > t : Nat ->
    Γ ⊢< ty 0 > cast (ty 0) Nat Nat e t --> t : Nat 

| red_cast_sort Γ i A e :
    Γ ⊢< Ax i > A : Sort i -> 
    Γ ⊢< prop > e : obseq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) ->
    Γ ⊢< Ax i > cast (Ax i) (Sort i) (Sort i) e A --> A : Sort i

| red_cast_pi Γ i j A1 A2 B1 B2 e f :
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
    Γ ⊢< Ru i j > cast (Ru i j) (Pi i j A1 B1) (Pi i j A2 B2) e f --> t4 : Pi i j A2 B2
    
where "Γ ⊢< l > t --> u : T" := (red Γ l t u T).

Lemma red_meta_conv Γ u v l A B w :
  Γ ⊢< l > u --> v : A →
  A = B →
  v = w →
  Γ ⊢< l > u --> w : B.
Proof.
  intros. subst. assumption.
Qed.


Lemma red_accel' Γ i l A R a q P p X Y : 
    Γ ,, (i, A) ⊢< Ax l > P : Sort l ->
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
    Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' ->
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
    X = p <[ t5 .: a ..] ->
    Y = P <[a ..] ->
    Γ ⊢< l > accel i l A R P p a q --> X : Y.
Proof.
    intros. subst. 
    eapply validity_ty_ty in H1 as temp. 
    eapply type_inv_acc' in temp as (_ & AWt & RWt & aWt & _).
    eauto using red_accel.
Qed.




Lemma red_to_conv Γ l t u A :
    Γ ⊢< l > t --> u : A -> Γ ⊢< l > t ≡ u : A.
Proof.
    intros. induction H; eauto using conversion, refl_ty.
    - eapply conv_trans. eapply conv_app. 
      1,2:(eapply refl_ty; eauto using validity_conv_left).
      2: eauto using refl_ty.
      eapply conv_conv. eapply conv_lam; eauto using refl_ty, conv_sym, conv_ty_in_ctx_conv, type_conv.
      eapply conv_pi; eauto using conv_ty_in_ctx_conv, conv_sym.
      eauto using conv_beta, validity_conv_left.
    - eapply conv_cast_refl; eauto using conv_nat, validity_ty_ctx.
    - eapply conv_cast_refl; eauto using conv_sort, validity_ty_ctx. 
Qed.

Lemma red_app' Γ t t' u i j A B X Y :
    Γ ⊢< Ru i j > t --> t' : Pi i j A B -> 
    Γ ⊢< i > u : A ->
    X = app i j A B t' u -> 
    Y = B <[ u..] ->
    Γ ⊢< j > app i j A B t u --> X : Y.
Proof.
    intros. subst.
    eapply red_to_conv in H as temp.  eapply validity_conv_left in temp. eapply validity_ty_ty in temp.
    eapply type_inv_pi' in temp as (_ & Awt & BWt & _).
    eapply red_app; eauto.
Qed.

Lemma red_beta' Γ t u i j A B A' B' X Y : 
    Γ ⊢< Ax i > A ≡ A' : Sort i -> 
    Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j -> 
    Γ ,, (i , A) ⊢< j > t : B →
    Γ ⊢< i > u : A →
    X = t <[ u.. ] ->
    Y = B <[ u..] ->
    Γ ⊢< j > app i j A B (lam i j A' B' t) u --> X : Y.
Proof.
    intros. subst. eapply red_beta; eauto.
Qed.

Reserved Notation "Γ ⊢< l > t -->> u : T" (at level 50, l, t, u, T at next level).

Inductive redd : ctx -> level -> term -> term -> term -> Prop := 
  | redd_refl Γ l t A : Γ ⊢< l > t : A -> Γ ⊢< l > t -->> t : A 
  | redd_step Γ l t u v A : Γ ⊢< l > t --> v : A -> Γ ⊢< l > v -->> u : A -> Γ ⊢< l > t -->>u : A 
where "Γ ⊢< l > t -->> t' : A " := (redd Γ l t t' A).


Definition whnf Γ l t A := forall u, Γ ⊢< l > t --> u : A -> False.


Definition redd_whnf Γ l t t' A := redd Γ l t t' A /\ whnf Γ l t' A.

Notation "Γ ⊢< l > t -->>! u : T" := (redd_whnf Γ l t u T) (at level 50, l, t, u, T at next level).

Lemma redd_to_conv Γ l t u A :
    Γ ⊢< l > t -->> u : A -> Γ ⊢< l > t ≡ u : A.
Proof.
    intros. induction H; eauto using refl_ty, conv_trans, red_to_conv.
Qed.

Lemma redd_whnf_to_conv Γ l t u A :
    Γ ⊢< l > t -->>! u : A -> Γ ⊢< l > t ≡ u : A.
Proof.
    intros. destruct H.  eauto using redd_to_conv. 
Qed.

Lemma redd_trans Γ l t u v A :
    Γ ⊢< l > t -->> v : A -> 
    Γ ⊢< l > v -->> u : A ->
    Γ ⊢< l > t -->> u : A.
Proof.
    intros. induction H; eauto.
    eapply redd_step; eauto.
Qed.

Lemma redd_comp_redd_whnf Γ l t u v A :
    Γ ⊢< l > t -->> v : A -> 
    Γ ⊢< l > v -->>! u : A ->
    Γ ⊢< l > t -->>! u : A.
Proof.
    intros. destruct H0. 
    split; eauto using redd_trans.
Qed.

Lemma redd_app Γ i j A B t t' u :
    Γ ⊢< Ru i j > t -->> t' : Pi i j A B -> 
    Γ ⊢< i > u : A ->
    Γ ⊢< j > app i j A B t u -->> app i j A B t' u : B <[ u.. ].
Proof.
    intros. eapply redd_to_conv in H as H'. 
    eapply validity_conv_left in H'. eapply validity_ty_ty in H'.
    eapply type_inv_pi in H' as (AWt & BWt).
    dependent induction H.
    - eapply redd_refl. eauto using type_app.
    - eapply redd_step; eauto using red_app.
Qed.

Lemma red_to_redd Γ l t u A :
    Γ ⊢< l > t --> u : A -> 
    Γ ⊢< l > t -->> u : A.
Proof.
    intros. eapply red_to_conv in H as temp.
    eapply validity_conv_right in temp.
    eapply redd_step; eauto.
    eapply redd_refl. eauto.
Qed.

Lemma redd_conv Γ l t u B A :
    Γ ⊢< l > t -->> u : A -> 
    Γ ⊢< Ax l > A ≡ B : Sort l -> 
    Γ ⊢< l > t -->> u : B.
Proof.
    intros. induction H.
    - eapply redd_refl; eauto using type_conv.
    - eapply redd_step; eauto. eauto using red_conv.
Qed.

Lemma redd_rec Γ l P p_zero p_succ n n' :
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->    
    Γ ⊢< ty 0 > n -->> n' : Nat -> 
    Γ ⊢< l > rec l P p_zero p_succ n -->> rec l P p_zero p_succ n' : P <[ n.. ].
Proof.
    intros. dependent induction H2.
    - eapply redd_refl. eauto using type_rec.
    - eapply redd_step; eauto using red_rec. 
      eapply redd_conv. eapply IHredd; eauto.
      eauto 6 using subst, refl_ty, red_to_conv, conv_sym, aux_subst.
Qed.


Lemma redd_rec_zero  Γ l P p_zero p_succ t : 
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< ty 0 > t -->> zero : Nat ->
    Γ ⊢< l > rec l P p_zero p_succ t -->> p_zero : P <[ zero .. ].
Proof.
    intros.
    dependent induction H2.
    - eapply red_to_redd. eapply red_rec_zero; eauto.
    - eapply redd_step. eapply red_conv. eapply red_rec; eauto. 
      eauto 7 using subst, refl_ty, redd_to_conv, red_to_conv, conv_trans, aux_subst, conv_sym.
      eapply IHredd; eauto.
Qed.

Lemma redd_rec_succ  Γ l P p_zero p_succ t n : 
    Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
    Γ ⊢< l > p_zero : P <[ zero .. ] -> 
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢< ty 0 > t -->> succ n : Nat ->
    Γ ⊢< l > rec l P p_zero p_succ t -->> p_succ <[  (rec l P p_zero p_succ n) .: n ..] : P <[ (succ n) .. ].
Proof.
    intros.
    dependent induction H2.
    - eapply red_to_redd. eapply type_inv_succ' in H2 as (_ & nWt & _). eapply red_rec_succ; eauto.
    - eapply redd_step. eapply red_conv. eapply red_rec; eauto. 
      eauto 7 using subst, refl_ty, redd_to_conv, red_to_conv, conv_trans, aux_subst, conv_sym.
      eapply IHredd; eauto.
Qed.


Definition red_inv_type Γ t v :=
    match t with 
    | app i j A B (lam i' j' A' B' t) u => 
        i = i' /\ 
        j = j' /\
        v = t <[ u.. ] /\ 
        Γ ⊢< Ax i > A ≡ A' : Sort i /\
        Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j /\
        Γ ,, (i , A) ⊢< j > t : B /\ 
        Γ ⊢< i > u : A 
    | app i j A B t u =>
        exists t', 
            v = app i j A B t' u /\
            Γ ⊢< Ax i > A : Sort i /\ 
            Γ ,, (i, A) ⊢< Ax j > B : Sort j /\
            Γ ⊢< Ru i j > t --> t' : Pi i j A B /\
            Γ ⊢< i > u : A
    | rec l P p_zero p_succ zero => 
        v = p_zero /\ 
        Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
        Γ ⊢< l > p_zero : P <[ zero .. ] /\
        Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]
    | rec l P p_zero p_succ (succ n) => 
        v = p_succ <[  (rec l P p_zero p_succ n) .: n ..] /\
        Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
        Γ ⊢< l > p_zero : P <[ zero .. ] /\
        Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
        Γ ⊢< ty 0 > n : Nat
    | rec l P p_zero p_succ n => 
        exists n',
            v = rec l P p_zero p_succ n' /\
            Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
            Γ ⊢< l > p_zero : P <[ zero .. ] /\
            Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
            Γ ⊢< ty 0 > n --> n' : Nat
    | accel i l A R P p a q =>  
    let R' := R <[var 1 .: (var 0 .: (S >> S >> var))] in
    let P' := P <[var 1 .: (S >> S >> S >> var)] in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := P <[var 1.: (S >> (S >> var))] in
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
        v = p <[ t5 .: a ..] /\ 
        Γ ⊢< Ax i > A : Sort i /\
        Γ ,, (i, A) ,, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop /\ 
        Γ ,, (i, A) ⊢< Ax l > P : Sort l /\
        Γ ,, (i, A) ,, (Ru i l, B) ⊢< l > p : P'' /\
        Γ ⊢< i > a : A /\ 
        Γ ⊢< prop > q : acc i A R a
    | cast _ Nat Nat e t => 
        v = t /\
        Γ ⊢< prop > e : obseq (ty 1) (Sort (ty 0)) Nat Nat /\
        Γ ⊢< ty 0 > t : Nat
    | cast l (Sort i) (Sort j) e A => 
        v = A /\ 
        Γ ⊢< Ax i > A : Sort i /\
        Γ ⊢< prop > e : obseq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) /\
        i = j /\ 
        l = Ax i
    | cast l (Pi i j A1 B1) (Pi i' j' A2 B2) e f => 
        let A1' := S ⋅ A1 in
        let A2' := S ⋅ A2 in 
        let B1' := (up_ren S) ⋅ B1 in 
        let B2' := (up_ren S) ⋅ B2 in
        let t1 := cast i A2' A1' (injpi1 i j A1' A2' B1' B2' (S ⋅ e)) (var 0) in
        let t2 := app i j A1' B1' (S ⋅ f) t1 in 
        let t3 := cast j (B1 <[t1.: S >> var]) B2 (injpi2 i j A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in 
        let t4 := lam i j A2 B2 t3 in 
        v = t4 /\
        Γ ⊢< Ax i > A1 : Sort i /\
        Γ ,, (i, A1) ⊢< Ax j > B1 : Sort j /\
        Γ ⊢< Ax i > A2 : Sort i /\
        Γ ,, (i, A2) ⊢< Ax j > B2 : Sort j /\
        Γ ⊢< prop > e : obseq (Ax (Ru i j)) (Sort (Ru i j)) (Pi i j A1 B1) (Pi i j A2 B2) /\
        Γ ⊢< Ru i j > f : Pi i j A1 B1 /\
        l = Ru i j /\ 
        i' = i /\ 
        j' = j

    | cast i A B e t => 
        (exists A',
            v = cast i A' B e t /\
            Γ ⊢< Ax i > A --> A' : Sort i /\
            Γ ⊢< Ax i > B : Sort i /\
            Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B /\ 
            Γ ⊢< i > t : A) \/ 
        (exists B', 
            v = cast i A B' e t /\ 
            val A /\
            Γ ⊢< Ax i > B --> B' : Sort i /\
            Γ ⊢< Ax i > A : Sort i /\
            Γ ⊢< prop > e : obseq (Ax i) (Sort i) A B /\ 
            Γ ⊢< i > t : A)
    | _ => False
    end.

Fixpoint size (t : term) : nat := 
  match t with 
  | var _ => 0
  | Sort _ => 0
  | Pi _ _ A B => 1 + size A + size B
  | lam _ _ A B t => 1 + size A + size B + size t
  | app _ _ A B t u => 1 + size A + size B + size t + size u
  | Nat => 0
  | zero => 0
  | succ t => 1 + size t
  | rec _ P p0 ps t => 1 + size P + size p0 + size ps + size t
  | accel _ _ A R a q P p => 1 + size A + size R + size a + size q + size P + size p 
  | acc _ A R a => 1 + size A + size R + size a 
  | cast _ A B e t => 1 + size A + size B + size e + size t 
  | obseq _ A a b => 1 + size A + size a + size b
  | _ => 0
end.


Lemma red_inv Γ l t u T : Γ ⊢< l > t --> u : T -> red_inv_type Γ t u.
Proof.
    generalize t Γ l u T. clear t Γ l u T.
    refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _). 
    eauto using wf_inverse_image, lt_wf.
    intros. induction H0.
    - destruct t.
      5: (unshelve eapply (H _ _) in H2; simpl). 5: lia. 5: inversion H2.
      all: simpl.
      all: eexists; eauto. 
    - simpl. split; eauto. split; eauto.
    - destruct n.
      8,9 :(unshelve eapply (H _ _) in H3; simpl). 8,9: lia. 8,9: inversion H3.
      all: simpl.
      all: eexists; eauto.
    - simpl. split; eauto. 
    - simpl. split; eauto.
    - simpl. split; eauto. split; eauto.
    - eapply IHred. eauto.
    - destruct A.
      1,3,5,6,8-18: simpl;left;eexists; split; eauto.
      1-3:(unshelve eapply (H _ _) in H0); simpl. 1-3:lia. 1-3:inversion H0.
    - destruct B.
      1,3,5,6,8-18:destruct A; simpl; right; eexists; split; eauto.
      1-3:(unshelve eapply (H _ _) in H2); simpl. 1-3:lia. 1-3:inversion H2.
    - simpl. split; eauto.
    - simpl. split; eauto.
    - simpl. split; eauto. split; eauto. split; eauto. split; eauto. split; eauto.
Qed.

Lemma val_whnf Γ l t A : val t -> whnf Γ l t A.
Proof.
    intros. unfold whnf. intros.
    destruct t.
    all:eapply red_inv in H0.
    6, 10,14,16:inversion H.
    all: simpl in H0; dependent destruction H0.
Qed.

Hint Unfold val.


Lemma red_det Γ l t u v A : 
    Γ ⊢< l > t --> u : A -> 
    Γ ⊢< l > t --> v : A ->
    u = v.
Proof.
    intros. 
    generalize v H0. clear v H0. induction H; intros.
    - apply red_inv in H3. destruct t. 
      5: (apply red_inv in H1; inversion H1).
      all: destruct H3 as (t'' & eq & _ & _ & red & _). all: eapply IHred in red. all: subst. all: eauto.
    - apply red_inv in H3 as (_ & _ & eq & _). eauto.
    - apply red_inv in H3. destruct n.
      8,9 : (apply red_inv in H2; inversion H2).
      all: destruct H3 as (n'' & eq & _ & _ & _ & red). all: eapply IHred in red. all: subst. all: eauto.
    - apply red_inv in H2 as (eq & _). eauto.
    - apply red_inv in H3 as (eq & _). eauto.
    - apply red_inv in H5 as (eq & _). eauto.
    - eapply IHred. eapply red_conv; eauto using conv_sym.
    - destruct A.
      6,10,14,16:eapply red_inv in H3; simpl in H3; destruct H3 as [ (A_ & eq & red & _) | (A_ & eq & false & red & _)]; 
        try inversion false; eapply IHred in red; subst; eauto.
      all: eapply red_inv in H; simpl in H; dependent destruction H.
    - destruct B.
      6,10,14,16:destruct A; eapply red_inv in H4; simpl in H4; destruct H4 as [ (A_ & eq & red1 & _) | (A_ & eq & _ & red2 & _)];
        try eapply val_whnf in red1 ; eauto; try inversion red1; try eapply IHred in red2; subst; eauto.
      all: eapply red_inv in H1; simpl in H1; dependent destruction H1.
    - eapply red_inv in H1. destruct H1. eauto.
    - eapply red_inv in H1. destruct H1. eauto.
    - eapply red_inv in H5. destruct H5. eauto.
Qed.

Lemma redd_whnf_det Γ l t u v A : 
    Γ ⊢< l > t -->>! u : A -> 
    Γ ⊢< l > t -->>! v : A ->
    u = v.
Proof.
    intros. destruct H. generalize v H0. clear v H0. induction H; intros.
    - destruct H0. dependent destruction H0.
        + eauto.
        + eapply H1 in H0. inversion H0.
    - destruct H2. dependent destruction H2.
        + apply H3 in H. inversion H.
        + eapply red_det in H; eauto. subst.
          apply IHredd; eauto. split; eauto.
Qed.


Lemma val_redd_to_whnf Γ l t A : Γ ⊢< l > t : A -> val t -> Γ ⊢< l > t -->>! t : A.
Proof.
    intros.
    split; eauto using redd_refl.
    unfold whnf. intros. eapply val_whnf in H1; eauto.
Qed.


Lemma iredd_comp_redd_whnf Γ l t u v A :
    Γ ⊢< l > v -->> t : A -> 
    Γ ⊢< l > v -->>! u : A ->
    Γ ⊢< l > t -->>! u : A.
Proof.
    intros. destruct H0.
    split; eauto.
    generalize u H0 H1. clear u H0 H1.
    dependent induction H.
    - intros. eauto.
    - intros. dependent destruction H1.
      + eapply H2 in H. inversion H.
      + eapply red_det in H; eauto. subst. 
        eapply IHredd; eauto.
Qed.

Reserved Notation "Γ ⊢< l > t ~ u : T" (at level 50, l, t, u, T at next level).

Inductive ann_conv : ctx -> level -> term -> term -> term -> Prop :=

| aconv_refl :
    ∀ Γ l t A,
      Γ ⊢< l > t : A -> 
      Γ ⊢< l > t ~ t : A

| aconv_app :
    ∀ Γ i j A B t u A' B' t' T,
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ~ t' : Pi i j A B →
      Γ ⊢< i > u : A →
      Γ ⊢< Ax j > T ≡ B <[ u.. ] : Sort j ->
      Γ ⊢< j > app i j A B t u ~ app i j A' B' t' u : T

where "Γ ⊢< l > t ~ u : A" := (ann_conv Γ l t u A).

Lemma sim_to_conv Γ l t u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t ≡ u : A.
Proof.
    intros. induction H; eauto using conversion, refl_ty.
Qed.
  
Lemma aconv_conv Γ l t u T T' : 
    Γ ⊢< l > t ~ u : T -> 
    Γ ⊢< Ax l > T ≡ T' : Sort l ->
    Γ ⊢< l > t ~ u : T'.
Proof.
    intros.
    dependent induction H.
    - eapply aconv_refl. eauto using type_conv.
    - eapply aconv_app; eauto using conv_sym, conv_trans.
Qed.

Lemma sim_sym Γ l t u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > u ~ t : A.
Proof.
    intros. induction H; eauto using ann_conv.
    eapply aconv_app; eauto using conv_ty_in_ctx_conv, conv_sym, type_conv.
    eapply aconv_conv; eauto using conv_pi.
    eauto using conv_trans, subst, aux_subst, refl_ty.
Qed.

Lemma sim_left_red Γ l t t' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t --> t' : A ->
    exists u', Γ ⊢< l > u --> u' : A 
    /\ Γ ⊢< l > t' ~ u' : A.
Proof.
    intros H. generalize t'. clear t'. 
    dependent induction H; intros.
    - eauto 6 using red_to_conv, validity_conv_right, aconv_refl.
    - dependent induction H4.
      + eapply IHann_conv in H4 as (u' & red & sim).
        eexists. split.
        eapply red_conv. eapply red_app'; eauto using type_conv, red_conv, conv_pi, conv_sym, conv_ty_in_ctx_conv.
        eapply subst; eauto using aux_subst, refl_ty, conv_sym.
        eapply aconv_app; eauto.
      + dependent destruction H1. eexists.
        split. eapply red_conv.
        eapply red_beta'; eauto using conv_sym, conv_trans, conv_ty_in_ctx_conv, type_conv, conv_ty_in_ctx_ty.
        eapply subst; eauto using aux_subst, refl_ty, conv_sym.
        eapply aconv_refl. 
        eapply validity_conv_left. 
        eapply subst; eauto using aux_subst, refl_ty, conv_sym.
      + eapply IHred in H1 as (v & red & sim); eauto using conv_trans.
        eexists. split; eauto using red_conv, aconv_conv.
Qed.

Lemma sim_left_redd Γ l t t' u A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->> t' : A ->
    exists u', Γ ⊢< l > u -->> u' : A 
    /\ Γ ⊢< l > t' ~ u' : A.
Proof.
    intros. generalize u H. clear u H. induction H0; intros.
    - exists u. split; eauto using redd, sim_to_conv, validity_conv_right.
    - pose proof H1 as t_sim_u0. eapply sim_left_red in H1 as (u' & u0_red_U' & v_sim_u'); eauto.
      eapply IHredd in v_sim_u' as (u'' & u'_redd & u_sim).
      exists u''. split; eauto using redd.
Qed.

Lemma sim_left_redd_whnf Γ l t u v A :
    Γ ⊢< l > t ~ u : A -> 
    Γ ⊢< l > t -->>! v : A ->
    val v ->
    Γ ⊢< l > u -->>! v : A.
Proof.
    intros. 
    destruct H0. split.
    2:assumption.
    eapply sim_left_redd in H0 as (u' & u_redd_u' & t'_sim_u'); eauto.
    dependent induction t'_sim_u'; eauto.
    inversion H1.
Qed.
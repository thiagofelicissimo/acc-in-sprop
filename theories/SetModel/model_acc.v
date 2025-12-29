From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_acc HO_obseq HO_forall.
Require Import model_interp model_def.

Lemma model_acc (Γ : ctx) (i : level) (A R a : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tR : (Γ,, (i, A)),, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (i, A)),, (i, S ⋅ A)) (Ax prop) R (Sort prop))
  (ta : Γ ⊢< i > a : A) (ma : model_typing Γ i a A) :
  model_typing Γ (Ax prop) (Core.acc i A R a) (Sort prop).
Proof.
Admitted.

Lemma model_accin (Γ : ctx) (i : level) (A R a p : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tR : (Γ,, (i, A)),, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (i, A)),, (i, S ⋅ A)) (Ax prop) R (Sort prop))
  (ta : Γ ⊢< i > a : A) (ma : model_typing Γ i a A)
  (A_wk := (S >> S) ⋅ A)
  (R_wk := (up_ren (up_ren (S >> S))) ⋅ R)
  (acc_wk := Core.acc i A_wk R_wk (var 1))
  (R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))])
  (tp : Γ ⊢< prop > p : Pi i prop A (Pi prop prop R' acc_wk))
  (mp : model_typing Γ prop p (Pi i prop A (Pi prop prop R' acc_wk))) :
  model_typing Γ prop (accin i A R a p) (Core.acc i A R a).
Proof.
Admitted.

Lemma model_accinv (Γ : ctx) (i : level) (A R a p b r : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tR : (Γ,, (i, A)),, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (i, A)),, (i, S ⋅ A)) (Ax prop) R (Sort prop))
  (ta : Γ ⊢< i > a : A) (ma : model_typing Γ i a A)
  (tp : Γ ⊢< prop > p : Core.acc i A R a) (mp : model_typing Γ prop p (Core.acc i A R a))
  (tb : Γ ⊢< i > b : A) (mb : model_typing Γ i b A)
  (tr : Γ ⊢< prop > r : R <[ scons a b..]) (mr : model_typing Γ prop r (R <[ scons a b..])) :
  model_typing Γ prop (accinv i A R a p b r) (Core.acc i A R b).
Proof.
Admitted.

Lemma model_accelim (Γ : ctx) (i l : level) (A R a q P p : term) (tA : Γ ⊢< Ax i > A : Sort i) (mA : model_typing Γ (Ax i) A (Sort i))
  (tR : (Γ,, (i, A)),, (i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (i, A)),, (i, S ⋅ A)) (Ax prop) R (Sort prop))
  (tP : Γ,, (i, A) ⊢< Ax l > P : Sort l) (mP : model_typing (Γ,, (i, A)) (Ax l) P (Sort l))
  (R' := R <[var 1 .: (var 0 .: (S >> S >> var))])
  (P' := P <[var 1 .: (S >> S >> S >> var)])
  (B := Pi i l (S ⋅ A) (Pi prop l R' P'))
  (P'' := P <[var 1.: (S >> (S >> var))])
  (tp : (Γ,, (i, A)),, (Ru i l, B) ⊢< l > p : P'') (mp : model_typing ((Γ,, (i, A)),, (Ru i l, B)) l p P'')
  (ta : Γ ⊢< i > a : A) (ma : model_typing Γ i a A)
  (tq : Γ ⊢< prop > q : Core.acc i A R a) (mq : model_typing Γ prop q (Core.acc i A R a)) :
  model_typing Γ l (accel i l A R P p a q) (P <[ a..]).
Proof.
Admitted.

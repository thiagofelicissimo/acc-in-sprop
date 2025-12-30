From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_acc HO_obseq HO_forall.
Require Import model_interp model_def.

Lemma model_acc (Γ : ctx) (i : nat) (A R a : term) (tA : Γ ⊢< Ax (ty i) > A : Sort (ty i)) (mA : model_typing Γ (Ax (ty i)) A (Sort (ty i)))
  (tR : (Γ,, (ty i, A)),, (ty i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (ty i, A)),, (ty i, S ⋅ A)) (Ax prop) R (Sort prop))
  (ta : Γ ⊢< ty i > a : A) (ma : model_typing Γ (ty i) a A) :
  model_typing Γ (Ax prop) (Core.acc (ty i) A R a) (Sort prop).
Proof.
Admitted.

Lemma model_accin (Γ : ctx) (i : nat) (A R a p : term)
  (tA : Γ ⊢< Ax (ty i) > A : Sort (ty i)) (mA : model_typing Γ (Ax (ty i)) A (Sort (ty i)))
  (tR : (Γ,, (ty i, A)),, (ty i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (ty i, A)),, (ty i, S ⋅ A)) (Ax prop) R (Sort prop))
  (ta : Γ ⊢< ty i > a : A) (ma : model_typing Γ (ty i) a A)
  (A_wk := (S >> S) ⋅ A)
  (R_wk := (up_ren (up_ren (S >> S))) ⋅ R)
  (acc_wk := Core.acc (ty i) A_wk R_wk (var 1))
  (R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))])
  (tp : Γ ⊢< prop > p : Pi (ty i) prop A (Pi prop prop R' acc_wk))
  (mp : model_typing Γ prop p (Pi (ty i) prop A (Pi prop prop R' acc_wk))) :
  model_typing Γ prop (accin (ty i) A R a p) (Core.acc (ty i) A R a).
Proof.
Admitted.

Lemma model_accinv (Γ : ctx) (i : nat) (A R a p b r : term)
  (tA : Γ ⊢< Ax (ty i) > A : Sort (ty i)) (mA : model_typing Γ (Ax (ty i)) A (Sort (ty i)))
  (tR : (Γ,, (ty i, A)),, (ty i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (ty i, A)),, (ty i, S ⋅ A)) (Ax prop) R (Sort prop))
  (ta : Γ ⊢< ty i > a : A) (ma : model_typing Γ (ty i) a A)
  (tp : Γ ⊢< prop > p : Core.acc (ty i) A R a) (mp : model_typing Γ prop p (Core.acc (ty i) A R a))
  (tb : Γ ⊢< ty i > b : A) (mb : model_typing Γ (ty i) b A)
  (tr : Γ ⊢< prop > r : R <[ scons a b..]) (mr : model_typing Γ prop r (R <[ scons a b..])) :
  model_typing Γ prop (accinv (ty i) A R a p b r) (Core.acc (ty i) A R b).
Proof.
Admitted.

Lemma model_accelim (Γ : ctx) (i : nat) (l : level) (A R a q P p : term)
  (tA : Γ ⊢< Ax (ty i) > A : Sort (ty i)) (mA : model_typing Γ (Ax (ty i)) A (Sort (ty i)))
  (tR : (Γ,, (ty i, A)),, (ty i, S ⋅ A) ⊢< Ax prop > R : Sort prop)
  (mR : model_typing ((Γ,, (ty i, A)),, (ty i, S ⋅ A)) (Ax prop) R (Sort prop))
  (tP : Γ,, (ty i, A) ⊢< Ax l > P : Sort l) (mP : model_typing (Γ,, (ty i, A)) (Ax l) P (Sort l))
  (R' := R <[var 1 .: (var 0 .: (S >> S >> var))])
  (P' := P <[var 1 .: (S >> S >> S >> var)])
  (B := Pi (ty i) l (S ⋅ A) (Pi prop l R' P'))
  (P'' := P <[var 1.: (S >> (S >> var))])
  (tp : (Γ,, (ty i, A)),, (Ru (ty i) l, B) ⊢< l > p : P'') (mp : model_typing ((Γ,, (ty i, A)),, (Ru (ty i) l, B)) l p P'')
  (ta : Γ ⊢< ty i > a : A) (ma : model_typing Γ (ty i) a A)
  (tq : Γ ⊢< prop > q : Core.acc (ty i) A R a) (mq : model_typing Γ prop q (Core.acc (ty i) A R a)) :
  model_typing Γ l (accel (ty i) l A R P p a q) (P <[ a..]).
Proof.
Admitted.

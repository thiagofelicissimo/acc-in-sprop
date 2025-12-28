From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp model_def.

Open Scope subst_scope.

Lemma model_nat (Γ : ctx) (tΓ : ⊢ Γ) (mΓ : model_ctx Γ) :
  model_typing Γ (ty 1) Nat (Sort (ty 0)).
Proof.
  destruct mΓ as [ iΓ fΓ ]. econstructor.
  - exact fΓ.
  - apply interp_type.
  - apply interp_nat.
  - apply univTy_HO_typing.
  - apply natTy_HO_typing'.
Qed.

Lemma model_zero (Γ : ctx) (tΓ : ⊢ Γ) (mΓ : model_ctx Γ) :
  model_typing Γ (ty 0) zero Nat.
Proof.
  destruct mΓ as [ iΓ fΓ ]. econstructor.
  - exact fΓ.
  - apply interp_nat.
  - apply interp_zero.
  - apply natTy_HO_typing.
  - intros γ Hγ. apply zeroTm_HO_typing. 
Qed.

Lemma model_suc (Γ : ctx) (t : term) (tt : Γ ⊢< ty 0 > t : Nat) (mt : model_typing Γ (ty 0) t Nat) :
  model_typing Γ (ty 0) (succ t) Nat.
Proof.
  destruct mt. inversion fA ; subst ; clear fA. econstructor.
  - exact fΓ.
  - apply interp_nat.
  - apply interp_succ. exact ft.
  - apply natTy_HO_typing.
  - intros γ Hγ. apply (sucTm_HO_typing vt Hγ). 
Qed.

Lemma model_natrec (Γ : ctx) (l : level) (P pz ps t : term)
  (tP : Γ,, (ty 0, Nat) ⊢< Ax l > P : Sort l) (mP : model_typing (Γ,, (ty 0, Nat)) (Ax l) P (Sort l)) 
  (tpz : Γ ⊢< l > pz : P <[ zero..]) (mpz : model_typing Γ l pz (P <[ zero..]))
  (tps : (Γ,, (ty 0, Nat)),, (l, P) ⊢< l > ps : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ])
  (mps : model_typing ((Γ,, (ty 0, Nat)),, (l, P)) l ps (P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]))
  (tt : Γ ⊢< ty 0 > t : Nat) (mt : model_typing Γ (ty 0) t Nat) :
  model_typing Γ l (rec l P pz ps t) (P <[ t..]).
Proof.
Admitted.

From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp model_def.

Open Scope subst_scope.

(* Lemma model_nat (Γ : ctx) (tΓ : ⊢ Γ) (mΓ : model_ctx Γ) : *)
(*   model_typing Γ (ty 1) Nat (Sort (ty 0)). *)
(* Proof. *)
(*   destruct mΓ as [ *)

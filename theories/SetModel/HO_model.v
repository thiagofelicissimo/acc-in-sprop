From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory Reduction. 
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Require Import library.
Require Import ZF_axioms ZF_library.
Require Import HO HO_pi HO_sigma HO_nat.

Open Scope subst_scope.

Definition to_ZF_level (l : level) : nat :=
  match l with
  | ty n => n
  | prop => 0
  end.

Inductive interp_ctx : forall (Γ : ctx), ZFSet -> SProp :=

| interp_empty : interp_ctx ∙ (setSingl ∅)

| interp_cons  : forall Γ l A iΓ iA, interp_ctx Γ iΓ -> interp_tm Γ l A iA
                 -> interp_ctx (Γ ,, (l , A)) (setSigma (to_ZF_level l) iΓ (fun γ => 𝕌el (to_ZF_level l) (iA γ)))

with is_nth_proj : forall (Γ : ctx), (ZFSet -> ZFSet) -> SProp :=
| here :
  -> is_nth_proj (Γ ,, (l , A)) (fun γa => setSndSigma (to_ZF_level l) Γi (fun γ => 𝕌el (to_ZF_level l) (iA γ)) γa)

with interp_tm : forall (Γ : ctx) (l : level) (A : term), (ZFSet -> ZFSet) -> SProp :=

| interp_pi : forall Γ lA lB A B iΓ iA iB, interp_tm Γ lA A iA
              -> interp_tm (Γ ,, (lA , A)) (ty lB) B iB
              -> interp_tm Γ (Ru lA (ty lB)) (Pi lA (ty lB) A B) (piTy_HO (to_ZF_level (Ru lA (ty lB))) iΓ iA (fun γ a => iB ⟨ γ ; a ⟩))

(* | interp_forall :  *)

| interp_nat : forall Γ, interp_tm Γ (ty 0) Nat natTy_HO

| interp_type : forall Γ l, interp_tm Γ (Ax (ty l)) (Sort (ty l)) natTy_HO

| interp_prop : forall Γ l, interp_tm Γ (Ax (ty l)) (Sort (ty l)) natTy_HO

(* | interp_acc : ... *)

| interp_

piTy_HO (n : nat) (Γ : ZFSet) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet -> ZFSet) : ZFSet -> ZFSet :=



with interp_tm : forall (Γ : ctx) (l : level) (t : term), (ZFSet -> ZFSet) -> SProp :=
| interp_var : is_nth_proj Γ π 
    -> interp_tm Γ l (var x) π



Γ ⊢ t : A

∀ γ ∈ ⟦ Γ ⟧, ⟦ Γ ⊢ t ⟧γ ∈ ⟦ Γ ⊢ A ⟧γ

Lemma model : forall Γ l t A, Γ ⊢< l > t : A -> True.

(forall Γ l t A, Γ ⊢< l > t : A -> forall k (_temp : l = ty k), Γ ⊢< l > t ≡ t : A -> Γ ⊨< l > t ≡ t : A) ∧
      (forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> forall k (_temp : l = ty k), Γ ⊢< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A).

From Stdlib Require Import List Arith.
From TypedConfluence Require Import core unscoped AST SubstNotations.
From TypedConfluence Require Import Util BasicAST Contexts Typing. 

Import ListNotations.

Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_univ HO_prop HO_box HO_pi HO_sigma HO_nat HO_obseq HO_forall.
Require Import model_interp.

Open Scope subst_scope.

Inductive model_ctx (Γ : ctx) : Prop :=
| mkModelCtx (iΓ : ZFSet) (fΓ : interp_ctx Γ iΓ).

Inductive model_typing_rel (Γ : ctx) (l : nat) (t A : term) : Prop :=
| mkModelTypingRel (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax (ty l)) A iA)
    (it : ZFSet -> ZFSet)
    (ft : interp_tm Γ (ty l) t it)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l)
    (vt : ∀ γ ∈ iΓ, it γ ∈ 𝕌el l (iA γ)).

Inductive model_typing_irr (Γ : ctx) (t A : term) : Prop :=
| mkModelTypingIrr (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax prop) A iA)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω)
    (vt : ∀ γ ∈ iΓ, ∅ ∈ iA γ).

Definition model_typing (Γ : ctx) (l : level) (t A : term) : Prop :=
  match l with
  | prop => model_typing_irr Γ t A
  | ty l => model_typing_rel Γ l t A
  end.

Inductive model_conv_rel (Γ : ctx) (l : nat) (t u A : term) : Prop :=
| mkModelConvRel (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax (ty l)) A iA)
    (it : ZFSet -> ZFSet)
    (ft : interp_tm Γ (ty l) t it)
    (iu : ZFSet -> ZFSet)
    (fu : interp_tm Γ (ty l) u iu)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l)
    (vt : ∀ γ ∈ iΓ, it γ ∈ 𝕌el l (iA γ))
    (vu : ∀ γ ∈ iΓ, it γ ≡ iu γ).
  
Inductive model_conv_irr (Γ : ctx) (t u A : term) : Prop := True.
(* | mkModelConvIrr (iΓ : ZFSet) *)
(*     (fΓ : interp_ctx Γ iΓ) *)
(*     (iA : ZFSet -> ZFSet) *)
(*     (fA : interp_tm Γ (Ax prop) A iA) *)
(*     (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω) *)
(*     (vt : ∀ γ ∈ iΓ, ∅ ∈ iA γ). *)

Definition model_conv (Γ : ctx) (l : level) (t u A : term) : Prop :=
  match l with
  | prop => model_conv_irr Γ t u A
  | ty l => model_conv_rel Γ l t u A
  end.

(* Useful shortcuts *)

Inductive model_typing_type (Γ : ctx) (l : nat) (A : term) : Prop :=
| mkModelTypingType (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax (ty l)) A iA)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l).

Inductive model_typing_prop (Γ : ctx) (A : term) : Prop :=
| mkModelTypingProp (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax prop) A iA)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω).

Definition model_typing_univ (Γ : ctx) (l : level) (A : term) : Prop :=
  match l with
  | prop => model_typing_prop Γ A
  | ty l => model_typing_type Γ l A
  end.

Inductive model_conv_type (Γ : ctx) (l : nat) (A B : term) : Prop :=
| mkModelConvType (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax (ty l)) A iA)
    (iB : ZFSet -> ZFSet)
    (fB : interp_tm Γ (Ax (ty l)) B iB)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ 𝕌 l)
    (vu : ∀ γ ∈ iΓ, iA γ ≡ iB γ).

Inductive model_conv_prop (Γ : ctx) (A B : term) : Prop :=
| mkModelConvProp (iΓ : ZFSet)
    (fΓ : interp_ctx Γ iΓ)
    (iA : ZFSet -> ZFSet)
    (fA : interp_tm Γ (Ax prop) A iA)
    (iB : ZFSet -> ZFSet)
    (fB : interp_tm Γ (Ax prop) B iB)
    (vA : ∀ γ ∈ iΓ, iA γ ∈ Ω)
    (vu : ∀ γ ∈ iΓ, iA γ ≡ iB γ).

Definition model_conv_univ (Γ : ctx) (l : level) (A B : term) : Prop :=
  match l with
  | prop => model_conv_prop Γ A B
  | ty l => model_conv_type Γ l A B
  end.

Lemma of_model_type (Γ : ctx) (l : nat) (A : term) : model_typing_rel Γ (S l) A (Sort (ty l)) -> model_typing_type Γ l A.
Proof.
  intros [ iΓ fΓ iS fS iA fA vS vA ]. inversion fS ; subst ; clear fS.
  destruct (functional_ctx Γ fΓ H1) ; clear H1. econstructor.
  + exact fΓ.
  + exact fA.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) _ (vA γ Hγ)). now apply el_univTy_cl.
Qed.

Lemma of_model_prop (Γ : ctx) (A : term) : model_typing_rel Γ 0 A (Sort prop) -> model_typing_prop Γ A.
Proof.
  intros [ iΓ fΓ iS fS iA fA vS vA ]. inversion fS ; subst ; clear fS.
  destruct (functional_ctx Γ fΓ H) ; clear H. econstructor.
  + exact fΓ.
  + exact fA.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) _ (vA γ Hγ)). now apply el_propTy_cl.
Qed.

Lemma of_model_univ (Γ : ctx) (l : level) (A : term) : model_typing Γ (Ax l) A (Sort l) -> model_typing_univ Γ l A.
Proof.
  destruct l as [ l | ].
  - apply of_model_type.
  - apply of_model_prop.
Qed.

Lemma to_model_type (Γ : ctx) (l : nat) (A : term) : model_typing_type Γ l A -> model_typing_rel Γ (S l) A (Sort (ty l)).
Proof.
  intros [ iΓ fΓ iA fA vA ]. econstructor.
  + exact fΓ.
  + apply interp_type. exact fΓ.
  + exact fA.
  + apply univTy_cl_typing.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA γ Hγ)). now apply el_univTy_cl.
Qed.

Lemma to_model_prop (Γ : ctx) (A : term) : model_typing_prop Γ A -> model_typing_rel Γ 0 A (Sort prop).
Proof.
  intros [ iΓ fΓ iA fA vA ]. econstructor.
  + exact fΓ.
  + apply interp_prop. exact fΓ.
  + exact fA.
  + apply propTy_cl_typing.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA γ Hγ)). now apply el_propTy_cl.
Qed.

Lemma to_model_univ (Γ : ctx) (l : level) (A : term) : model_typing_univ Γ l A -> model_typing Γ (Ax l) A (Sort l).
Proof.
  destruct l as [ l | ].
  - apply to_model_type.
  - apply to_model_prop.
Qed.

Lemma of_model_conv_type (Γ : ctx) (l : nat) (A B : term) : model_conv_rel Γ (S l) A B (Sort (ty l)) -> model_conv_type Γ l A B.
Proof.
  intros [ iΓ fΓ iS fS iA fA iB fB vS vA vB ]. inversion fS ; subst ; clear fS.
  destruct (functional_ctx Γ fΓ H1) ; clear H1. econstructor.
  + exact fΓ.
  + exact fA.
  + exact fB.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) _ (vA γ Hγ)). now apply el_univTy_cl.
  + exact vB.
Qed.

Lemma of_model_conv_prop (Γ : ctx) (A B : term) : model_conv_rel Γ 0 A B (Sort prop) -> model_conv_prop Γ A B.
Proof.
  intros [ iΓ fΓ iS fS iA fA iB fB vS vA vB ]. inversion fS ; subst ; clear fS. 
  destruct (functional_ctx Γ fΓ H) ; clear H. econstructor.
  + exact fΓ.
  + exact fA.
  + exact fB.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) _ (vA γ Hγ)). now apply el_propTy_cl.
  + exact vB.
Qed.

Lemma of_model_conv_univ (Γ : ctx) (l : level) (A B : term) : model_conv Γ (Ax l) A B (Sort l) -> model_conv_univ Γ l A B.
Proof.
  destruct l as [ l | ].
  - apply of_model_conv_type.
  - apply of_model_conv_prop.
Qed.

Lemma to_model_conv_type (Γ : ctx) (l : nat) (A B : term) : model_conv_type Γ l A B -> model_conv_rel Γ (S l) A B (Sort (ty l)).
Proof.
  intros [ iΓ fΓ iA fA iB fB vA vB ]. econstructor.
  + exact fΓ.
  + apply interp_type. exact fΓ.
  + exact fA.
  + exact fB.
  + apply univTy_cl_typing.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA γ Hγ)). now apply el_univTy_cl.
  + exact vB.
Qed.

Lemma to_model_conv_prop (Γ : ctx) (A B : term) : model_conv_prop Γ A B -> model_conv_rel Γ 0 A B (Sort prop).
Proof.
  intros [ iΓ fΓ iA fA iB fB vA vB ]. econstructor.
  + exact fΓ.
  + apply interp_prop. apply fΓ.
  + exact fA.
  + exact fB.
  + apply propTy_cl_typing.
  + intros γ Hγ. refine (transpS (fun X => _ ∈ X) (sym _) (vA γ Hγ)). now apply el_propTy_cl.
  + exact vB.
Qed.

Lemma to_model_conv_univ (Γ : ctx) (l : level) (A B : term) : model_conv_univ Γ l A B -> model_conv Γ (Ax l) A B (Sort l).
Proof.
  destruct l as [ l | ].
  - apply to_model_conv_type.
  - apply to_model_conv_prop.
Qed.


  

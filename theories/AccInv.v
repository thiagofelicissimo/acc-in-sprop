

(* this file justifies why we can suppose an object term acc_inv with the appropriate typing rule. 
  indeed, by translating this proof into the object language, we would obtain implementations of the axioms 
    Axiom accinv : level -> term -> term -> term -> term -> term -> term -> term.
    Axiom type_accinv :
        ∀ Γ i A R a p b r,
        Γ ⊢< Ax i > A : Sort i ->
        Γ ,, (i, A) ,, (i, A<[shift>>var]) ⊢< Ax prop > R : Sort prop -> 
        Γ ⊢< i > a : A -> 
        Γ ⊢< prop > p : acc i A R a -> 
        Γ ⊢< i > b : A -> 
        Γ ⊢< prop > r : R <[a.:b..] -> 
        Γ ⊢< prop > accinv i A R a p b r : acc i A R b.  
  *)

Axiom Acc : forall (A : Type) (R : A -> A -> Prop) (a : A), Prop.

Axiom acc_in : forall A R a, (forall y, R a y -> Acc A R y) -> Acc A R a.

Axiom Acc_pre_ind : forall A R (P : A -> Prop) (p : forall a : A, (forall y : A, R a y -> P y) -> P a) (y : A) (r : Acc A R y), P y.

Definition prod_prop (A B : Prop) : Prop := forall P, (A -> B -> P) -> P.

Definition fst_prop {A B}: prod_prop A B -> A := fun f => f A (fun a b => a).

Definition snd_prop {A B}: prod_prop A B -> B := fun f => f B (fun a b => b).

Definition mk_prod_prop {A B} : A -> B -> prod_prop A B := fun a b P f => f a b.

Lemma Acc_ind A R (P : A -> Prop) (p : forall a : A, (forall y, R a y -> Acc A R y) -> (forall y, R a y -> P y) -> P a) (y : A) (r : Acc A R y) : P y.
Proof.
  intros.
  eapply snd_prop.
  eapply (Acc_pre_ind _ _ (fun a => prod_prop (Acc A R a) (P a))).
  2:exact r.
  intros. eapply mk_prod_prop.
  - eapply acc_in. intros. eapply H in H0. eapply (fst_prop H0).
  - eapply p.
    + intros. eapply H in H0.  eapply (fst_prop H0).
    + intros. eapply H in H0. eapply (snd_prop H0). 
Defined.

Lemma acc_inv A R a : Acc A R a -> forall b, R a b -> Acc A R b.
Proof.
  intros.
  eapply (Acc_ind _ _ (fun a => R a b -> Acc A R b)). 3:exact H0. 2:exact H.
  intros. eapply H1. exact H3.
Defined.

(* the implementation of accinv would require us to write the term printed by the 
  following command in the syntax specified in AST.v, and then retype it using 
  the rules of Typing.v. by the above proofs, this would be theoretically possible
  but practically infeasible, justifying why supposing these axioms is reasonable *)
Eval cbv in acc_inv.
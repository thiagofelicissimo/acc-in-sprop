From Stdlib Require Import Arith.
Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_univ.

(* Sigma types. Similar to Pi types *)

Definition sigmaTy_HO (nA nB : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setSigma (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩))
           ; ⟨ ZFtwo ; typeTelescope2 nA nB A B γ ⟩ ⟩.

Lemma sigmaTy_HO_typing {nA nB : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) :
  ∀ γ ∈ Γ, sigmaTy_HO nA nB A B γ ∈ 𝕌 (max nA nB).
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setSigma_typing.
    + eapply univ_le_incl. apply Nat.le_max_l. apply 𝕌el_typing. now apply HA.
    + intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB). 
  - apply setMkPair_typing.
    + apply two_typing.
    + apply (typeTelescope2_typing nA nB (Γ := Γ)) ; try assumption. 
Qed.

Lemma el_sigmaTy {nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌el (max nA nB) (sigmaTy_HO nA nB A B γ) ≡ setSigma (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩)).
Proof.
  apply setPairβ1'. now apply (sigmaTy_HO_typing (Γ := Γ)).
Qed.

Lemma el_sigmaTy' {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} 
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌el n (sigmaTy_HO nA nB A B γ) ≡ setSigma (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩)).
Proof.
  apply setPairβ1'. eapply 𝕌_le_incl. apply (Nat.max_lub _ _ _ HnA HnB). now apply (sigmaTy_HO_typing (Γ := Γ)).
Qed.

Lemma hd_sigmaTy' {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} 
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌hd n (sigmaTy_HO nA nB A B γ) ≡ ZFtwo.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'. eapply 𝕌_le_incl. apply (Nat.max_lub _ _ _ HnA HnB). now apply (sigmaTy_HO_typing (Γ := Γ)).
  apply setPairβ1. apply two_typing. eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
  apply (typeTelescope2_typing nA nB (Γ := Γ)) ; try assumption.
Qed.  

Lemma lbl_sigmaTy' {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌lbl n (sigmaTy_HO nA nB A B γ) ≡ typeTelescope2 nA nB A B γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _).
  apply setPairβ2'. eapply 𝕌_le_incl. apply (Nat.max_lub _ _ _ HnA HnB). now apply (sigmaTy_HO_typing (Γ := Γ)).
  apply setPairβ2. apply two_typing. eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
  apply (typeTelescope2_typing nA nB (Γ := Γ)) ; try assumption.
Qed.

(* Recovering the domain and codomain, along with their levels, from the code of a Sigma type *)

Definition dom_sigmaTy (n : nat) (x : ZFSet) := setFstPair (ω × 𝕌 n) (ω × 𝕍 n) (𝕌lbl n x).
Definition dom_sigmaTy_level (n : nat) (x : ZFSet) := setFstPair ω (𝕌 n) (dom_sigmaTy n x).
Definition dom_sigmaTy_set (n : nat) (x : ZFSet) := setSndPair ω (𝕌 n) (dom_sigmaTy n x).
Definition cod_sigmaTy (n : nat) (x : ZFSet) := setSndPair (ω × 𝕌 n) (ω × 𝕍 n) (𝕌lbl n x).
Definition cod_sigmaTy_level (n : nat) (x : ZFSet) := setFstPair ω (𝕍 n) (cod_sigmaTy n x).
Definition cod_sigmaTy_set (n : nat) (x : ZFSet) := setSndPair ω (𝕍 n) (cod_sigmaTy n x).

Lemma dom_sigmaTy_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  dom_sigmaTy n (sigmaTy_HO nA nB A B γ) ≡ ⟨ nat_to_ω nA ; A γ ⟩.
Proof.
  refine (trans (fequal (setFstPair (ω × 𝕌 n) (ω × 𝕍 n)) _) _). now apply (lbl_sigmaTy' (Γ := Γ)). apply setPairβ1. 
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply 𝕌_le_incl. exact HnA. now apply HA.
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
      apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma dom_sigmaTy_level_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  dom_sigmaTy_level n (sigmaTy_HO nA nB A B γ) ≡ nat_to_ω nA.
Proof.
  refine (trans (fequal (setFstPair ω (𝕌 n)) _) _). now apply (dom_sigmaTy_eq HnA HnB HA HB). apply setPairβ1.
  - apply nat_to_ω_typing.
  - eapply 𝕌_le_incl. exact HnA. now apply HA.
Qed.

Lemma dom_sigmaTy_set_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  dom_sigmaTy_set n (sigmaTy_HO nA nB A B γ) ≡ A γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕌 n)) _) _). now apply (dom_sigmaTy_eq HnA HnB HA HB). apply setPairβ2.
  - apply nat_to_ω_typing.
  - eapply 𝕌_le_incl. exact HnA. now apply HA.
Qed.

Lemma cod_sigmaTy_eq {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  cod_sigmaTy n (sigmaTy_HO nA nB A B γ) ≡ ⟨ nat_to_ω nB ; typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩) ⟩.
Proof.
  refine (trans (fequal (setSndPair (ω × 𝕌 n) (ω × 𝕍 n)) _) _). now apply (lbl_sigmaTy' (Γ := Γ)). apply setPairβ2.
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply 𝕌_le_incl. exact HnA. now apply HA.
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
      apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma cod_sigmaTy_level_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  cod_sigmaTy_level n (sigmaTy_HO nA nB A B γ) ≡ nat_to_ω nB.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _). now apply (cod_sigmaTy_eq HnA HnB HA HB). apply setPairβ1.
  - apply nat_to_ω_typing.
  - eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
    apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma cod_sigmaTy_set_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  cod_sigmaTy_set n (sigmaTy_HO nA nB A B γ) ≡ typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩).
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _). now apply (cod_sigmaTy_eq HnA HnB HA HB). apply setPairβ2.
  - apply nat_to_ω_typing.
  - eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
    apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

(* We deduce that Sigma types are injective *)

Definition maxmax (nA nA' nB nB' : nat) := max (max nA nA') (max nB nB').

Lemma maxmax_le (nA nA' nB nB' : nat) :
  (nA <= maxmax nA nA' nB nB') /\ (nA' <= maxmax nA nA' nB nB') /\ (nB <= maxmax nA nA' nB nB') /\ (nB' <= maxmax nA nA' nB nB').
Proof.
  split. { etransitivity. apply (Nat.le_max_l nA nA'). apply Nat.le_max_l. }
  split. { etransitivity. apply (Nat.le_max_r nA nA'). apply Nat.le_max_l. }
  split. { etransitivity. apply (Nat.le_max_l nB nB'). apply Nat.le_max_r. }
  etransitivity. apply (Nat.le_max_r nB nB'). apply Nat.le_max_r.
Qed.

Lemma sigmaTy_HO_inj_dom {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO nA nB A B γ ≡ sigmaTy_HO nA' nB' A' B' γ) : A γ ≡ A' γ.
Proof.
  set (N := maxmax nA nA' nB nB').
  refine (trans (b := dom_sigmaTy_set N (sigmaTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (dom_sigmaTy_set_eq _ _ HA HB Hγ) ; now apply (maxmax_le nA nA' nB nB'). }
  refine (trans (fequal (dom_sigmaTy_set N) H) _).
  refine (dom_sigmaTy_set_eq _ _ HA' HB' Hγ) ; now apply (maxmax_le nA nA' nB nB').
Qed.

Lemma sigmaTy_HO_inj_dom_level {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO nA nB A B γ ≡ sigmaTy_HO nA' nB' A' B' γ) : nA ≡ nA'.
Proof.
  apply nat_to_ω_inj. set (N := maxmax nA nA' nB nB').
  refine (trans (b := dom_sigmaTy_level N (sigmaTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (dom_sigmaTy_level_eq _ _ HA HB Hγ) ; now apply (maxmax_le nA nA' nB nB'). }
  refine (trans (fequal (dom_sigmaTy_level N) H) _).
  refine (dom_sigmaTy_level_eq _ _ HA' HB' Hγ) ; now apply (maxmax_le nA nA' nB nB').
Qed.

Lemma sigmaTy_HO_inj_cod_level {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO nA nB A B γ ≡ sigmaTy_HO nA' nB' A' B' γ) : nB ≡ nB'.
Proof.
  apply nat_to_ω_inj. set (N := maxmax nA nA' nB nB').
  refine (trans (b := cod_sigmaTy_level N (sigmaTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (cod_sigmaTy_level_eq _ _ HA HB Hγ) ; now apply (maxmax_le nA nA' nB nB'). }
  refine (trans (fequal (cod_sigmaTy_level N) H) _).
  refine (cod_sigmaTy_level_eq _ _ HA' HB' Hγ) ; now apply (maxmax_le nA nA' nB nB').
Qed.

Lemma sigmaTy_HO_inj_cod' {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO nA nB A B γ ≡ sigmaTy_HO nA' nB' A' B' γ) :
  typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩) ≡ typeToGraph nA nB' (A γ) (fun a => B' ⟨ γ ; a ⟩).
Proof.
  set (N := maxmax nA nA' nB nB').
  pose proof (sigmaTy_HO_inj_dom HA HB HA' HB' Hγ H) as HAA'.
  pose proof (sigmaTy_HO_inj_dom_level HA HB HA' HB' Hγ H) as HnAA'. destruct HnAA'.
  refine (trans (b := cod_sigmaTy_set N (sigmaTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (cod_sigmaTy_set_eq _ _ HA HB Hγ) ; apply (maxmax_le nA nA nB nB'). }
  refine (trans (fequal (cod_sigmaTy_set N) H) _).
  refine (transpS (fun X => _ ≡ typeToGraph nA nB' X _) (sym HAA') _).
  refine (cod_sigmaTy_set_eq _ _ HA' HB' Hγ) ; apply (maxmax_le nA nA nB nB').
Qed.

Lemma sigmaTy_HO_inj_cod {nA nA' nB nB' : nat} {Γ γ a : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : sigmaTy_HO nA nB A B γ ≡ sigmaTy_HO nA' nB' A' B' γ) (Ha : a ∈ 𝕌el nA (A γ)) :
  B ⟨ γ ; a ⟩ ≡ B' ⟨ γ ; a ⟩.
Proof.
  pose proof (sigmaTy_HO_inj_dom HA HB HA' HB' Hγ H) as HAA'.
  pose proof (sigmaTy_HO_inj_dom_level HA HB HA' HB' Hγ H) as HnAA'. destruct HnAA'.
  pose proof (sigmaTy_HO_inj_cod' HA HB HA' HB' Hγ H) as HBB'.
  pose proof (sigmaTy_HO_inj_cod_level HA HB HA' HB' Hγ H) as HnBB'. destruct HnBB'.
  refine (trans (b := setAppArr (𝕌el nA (A γ)) (𝕌 nB) (typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩)) a) _ _).
  { symmetry. refine (trans _ _). apply setAppArr_HO ; try assumption.
    now apply (typeExt_typing HA HB). reflexivity. }
  refine (trans (fequal (fun X => setAppArr (𝕌el nA (A γ)) (𝕌 nB) X a) HBB') _).
  refine (trans _ _). apply setAppArr_HO ; try assumption. 2:reflexivity.
  intros a' Ha'. pose proof (transpS (fun X => a' ∈ 𝕌el nA X) HAA' Ha') as Ha''. cbn in Ha''. clear Ha'.
  revert a' Ha''. now apply (typeExt_typing HA' HB').
Qed.

(* Pairing *)

Definition pairTm_HO (nA nB : nat) (t : ZFSet -> ZFSet) (u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ t γ ; u γ ⟩.

Lemma pairTm_HO_typing {nA nB : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el nA (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el nB (B ⟨ γ ; t γ ⟩))
  : ∀ γ ∈ Γ, pairTm_HO nA nB t u γ ∈ 𝕌el (max nA nB) (sigmaTy_HO nA nB A B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_sigmaTy HA HB Hγ)) _). apply setMkSigma_typing.
  - intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Ht.
  - now apply Hu.
Qed.

(* First projection *)

Definition fstTm_HO (nA nB : nat) (A B t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setFstSigma (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩)) (t γ).

Lemma fstTm_HO_typing {nA nB : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el (max nA nB) (sigmaTy_HO nA nB A B γ)) : ∀ γ ∈ Γ, fstTm_HO nA nB A B t γ ∈ 𝕌el nA (A γ).
Proof.
  intros γ Hγ. cbn. unfold fstTm_HO. apply setFstSigma_typing.
  - intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - refine (transpS (fun X => _ ∈ X) (el_sigmaTy HA HB Hγ) _). now apply Ht.
Qed.

(* Second projection *)

Definition sndTm_HO (nA nB : nat) (A B t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setSndSigma (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩)) (t γ).

Lemma sndTm_HO_typing {nA nB : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el (max nA nB) (sigmaTy_HO nA nB A B γ)) :
  ∀ γ ∈ Γ, sndTm_HO nA nB A B t γ ∈ 𝕌el nB (B ⟨ γ ; fstTm_HO nA nB A B t γ ⟩).
Proof.
  intros γ Hγ. cbn. unfold fstTm_HO. refine (transpS (fun X => _ ∈ X) _ _).
  2:{ apply setSndSigma_typing.
      - intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
      - refine (transpS (fun X => _ ∈ X) (el_sigmaTy HA HB Hγ) _). now apply Ht. }
  reflexivity.
Qed.

(* Equations (β and η) *)

Lemma sigmaTy_HO_β1 {nA nB : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el nA (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el nB (B ⟨ γ ; t γ ⟩)) :
  ∀ γ ∈ Γ, fstTm_HO nA nB A B (pairTm_HO nA nB t u) γ ≡ t γ.
Proof.
  intros γ Hγ. cbn. apply setSigmaβ1.
  - intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Ht.
  - now apply Hu.
Qed.

Lemma sigmaTy_HO_β2 {nA nB : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el nA (A γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el nB (B ⟨ γ ; t γ ⟩)) :
  ∀ γ ∈ Γ, sndTm_HO nA nB A B (pairTm_HO nA nB t u) γ ≡ u γ.
Proof.
  intros γ Hγ. cbn. apply setSigmaβ2.
  - intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Ht.
  - now apply Hu.
Qed.

Lemma sigmaTy_HO_η {nA nB : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el (max nA nB) (sigmaTy_HO nA nB A B γ)) :
  ∀ γ ∈ Γ, t γ ≡ pairTm_HO nA nB (fstTm_HO nA nB A B t) (sndTm_HO nA nB A B t) γ.
Proof.
  intros γ Hγ. cbn. apply setSigmaη.
  - intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - refine (transpS (fun X => _ ∈ X) (el_sigmaTy HA HB Hγ) _). now apply Ht.
Qed.

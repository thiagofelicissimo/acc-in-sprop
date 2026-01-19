From Stdlib Require Import Arith.
Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_univ HO_box.

(* Pi types *)

Definition piTy_HO (nA nB : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ⟨ setPi (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩))
           ; ⟨ ZFone ; typeTelescope2 nA nB A B γ ⟩ ⟩.

Lemma piTy_HO_cong {nA nB : nat} {Γ : ZFSet} {A1 A2 B1 B2 : ZFSet -> ZFSet} 
  (HAe : ∀ γ ∈ Γ, A1 γ ≡ A2 γ) (HBe : ∀ γa ∈ ctxExt nA Γ A1, B1 γa ≡ B2 γa) :
  ∀ γ ∈ Γ, piTy_HO nA nB A1 B1 γ ≡ piTy_HO nA nB A2 B2 γ.
Proof.
  intros γ Hγ. unfold piTy_HO. refine (fequal2 (fun X Y => ⟨ X ; ⟨ ZFone ; Y ⟩ ⟩) _ _).
  - destruct (HAe γ Hγ). apply setPi_cong. intros a Ha. refine (fequal (𝕌el nB) _).
    apply HBe. apply setMkSigma_typing ; try assumption. clear γ Hγ a Ha. unfold 𝕌el.
    intros γ Hγ. apply 𝕌el_typing'.
  - now apply (typeTelescope2_cong (Γ := Γ)).
Qed.

Lemma piTy_HO_typing {nA nB : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) :
  ∀ γ ∈ Γ, piTy_HO nA nB A B γ ∈ 𝕌 (max nA nB).
Proof.
  intros γ Hγ. cbn. apply setMkPair_typing.
  - apply setPi_typing.
    + eapply univ_le_incl. apply Nat.le_max_l. apply 𝕌el_typing. now apply HA.
    + intros a Ha. eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB). 
  - apply setMkPair_typing.
    + apply one_typing.
    + apply (typeTelescope2_typing nA nB (Γ := Γ)) ; try assumption. 
Qed.

Lemma piTy_HO_typing_ir {nB : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ Ω) (HB : ∀ γa ∈ ctxExt 0 Γ (boxTy_HO A), B γa ∈ 𝕌 nB) :
  ∀ γ ∈ Γ, piTy_HO 0 nB (boxTy_HO A) B γ ∈ 𝕌 nB.
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym _) (piTy_HO_typing (boxTy_HO_typing HA) HB γ Hγ)).
  refine (fequal 𝕌 _). destruct (eq_sym (Nat.max_0_l nB)). easy.
Qed.

Lemma el_piTy {nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌el (max nA nB) (piTy_HO nA nB A B γ) ≡ setPi (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩)).
Proof.
  apply setPairβ1'. now apply (piTy_HO_typing (Γ := Γ)).
Qed.

Lemma el_piTy' {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} 
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌el n (piTy_HO nA nB A B γ) ≡ setPi (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩)).
Proof.
  apply setPairβ1'. eapply 𝕌_le_incl. apply (Nat.max_lub _ _ _ HnA HnB). now apply (piTy_HO_typing (Γ := Γ)).
Qed.

Lemma hd_piTy' {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} 
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌hd n (piTy_HO nA nB A B γ) ≡ ZFone.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'. eapply 𝕌_le_incl. apply (Nat.max_lub _ _ _ HnA HnB). now apply (piTy_HO_typing (Γ := Γ)).
  apply setPairβ1. apply one_typing. eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
  apply (typeTelescope2_typing nA nB (Γ := Γ)) ; try assumption.
Qed.  

Lemma lbl_piTy' {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  𝕌lbl n (piTy_HO nA nB A B γ) ≡ typeTelescope2 nA nB A B γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _).
  apply setPairβ2'. eapply 𝕌_le_incl. apply (Nat.max_lub _ _ _ HnA HnB). now apply (piTy_HO_typing (Γ := Γ)).
  apply setPairβ2. apply one_typing. eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
  apply (typeTelescope2_typing nA nB (Γ := Γ)) ; try assumption.
Qed.

(* Recovering the domain and codomain, along with their levels, from the code of a Pi type *)

Definition dom_piTy (n : nat) (x : ZFSet) := setFstPair (ω × 𝕌 n) (ω × 𝕍 n) (𝕌lbl n x).
Definition dom_piTy_level (n : nat) (x : ZFSet) := setFstPair ω (𝕌 n) (dom_piTy n x).
Definition dom_piTy_set (n : nat) (x : ZFSet) := setSndPair ω (𝕌 n) (dom_piTy n x).
Definition cod_piTy (n : nat) (x : ZFSet) := setSndPair (ω × 𝕌 n) (ω × 𝕍 n) (𝕌lbl n x).
Definition cod_piTy_level (n : nat) (x : ZFSet) := setFstPair ω (𝕍 n) (cod_piTy n x).
Definition cod_piTy_set (n : nat) (x : ZFSet) := setSndPair ω (𝕍 n) (cod_piTy n x).

Lemma dom_piTy_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  dom_piTy n (piTy_HO nA nB A B γ) ≡ ⟨ nat_to_ω nA ; A γ ⟩.
Proof.
  refine (trans (fequal (setFstPair (ω × 𝕌 n) (ω × 𝕍 n)) _) _). now apply (lbl_piTy' (Γ := Γ)). apply setPairβ1. 
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply 𝕌_le_incl. exact HnA. now apply HA.
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
      apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma dom_piTy_level_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  dom_piTy_level n (piTy_HO nA nB A B γ) ≡ nat_to_ω nA.
Proof.
  refine (trans (fequal (setFstPair ω (𝕌 n)) _) _). now apply (dom_piTy_eq HnA HnB HA HB). apply setPairβ1.
  - apply nat_to_ω_typing.
  - eapply 𝕌_le_incl. exact HnA. now apply HA.
Qed.

Lemma dom_piTy_set_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  dom_piTy_set n (piTy_HO nA nB A B γ) ≡ A γ.
Proof.
  refine (trans (fequal (setSndPair ω (𝕌 n)) _) _). now apply (dom_piTy_eq HnA HnB HA HB). apply setPairβ2.
  - apply nat_to_ω_typing.
  - eapply 𝕌_le_incl. exact HnA. now apply HA.
Qed.

Lemma cod_piTy_eq {n nA nB : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  cod_piTy n (piTy_HO nA nB A B γ) ≡ ⟨ nat_to_ω nB ; typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩) ⟩.
Proof.
  refine (trans (fequal (setSndPair (ω × 𝕌 n) (ω × 𝕍 n)) _) _). now apply (lbl_piTy' (Γ := Γ)). apply setPairβ2.
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply 𝕌_le_incl. exact HnA. now apply HA.
  - apply setMkPair_typing.
    + apply nat_to_ω_typing.
    + eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
      apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma cod_piTy_level_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  cod_piTy_level n (piTy_HO nA nB A B γ) ≡ nat_to_ω nB.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _). now apply (cod_piTy_eq HnA HnB HA HB). apply setPairβ1.
  - apply nat_to_ω_typing.
  - eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
    apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

Lemma cod_piTy_set_eq {nA nB n : nat} {Γ γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HnA : nA <= n) (HnB : nB <= n) (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) (Hγ : γ ∈ Γ) :
  cod_piTy_set n (piTy_HO nA nB A B γ) ≡ typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩).
Proof.
  refine (trans (fequal (setSndPair ω (𝕍 n)) _) _). now apply (cod_piTy_eq HnA HnB HA HB). apply setPairβ2.
  - apply nat_to_ω_typing.
  - eapply univ_le_incl. apply (Nat.max_lub _ _ _ HnA HnB).
    apply typeToGraph_sorting. now apply HA. now apply (typeExt_typing HA HB).
Qed.

(* We deduce that Pi types are injective *)

Definition maxmax (nA nA' nB nB' : nat) := max (max nA nA') (max nB nB').

Lemma maxmax_le (nA nA' nB nB' : nat) :
  (nA <= maxmax nA nA' nB nB') /\ (nA' <= maxmax nA nA' nB nB') /\ (nB <= maxmax nA nA' nB nB') /\ (nB' <= maxmax nA nA' nB nB').
Proof.
  split. { etransitivity. apply (Nat.le_max_l nA nA'). apply Nat.le_max_l. }
  split. { etransitivity. apply (Nat.le_max_r nA nA'). apply Nat.le_max_l. }
  split. { etransitivity. apply (Nat.le_max_l nB nB'). apply Nat.le_max_r. }
  etransitivity. apply (Nat.le_max_r nB nB'). apply Nat.le_max_r.
Qed.

Lemma piTy_HO_inj_dom {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : piTy_HO nA nB A B γ ≡ piTy_HO nA' nB' A' B' γ) : A γ ≡ A' γ.
Proof.
  set (N := maxmax nA nA' nB nB').
  refine (trans (b := dom_piTy_set N (piTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (dom_piTy_set_eq _ _ HA HB Hγ) ; now apply (maxmax_le nA nA' nB nB'). }
  refine (trans (fequal (dom_piTy_set N) H) _).
  refine (dom_piTy_set_eq _ _ HA' HB' Hγ) ; now apply (maxmax_le nA nA' nB nB').
Qed.

Lemma piTy_HO_inj_dom_level {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : piTy_HO nA nB A B γ ≡ piTy_HO nA' nB' A' B' γ) : nA ≡ nA'.
Proof.
  apply nat_to_ω_inj. set (N := maxmax nA nA' nB nB').
  refine (trans (b := dom_piTy_level N (piTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (dom_piTy_level_eq _ _ HA HB Hγ) ; now apply (maxmax_le nA nA' nB nB'). }
  refine (trans (fequal (dom_piTy_level N) H) _).
  refine (dom_piTy_level_eq _ _ HA' HB' Hγ) ; now apply (maxmax_le nA nA' nB nB').
Qed.

Lemma piTy_HO_inj_cod_level {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : piTy_HO nA nB A B γ ≡ piTy_HO nA' nB' A' B' γ) : nB ≡ nB'.
Proof.
  apply nat_to_ω_inj. set (N := maxmax nA nA' nB nB').
  refine (trans (b := cod_piTy_level N (piTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (cod_piTy_level_eq _ _ HA HB Hγ) ; now apply (maxmax_le nA nA' nB nB'). }
  refine (trans (fequal (cod_piTy_level N) H) _).
  refine (cod_piTy_level_eq _ _ HA' HB' Hγ) ; now apply (maxmax_le nA nA' nB nB').
Qed.

Lemma piTy_HO_inj_cod' {nA nA' nB nB' : nat} {Γ γ : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : piTy_HO nA nB A B γ ≡ piTy_HO nA' nB' A' B' γ) :
  typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩) ≡ typeToGraph nA nB' (A γ) (fun a => B' ⟨ γ ; a ⟩).
Proof.
  set (N := maxmax nA nA' nB nB').
  pose proof (piTy_HO_inj_dom HA HB HA' HB' Hγ H) as HAA'.
  pose proof (piTy_HO_inj_dom_level HA HB HA' HB' Hγ H) as HnAA'. destruct HnAA'.
  refine (trans (b := cod_piTy_set N (piTy_HO nA nB A B γ)) _ _).
  { symmetry. refine (cod_piTy_set_eq _ _ HA HB Hγ) ; apply (maxmax_le nA nA nB nB'). }
  refine (trans (fequal (cod_piTy_set N) H) _).
  refine (transpS (fun X => _ ≡ typeToGraph nA nB' X _) (sym HAA') _).
  refine (cod_piTy_set_eq _ _ HA' HB' Hγ) ; apply (maxmax_le nA nA nB nB').
Qed.

Lemma piTy_HO_inj_cod {nA nA' nB nB' : nat} {Γ γ a : ZFSet} {A A' B B' : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (HA' : ∀ γ ∈ Γ, A' γ ∈ 𝕌 nA') (HB' : ∀ γa ∈ ctxExt nA' Γ A', B' γa ∈ 𝕌 nB')
  (Hγ : γ ∈ Γ) (H : piTy_HO nA nB A B γ ≡ piTy_HO nA' nB' A' B' γ) (Ha : a ∈ 𝕌el nA (A γ)) :
  B ⟨ γ ; a ⟩ ≡ B' ⟨ γ ; a ⟩.
Proof.
  pose proof (piTy_HO_inj_dom HA HB HA' HB' Hγ H) as HAA'.
  pose proof (piTy_HO_inj_dom_level HA HB HA' HB' Hγ H) as HnAA'. destruct HnAA'.
  pose proof (piTy_HO_inj_cod' HA HB HA' HB' Hγ H) as HBB'.
  pose proof (piTy_HO_inj_cod_level HA HB HA' HB' Hγ H) as HnBB'. destruct HnBB'.
  refine (trans (b := setAppArr (𝕌el nA (A γ)) (𝕌 nB) (typeToGraph nA nB (A γ) (fun a => B ⟨ γ ; a ⟩)) a) _ _).
  { symmetry. refine (trans _ _). apply setAppArr_HO ; try assumption.
    now apply (typeExt_typing HA HB). reflexivity. }
  refine (trans (fequal (fun X => setAppArr (𝕌el nA (A γ)) (𝕌 nB) X a) HBB') _).
  refine (trans _ _). apply setAppArr_HO ; try assumption. 2:reflexivity.
  intros a' Ha'. pose proof (transpS (fun X => a' ∈ 𝕌el nA X) HAA' Ha') as Ha''. cbn in Ha''. clear Ha'.
  revert a' Ha''. now apply (typeExt_typing HA' HB').
Qed.

(* Lambda abstraction *)

Definition lamTm_HO (nA nB : nat) (A t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => relToGraph (𝕌el nA (A γ)) (𝕍 (max nA nB)) (HO_rel (fun a => t ⟨ γ ; a ⟩)).

Lemma lamTm_HO_cong {nA nB : nat} {Γ : ZFSet} {A1 A2 t1 t2 : ZFSet -> ZFSet} 
  (HAe : ∀ γ ∈ Γ, A1 γ ≡ A2 γ) (Hte : ∀ γa ∈ ctxExt nA Γ A1, t1 γa ≡ t2 γa) :
  ∀ γ ∈ Γ, lamTm_HO nA nB A1 t1 γ ≡ lamTm_HO nA nB A2 t2 γ.
Proof.
  intros γ Hγ. unfold lamTm_HO. destruct (HAe γ Hγ). unfold relToGraph. unfold HO_rel. apply ZFext.
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
    + assumption.
    + refine (trans (sym _) Hx2). apply Hte. apply setMkSigma_typing ; try assumption.
      * intros. apply 𝕌el_typing'.
      * now apply setFstPair_typing. 
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
    + assumption.
    + refine (trans _ Hx2). apply Hte. apply setMkSigma_typing ; try assumption.
      * intros. apply 𝕌el_typing'.
      * now apply setFstPair_typing. 
Qed.
    

Lemma lamTm_HO_typing {nA nB : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γa ∈ ctxExt nA Γ A, t γa ∈ 𝕌el nB (B γa)) :
  ∀ γ ∈ Γ, lamTm_HO nA nB A t γ ∈ 𝕌el (max nA nB) (piTy_HO nA nB A B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_piTy HA HB Hγ)) _). apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing.
    intros a Ha. eapply ZFuniv_trans. now apply (termExt_typing HA HB Ht).
    eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - intros a Ha. refine (transpS (fun X => X ∈ 𝕌el nB (B ⟨ γ ; a ⟩)) _ (Ht ⟨ γ ; a ⟩ _)).
    + refine (sym _). refine (trans _ _). apply setAppArr_HO ; [ | assumption].
      intros a' Ha'. eapply ZFuniv_trans. now apply (termExt_typing HA HB Ht).
      eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
      reflexivity.
    + apply setMkSigma_typing ; try assumption. intros γ' Hγ'. apply 𝕌el_typing. now apply HA.
Qed.

Lemma lamTm_HO_typing_ir {nB : nat} {Γ : ZFSet} {A B t : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ Ω) (HB : ∀ γa ∈ ctxExt 0 Γ (boxTy_HO A), B γa ∈ 𝕌 nB)
  (Ht : ∀ γa ∈ ctxExt 0 Γ (boxTy_HO A), t γa ∈ 𝕌el nB (B γa)) :
  ∀ γ ∈ Γ, lamTm_HO 0 nB (boxTy_HO A) t γ ∈ 𝕌el nB (piTy_HO 0 nB (boxTy_HO A) B γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym _) (lamTm_HO_typing (boxTy_HO_typing HA) HB Ht γ Hγ)).
  refine (fequal (fun n => 𝕌el n _) _). destruct (eq_sym (Nat.max_0_l nB)). easy.
Qed.

(* Application *)

Definition appTm_HO (nA nB : nat) (A t u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => setAppArr (𝕌el nA (A γ)) (𝕍 (max nA nB)) (t γ) (u γ).

Lemma appTm_HO_cong {nA nB : nat} {Γ : ZFSet} {A1 A2 t1 t2 u1 u2 : ZFSet -> ZFSet} 
  (HAe : ∀ γ ∈ Γ, A1 γ ≡ A2 γ) (Hte : ∀ γ ∈ Γ, t1 γ ≡ t2 γ) (Hue : ∀ γ ∈ Γ, u1 γ ≡ u2 γ) :
  ∀ γ ∈ Γ, appTm_HO nA nB A1 t1 u1 γ ≡ appTm_HO nA nB A2 t2 u2 γ.
Proof.
  intros γ Hγ. unfold appTm_HO. destruct (HAe γ Hγ). destruct (Hte γ Hγ). destruct (Hue γ Hγ). reflexivity.
Qed.

Lemma appTm_HO_typing {nA nB : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el (max nA nB) (piTy_HO nA nB A B γ)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el nA (A γ)) :
  ∀ γ ∈ Γ, appTm_HO nA nB A t u γ ∈ 𝕌el nB (B ⟨ γ ; u γ ⟩).
Proof.
  intros γ Hγ. assert (t γ ∈ setPi (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩))) as Htγ.
  { refine (transpS (fun X => t γ ∈ X) _ (Ht γ Hγ)). now apply (el_piTy (Γ := Γ)). }
  cbn. unfold appTm_HO. apply ZFincomp in Htγ. destruct Htγ as [ _ H ].
  apply H. now apply Hu.
Qed.

(* Equations (β and η) *)

Lemma piTy_HO_β {nA nB : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γa ∈ ctxExt nA Γ A, t γa ∈ 𝕌el nB (B γa)) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el nA (A γ)) :
  ∀ γ ∈ Γ, appTm_HO nA nB A (lamTm_HO nA nB A t) u γ ≡ t ⟨ γ ; u γ ⟩.
Proof.
  intros γ Hγ. cbn. refine (trans _ _). apply setAppArr_HO ; try assumption. 3:reflexivity.
  - intros a Ha. eapply ZFuniv_trans. now apply (termExt_typing HA HB Ht).
    eapply univ_le_incl. apply Nat.le_max_r. apply 𝕌el_typing. now apply (typeExt_typing HA HB).
  - now apply Hu.
Qed.

Lemma piTy_HO_η {nA nB : nat} {Γ : ZFSet} {A B t u : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB)
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el (max nA nB) (piTy_HO nA nB A B γ)) :
  ∀ γ ∈ Γ, t γ ≡ lamTm_HO nA nB A (appTm_HO nA nB (fun γa => A (ctx_wk nA Γ A γa)) (fun γa => t (ctx_wk nA Γ A γa)) (ctx_var0 nA Γ A)) γ.
Proof.
  intros γ Hγ. cbn. unfold lamTm_HO. unfold appTm_HO.
  assert (t γ ∈ setPi (max nA nB) (𝕌el nA (A γ)) (fun a => 𝕌el nB (B ⟨ γ ; a ⟩))) as Ht'.
  { refine (transpS (fun X => t γ ∈ X) (el_piTy HA HB Hγ) _). now apply Ht. }
  apply ZFincomp in Ht'. destruct Ht' as [ Ht' _ ].
  apply (setArr_funext (A := 𝕌el nA (A γ)) (B := 𝕍 (max nA nB))).
  - exact Ht'.
  - apply relToGraph_typing. apply HO_rel_typing. intros a Ha.
    refine (transp2S (fun X Y => setAppArr (𝕌el nA (A X)) (𝕍 (max nA nB)) (t X) Y ∈ 𝕍 (max nA nB))
              (sym (ctxExtβ1 HA Hγ Ha)) (sym (ctxExtβ2 HA Hγ Ha)) _).
    apply setAppArr_typing. 2:assumption. exact Ht'.
  - intros a Ha. refine (sym _). refine (trans _ _). apply setAppArr_HO. 2:assumption.
    + clear a Ha. intros a Ha. 
      refine (transp2S (fun X Y => setAppArr (𝕌el nA (A X)) (𝕍 (max nA nB)) (t X) Y ∈ 𝕍 (max nA nB))
                (sym (ctxExtβ1 HA Hγ Ha)) (sym (ctxExtβ2 HA Hγ Ha)) _).
      apply setAppArr_typing. 2:assumption. exact Ht'.
    + refine (fequal2 (fun X Y => setAppArr (𝕌el nA (A X)) (𝕍 (max nA nB)) (t X) Y)
                ((ctxExtβ1 HA Hγ Ha)) ((ctxExtβ2 HA Hγ Ha))).
Qed.

(* Clipped versions (requires excluded middle) *)

Definition piTy_cl (Γ : ZFSet) (nA nB : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  clip Γ (piTy_HO nA nB A B).

Definition lamTm_cl (Γ : ZFSet) (nA nB : nat) (A t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  clip Γ (lamTm_HO nA nB A t).

Definition appTm_cl (Γ : ZFSet) (nA nB : nat) (A t u : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  clip Γ (appTm_HO nA nB A t u).

(* Lemma piTy_cl_typing {nA nB : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet} *)
(*   (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 nA) (HB : ∀ γa ∈ ctxExt nA Γ A, B γa ∈ 𝕌 nB) : *)
(*   ∀ γ ∈ Γ, piTy_cl Γ nA nB A B γ ∈ 𝕌 (max nA nB). *)

Require Import library.
Require Import ZF_axioms.

(* In this file, we replicate the basic set theoretic constructions (cartesian products, function
   types, dependent sums, dependent products, etc). *)

Lemma subset_trans {A B C : ZFSet} : A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof.
  intros H1 H2 a Ha. apply H2. apply H1. exact Ha.
Qed.

Lemma setComp_sorting (n : nat) {A : ZFSet} {P : ZFSet -> SProp} (HA : A ∈ 𝕍 n) : { x ϵ A ∣ P x } ∈ 𝕍 n.
Proof.
  assert ({ x ϵ A ∣ P x } ∈ 𝒫 A) as H.
  { apply ZFinpower. intros a Ha. apply ZFincomp in Ha. now destruct Ha. }
  apply (ZFuniv_trans _ _ _ H). now apply ZFuniv_power.
Qed.

Lemma setSingl_sorting {n : nat} {x : ZFSet} : x ∈ 𝕍 n -> setSingl x ∈ 𝕍 n.
Proof.
  intro H. now apply ZFuniv_pair.
Qed.

(* Empty set *)

Lemma empty_in_univ (n : nat) : ∅ ∈ 𝕍 n.
Proof.
  assert (∅ ∈ ω).
  { now apply ZFininfinity. }
  apply (ZFuniv_trans _ _ _ H). apply ZFuniv_uncountable.
Qed.

(* Functional relations *)

Definition setRel := ZFSet -> ZFSet -> SProp.

Definition isFunRel (A B : ZFSet) (φ : setRel) : SProp :=
  ∀ a ∈ A, ∃! b ∈ B, φ a b.

Definition funRelApp (A B : ZFSet) (φ : setRel) (a : ZFSet) : ZFSet :=
  ι { b ϵ B ∣ φ a b }.

Definition HO_rel (φ : ZFSet -> ZFSet) : setRel :=
  fun a b => φ a ≡ b.

Lemma funRelApp_pretyping {A B a : ZFSet} {φ : setRel} (Hφ : isFunRel A B φ) (Ha : a ∈ A) :
  funRelApp A B φ a ∈ { b ϵ B ∣ φ a b }.
Proof.
  apply ZFindescr. specialize (Hφ a Ha). destruct Hφ as [ b [ [ Hb Hφb ] Hu ] ].
  exists b. split.
  - apply ZFincomp. now split.
  - intros b' Hb'. apply ZFincomp in Hb'. now revert b' Hb'. 
Qed.

Lemma funRelApp_typing {A B a : ZFSet} {φ : setRel} (Hφ : isFunRel A B φ) (Ha : a ∈ A) :
  funRelApp A B φ a ∈ B.
Proof.
  pose proof (funRelApp_pretyping Hφ Ha).
  apply ZFincomp in H. exact (fstS H).
Qed.

Lemma funRelApp_inRel {A B a : ZFSet} {φ : setRel} (Hφ : isFunRel A B φ) (Ha : a ∈ A) :
  φ a (funRelApp A B φ a).
Proof.
  pose proof (funRelApp_pretyping Hφ Ha).
  apply ZFincomp in H. exact (sndS H).
Qed.

Lemma funRel_unique {A B a b1 b2 : ZFSet} {φ : setRel} (Hφ : isFunRel A B φ) (Ha : a ∈ A) (Hb1 : b1 ∈ B) (Hb2 : b2 ∈ B) :
  φ a b1 -> φ a b2 -> b1 ≡ b2.
Proof.
  specialize (Hφ a Ha). cbn in Hφ. destruct Hφ as [ b0 [ [ Hb0 Hb0' ] Hu ] ].
  intros Hb1' Hb2'. pose proof (Hu b1 (mkAndS Hb1 Hb1')) as e1. pose proof (Hu b2 (mkAndS Hb2 Hb2')) as e2.
  exact (trans (sym e1) e2).
Qed.

Lemma HO_rel_typing (A B : ZFSet) (φ : ZFSet -> ZFSet) (Hφ : ∀ a ∈ A, φ a ∈ B) :
  isFunRel A B (HO_rel φ).
Proof.
  intros a Ha. unshelve econstructor.
  - exact (φ a).
  - split. split.
    + now apply Hφ.
    + unfold HO_rel. reflexivity.
    + intros b [ Hb1 Hb2 ]. unfold HO_rel in Hb2. now symmetry.
Qed.

(* From functional relations to higher order functions and back *)

Lemma rel_HO_rel {A B : ZFSet} {φ : setRel} (Hφ : isFunRel A B φ) {a b : ZFSet} (Ha : a ∈ A) (Hb : b ∈ B) :
  φ a b ↔ HO_rel (funRelApp A B φ) a b.
Proof.
  split.
  - intro Hab. unfold HO_rel.
    exact (funRel_unique Hφ Ha (funRelApp_typing Hφ Ha) Hb (funRelApp_inRel Hφ Ha) Hab).
  - intro Hab. unfold HO_rel in Hab. 
    refine (transpS (φ a) Hab _). now apply funRelApp_inRel.
Qed.

Lemma HO_rel_HO {A B : ZFSet} {φ : ZFSet -> ZFSet} (Hφ : ∀ a ∈ A, φ a ∈ B) {a : ZFSet} (Ha : a ∈ A) :
  φ a ≡ funRelApp A B (HO_rel φ) a.
Proof.
  pose proof (funRelApp_pretyping (HO_rel_typing A B φ Hφ) Ha) as H.
  apply ZFincomp in H. destruct H as [ _ H ]. unfold HO_rel in H. now symmetry.
Qed.

(* Identity and composition *)
  
Definition relId : setRel := HO_rel (fun x => x).

Definition relComp (A B C : ZFSet) (φ ψ : setRel) : setRel :=
  fun x z => ∃ y ∈ B, φ x y ∧ ψ y z.

Definition funRelComp (A B C : ZFSet) (φ ψ : setRel) : setRel :=
  HO_rel (fun x => funRelApp B C ψ (funRelApp A B φ x)).

Lemma funRelId_typing (A : ZFSet) : isFunRel A A relId.
Proof.
  now apply HO_rel_typing. 
Qed.

Lemma funRelComp_typing {A B C : ZFSet} {φ ψ : setRel} (Hφ : isFunRel A B φ) (Hψ : isFunRel B C ψ) : isFunRel A C (funRelComp A B C φ ψ).
Proof.
  apply HO_rel_typing. intros a Ha.
  apply funRelApp_typing. assumption.
  now apply funRelApp_typing.
Qed.

Lemma funRelComp_eval {A B C a : ZFSet} {φ ψ : setRel} (Hφ : isFunRel A B φ) (Hψ : isFunRel B C ψ) (Ha : a ∈ A) :
  funRelApp A C (funRelComp A B C φ ψ) a ≡ funRelApp B C ψ (funRelApp A B φ a).
Proof.
  symmetry. apply (HO_rel_HO (φ := fun x => funRelApp B C ψ (funRelApp A B φ x))).
  - intros a' Ha'. apply funRelApp_typing. assumption.
    now apply funRelApp_typing.
  - assumption.
Qed.

(* Union of two sets *)

Definition setUnion (A B : ZFSet) : ZFSet := ⋃ { A ; B }.
Notation "A ∪ B" := (setUnion A B) (at level 35, right associativity).

Lemma inSetUnion (A B : ZFSet) : forall x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
Proof.
  intro x. split.
  - intro H. apply ZFinunion in H. destruct H as [ X [ HX Hx ] ].
    apply ZFinpairing in HX. destruct HX as [ H | H ].
    + left. exact (transpS (fun A => x ∈ A) H Hx).
    + right. exact (transpS (fun B => x ∈ B) H Hx).
  - intros [ Hx | Hx ].
    + apply ZFinunion. exists A. split.
      * apply ZFinpairing. now left.
      * assumption.
    + apply ZFinunion. exists B. split.
      * apply ZFinpairing. now right.
      * assumption.
Qed.

Lemma setUnion_typing (n : nat) {A B : ZFSet} (HA : A ∈ 𝕍 n) (HB : B ∈ 𝕍 n) : A ∪ B ∈ 𝕍 n.
Proof.
  assert (⋃ { x ϵ 𝕍 n ∣ ∃ i ∈ { A ; B }, i ≡ x } ∈ 𝕍 n).
  { apply ZFuniv_union. now apply ZFuniv_pair. intros x Hx. exists x. split.
    - split. apply (ZFuniv_trans _ _ _ Hx). now apply ZFuniv_pair. easy.
    - intros y [ _ Hy ]. exact Hy. }
  refine (transpS (fun X => X ∈ 𝕍 n) _ H). clear H. apply ZFext.
  - intros x Hx. apply ZFinunion in Hx. destruct Hx as [ y [ Hy Hxy ] ].
    apply ZFincomp in Hy. destruct Hy as [ Hy1 [ z [ Hz Hyz ] ] ]. destruct Hyz.
    apply ZFinpairing in Hz. destruct Hz as [ Hz | Hz ] ; destruct Hz ; apply inSetUnion.
    now left. now right.
  - intros x Hx. apply inSetUnion in Hx. apply ZFinunion. destruct Hx as [ Hx | Hx ].
    + exists A. split ; [ | assumption ]. apply ZFincomp. split ; [ assumption | ].
      exists A. split ; [ | easy ]. apply ZFinpairing. now left.
    + exists B. split ; [ | assumption ]. apply ZFincomp. split ; [ assumption | ].
      exists B. split ; [ | easy ]. apply ZFinpairing. now right.
Qed.

(* Intersection of two sets *)

Definition setInter (A B : ZFSet) : ZFSet := { x ϵ A ∣ x ∈ B }.
Notation "A ∩ B" := (setInter A B) (at level 30, right associativity).
Lemma inSetInter (A B : ZFSet) : forall x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B.
Proof.
  intro x. split.
  + intro H. apply ZFincomp in H. exact H.
  + intro H. apply ZFincomp. exact H.
Qed.

(* Kuratowski pairs and cartesian products *)

Definition setMkPair (a b : ZFSet) := { setSingl a ; {a ; b} }.
Notation "⟨ a ; b ⟩" := (setMkPair a b) (at level 0).

Definition setProd (A B : ZFSet) : ZFSet := { x ϵ 𝒫 (𝒫 (A ∪ B)) ∣ ∃ a ∈ A, ∃ b ∈ B, x ≡ ⟨ a ; b ⟩ }.
Notation "A × B" := (setProd A B) (at level 26, right associativity).

Definition isSetFst (a x : ZFSet) : SProp := ∀ y ∈ x, a ∈ y.
Definition setFstPair (A B : ZFSet) : ZFSet -> ZFSet := fun x => ι { a ϵ A ∣ isSetFst a x }.

Definition isSetSnd (a x : ZFSet) : SProp := exU ZFSet (fun y => y ∈ x ∧ a ∈ y).
Definition setSndPair (A B : ZFSet) : ZFSet -> ZFSet := fun x => ι { b ϵ B ∣ isSetSnd b x }.

Lemma setProd_typing (n : nat) {A B : ZFSet} (HA : A ∈ 𝕍 n) (HB : B ∈ 𝕍 n) : A × B ∈ 𝕍 n.
Proof.
  unfold setProd. apply setComp_sorting. apply ZFuniv_power. apply ZFuniv_power.
  now apply setUnion_typing.
Qed.

Lemma setMkPair_pretyping {A B a b : ZFSet} (Ha : a ∈ A) (Hb : b ∈ B) : ⟨ a ; b ⟩ ∈ 𝒫 (𝒫 (A ∪ B)).
Proof.
  apply ZFinpower. intros x Hx. apply ZFinpower. intros y Hy. apply inSetUnion.
  apply ZFinpairing in Hx. destruct Hx as [ Hx | Hx ].
  - left. apply (transpS (fun x => y ∈ x) Hx) in Hy. apply inSetSingl in Hy. apply (transpS (fun y => y ∈ A) (sym Hy)). assumption.
  - apply (transpS (fun x => y ∈ x) Hx) in Hy. apply ZFinpairing in Hy. destruct Hy as [ Hy | Hy ].
    + left. apply (transpS (fun y => y ∈ A) (sym Hy)). assumption.
    + right. apply (transpS (fun y => y ∈ B) (sym Hy)). assumption.
Qed.

Lemma setMkPair_typing {A B a b : ZFSet} : a ∈ A -> b ∈ B -> ⟨ a ; b ⟩ ∈ A × B.
Proof.
  intros Ha Hb. apply ZFincomp. split.
  - apply setMkPair_pretyping. exact Ha. exact Hb.
  - exists a. split.
    + exact Ha.
    + exists b. split. exact Hb. reflexivity.
Qed.

Lemma setMkPair_sorting {n : nat} {x y : ZFSet} (Hx : x ∈ 𝕍 n) (Hy : y ∈ 𝕍 n) : ⟨ x ; y ⟩ ∈ 𝕍 n.
Proof.
  apply ZFuniv_pair.
  - now apply ZFuniv_pair.
  - now apply ZFuniv_pair.
Qed.

Lemma setFstPair_pretyping {A B x : ZFSet} (Hx : x ∈ A × B) : setFstPair A B x ∈ { a ϵ A ∣ isSetFst a x }.
Proof.
  apply ZFindescr. apply ZFincomp in Hx.
  destruct Hx as [ Hx1 [ a [ Ha [ b [ Hb H ] ] ] ] ]. exists a. split.
  - apply ZFincomp. split. exact Ha. apply (transpS (isSetFst a) (sym H)). clear x Hx1 H.
    intros x Hx. apply ZFinpairing in Hx. destruct Hx as [ Hx | Hx ].
    + apply (transpS (fun x => a ∈ x) (sym Hx)). apply inSetSingl. reflexivity.
    + apply (transpS (fun x => a ∈ x) (sym Hx)). apply ZFinpairing. left. reflexivity.
  - intros a' Ha'. apply ZFincomp in Ha'. destruct Ha' as [ Ha' Habs ].
    assert (setSingl a ∈ ⟨ a ; b ⟩) as Hsingla. { apply ZFinpairing. now left. }
    apply (transpS (isSetFst a') H) in Habs. unfold isSetFst in Habs.
    specialize (Habs (setSingl a) Hsingla). apply inSetSingl in Habs. now symmetry.
Qed.

Lemma setFstPair_typing {A B x : ZFSet} (Hx : x ∈ A × B) : setFstPair A B x ∈ A.
Proof.
  pose proof (setFstPair_pretyping Hx) as H. apply ZFincomp in H. exact (fstS H).
Qed.

Lemma setPairβ1' {A B a b : ZFSet} (Hab : ⟨ a ; b ⟩ ∈ A × B) : setFstPair A B ⟨ a ; b ⟩ ≡ a.
Proof.
  set (x := setFstPair A B ⟨ a; b ⟩).
  pose proof (setFstPair_pretyping Hab) as Hx. change (x ∈ {a0 ϵ A ∣ isSetFst a0 ⟨ a ; b ⟩}) in Hx.
  clearbody x. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. unfold isSetFst in Hx2.
  assert (x ∈ setSingl a). { apply Hx2. apply ZFinpairing. left. reflexivity. }
  apply inSetSingl in H. exact H.
Qed.

Lemma setPairβ1 {A B a b : ZFSet} (Ha : a ∈ A) (Hb : b ∈ B) : setFstPair A B ⟨ a ; b ⟩ ≡ a.
Proof.
  exact (setPairβ1' (setMkPair_typing Ha Hb)).
Qed.

Lemma isSetSnd_unique {a b b' : ZFSet} : isSetSnd b' ⟨ a ; b ⟩ -> b ≡ b'.
Proof.
  intros [ x [ [ Hx1 Hx2 ] Hx3 ] ]. 
  apply ZFinpairing in Hx1. destruct Hx1 as [ Hx1 | Hx1 ] ; symmetry in Hx1 ; destruct Hx1.
  - apply inSetSingl in Hx2. symmetry in Hx2. destruct Hx2.
    assert (setSingl a ≡ {a ; b}). 
    { apply Hx3. split ; apply ZFinpairing. now right. now left. }
    assert (b ∈ setSingl a) as Hb.
    { symmetry in H. destruct H. apply ZFinpairing. now right. }
    now apply inSetSingl in Hb.
  - apply ZFinpairing in Hx2. destruct Hx2 as [ Hb' | Hb' ].
    + symmetry in Hb'. destruct Hb'.
      assert ({a ; b} ≡ setSingl a). 
      { apply Hx3. split ; apply ZFinpairing. now left. now right. }
      assert (b ∈ setSingl a) as Hb.
      { destruct H. apply ZFinpairing. now right. }
      now apply inSetSingl in Hb.
    + now symmetry.
Qed.

Lemma setSndPair_pretyping {A B x : ZFSet} (Hx : x ∈ A × B) : setSndPair A B x ∈ { b ϵ B ∣ isSetSnd b x }.
Proof.
  apply ZFindescr. apply ZFincomp in Hx.
  destruct Hx as [ Hx1 [ a [ Ha [ b [ Hb H ] ] ] ] ].
  assert (isSetSnd b ⟨ a ; b ⟩) as Hbsnd. 
  { clear x Hx1 H. exists { a ; b }. split.
    + split ; apply ZFinpairing ; right ; reflexivity.
    + intros x [ Hx1 Hx2 ]. apply ZFinpairing in Hx1. destruct Hx1 as [ Hx1 | Hx1 ].
      * apply (transpS (fun x => {a ; b} ≡ x) (sym Hx1)).
        apply (transpS (fun x => b ∈ x) Hx1) in Hx2. apply inSetSingl in Hx2.
        apply (transpS (fun b => {a ; b} ≡ setSingl a) (sym Hx2)). reflexivity.
      * apply (transpS (fun x => {a ; b} ≡ x) (sym Hx1)). reflexivity. }
  exists b. split.
  - apply ZFincomp. split ; try assumption. now apply (transpS (isSetSnd b) (sym H)).
  - intros b' Hb'. apply ZFincomp in Hb'. destruct Hb' as [ Hb' Habs ].
    apply (transpS (isSetSnd b') H) in Habs. now apply isSetSnd_unique in Habs.
Qed.

Lemma setSndPair_typing {A B x : ZFSet} (Hx : x ∈ A × B) : setSndPair A B x ∈ B.
Proof.
  pose proof (setSndPair_pretyping Hx) as H. apply ZFincomp in H. exact (fstS H).
Qed.

Lemma setPairβ2' {A B a b : ZFSet} (Hab : ⟨ a ; b ⟩ ∈ A × B) : setSndPair A B ⟨ a ; b ⟩ ≡ b.
Proof.
  set (b' := setSndPair A B ⟨ a ; b ⟩).
  pose proof (setSndPair_pretyping Hab) as Hb'. change (b' ∈ {b0 ϵ B ∣ isSetSnd b0 ⟨ a ; b ⟩}) in Hb'.
  clearbody b'. apply ZFincomp in Hb'. destruct Hb' as [ Hb' [ x [ [ Hx Hb'x ] Hu ] ] ].
  assert (b' ≡ a -> b' ≡ b) as H.
  { clear Hx. intro H.
    assert (x ≡ setSingl a) as H1. { apply Hu. split. apply ZFinpairing. now left. apply inSetSingl. exact H. }
    assert (x ≡ { a ; b }) as H2. { apply Hu. split. apply ZFinpairing. now right. apply ZFinpairing. now left. }
    assert (∀ z ∈ x, b' ≡ z) as H3. { intros z Hz. apply (transpS (fun x => z ∈ x) H1) in Hz. apply inSetSingl in Hz. exact (trans H (sym Hz)). }
    apply H3. apply (transpS (fun x => b ∈ x) (sym H2)). apply ZFinpairing. now right. }
  clear Hu. apply ZFinpairing in Hx. destruct Hx as [ Hx | Hx ] ; apply (transpS (fun x => b' ∈ x) Hx) in Hb'x.
  - apply inSetSingl in Hb'x. apply H. exact Hb'x.
  - apply ZFinpairing in Hb'x. destruct Hb'x as [ Hb'x | Hb'x ].
    + apply H. exact Hb'x.
    + exact Hb'x.
Qed.

Lemma setPairβ2 {A B a b : ZFSet} (Ha : a ∈ A) (Hb : b ∈ B) : setSndPair A B ⟨ a ; b ⟩ ≡ b.
Proof.
  exact (setPairβ2' (setMkPair_typing Ha Hb)).
Qed.

Lemma setPairη {A B x : ZFSet} (Hx : x ∈ A × B) : x ≡ ⟨ setFstPair A B x ; setSndPair A B x ⟩.
Proof.
  apply ZFincomp in Hx. destruct Hx as [ Hx [ a [ Ha [ b [ Hb H ] ] ] ] ].
  apply (transpS (fun y => y ≡ ⟨ setFstPair A B y; setSndPair A B y ⟩) (sym H)). clear x Hx H.
  apply (transpS (fun x => ⟨ x ; b ⟩ ≡ ⟨ setFstPair A B ⟨ a ; b ⟩; setSndPair A B ⟨ a ; b ⟩ ⟩) (setPairβ1 Ha Hb)).
  apply (transpS (fun x => ⟨ setFstPair A B ⟨ a ; b ⟩ ; x ⟩ ≡ ⟨ setFstPair A B ⟨ a ; b ⟩; setSndPair A B ⟨ a ; b ⟩ ⟩) (setPairβ2 Ha Hb)).
  reflexivity.
Qed.

Lemma setMkPair_detyping {A B a b : ZFSet} : ⟨ a ; b ⟩ ∈ A × B -> a ∈ A ∧ b ∈ B.
Proof.
  intro H. split.
  - assert (setFstPair A B ⟨ a ; b ⟩ ≡ a) as Ha.
    { now apply setPairβ1'. }
    refine (transpS (fun X => X ∈ A) Ha _). now apply setFstPair_typing.
  - assert (setSndPair A B ⟨ a ; b ⟩ ≡ b) as Hb.
    { now apply setPairβ2'. }
    refine (transpS (fun X => X ∈ B) Hb _). now apply setSndPair_typing.
Qed.

Lemma setProd_incl {A B C D : ZFSet} : A ⊂ C -> B ⊂ D -> A × B ⊂ C × D.
Proof.
  intros H1 H2 x Hx. pose proof (setPairη Hx).
  refine (transpS (fun X => X ∈ C × D) (sym H) _). clear H.
  apply setMkPair_typing.
  - assert (setFstPair A B x ∈ A) as H. { now apply setFstPair_typing. } now apply H1. 
  - assert (setSndPair A B x ∈ B) as H. { now apply setSndPair_typing. } now apply H2. 
Qed.  

(* Image of a higher-order function (without replacement) *)

Definition setRelIm (A B : ZFSet) (f : setRel) : ZFSet :=
  { b ϵ B ∣ ∃ a ∈ A, f a b }.

Definition setIm (A B : ZFSet) (f : ZFSet -> ZFSet) : ZFSet :=
  setRelIm A B (HO_rel f).

Lemma setIm_typing {A B a : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ a ∈ A, f a ∈ B) (Ha : a ∈ A) : f a ∈ setIm A B f.
Proof.
  apply ZFincomp. split.
  - now apply Hf.
  - exists a. now split.
Qed.

(* Union of an indexed family in 𝕍 n *)

Definition setFamUnion (n : nat) (A : ZFSet) (f : ZFSet -> ZFSet) : ZFSet :=
  ⋃ (setIm A (𝕍 n) f).

Lemma inSetFamUnion {n : nat} {A a b : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ a ∈ A, f a ∈ 𝕍 n) (Ha : a ∈ A) (Hb : b ∈ f a) :
  b ∈ setFamUnion n A f.
Proof.
  apply ZFinunion. exists (f a). split.
  - exact (setIm_typing Hf Ha).
  - exact Hb.
Qed.

Lemma setFamUnion_typing (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  setFamUnion n A B ∈ 𝕍 n.
Proof.
  apply ZFuniv_union. assumption. now apply HO_rel_typing.
Qed.

(* Sigma types *)

Definition setSigma (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) : ZFSet :=
  { x ϵ (A × setFamUnion n A B) ∣ setSndPair A (setFamUnion n A B) x ∈ B (setFstPair A (setFamUnion n A B) x) }.

Definition setMkSigma (a b : ZFSet) := ⟨ a ; b ⟩.
Definition setFstSigma (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) (x : ZFSet) : ZFSet :=
  setFstPair A (setFamUnion n A B) x.
Definition setSndSigma (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) (x : ZFSet) : ZFSet :=
  setSndPair A (setFamUnion n A B) x.

Lemma setMkSigma_typing {n : nat} {A a b : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) (Ha : a ∈ A) (Hb : b ∈ B a)
  : ⟨ a ; b ⟩ ∈ setSigma n A B.
Proof.
  apply ZFincomp. split.
  - apply (setMkPair_typing Ha). apply (inSetFamUnion HB Ha Hb).
  - apply (transpS (fun x => x ∈ B (setFstPair A (setFamUnion n A B) ⟨ a; b ⟩))
                   (sym (setPairβ2 Ha (inSetFamUnion HB Ha Hb)))).
    apply (transpS (fun x => b ∈ B x) (sym (setPairβ1 Ha (inSetFamUnion HB Ha Hb)))).
    exact Hb.
Qed.

Lemma setFstSigma_typing {n : nat} {A x : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) (Hx : x ∈ setSigma n A B)
  : setFstSigma n A B x ∈ A.
Proof.
  apply ZFincomp in Hx.
  exact (setFstPair_typing (fstS Hx)).
Qed.

Lemma setSndSigma_typing {n : nat} {A x : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) (Hx : x ∈ setSigma n A B)
  : setSndSigma n A B x ∈ B (setFstSigma n A B x).
Proof.
  apply ZFincomp in Hx.
  exact (sndS Hx).
Qed.

Lemma setSigmaβ1 {n : nat} {A a b : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) (Ha : a ∈ A) (Hb : b ∈ B a)
  : setFstSigma n A B ⟨ a ; b ⟩ ≡ a.
Proof.
  exact (setPairβ1 Ha (inSetFamUnion HB Ha Hb)).
Qed.

Lemma setSigmaβ2 {n : nat} {A a b : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) (Ha : a ∈ A) (Hb : b ∈ B a)
  : setSndSigma n A B ⟨ a ; b ⟩ ≡ b.
Proof.
  exact (setPairβ2 Ha (inSetFamUnion HB Ha Hb)).
Qed.

Lemma setSigmaη {n : nat} {A x : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) (Hx : x ∈ setSigma n A B)
  : x ≡ ⟨ setFstSigma n A B x ; setSndSigma n A B x ⟩.
Proof.
  apply ZFincomp in Hx. apply fstS in Hx.
  exact (setPairη Hx).
Qed.

Lemma setMkSigma_detyping {n : nat} {A a b : ZFSet} {B : ZFSet -> ZFSet} (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  ⟨ a ; b ⟩ ∈ setSigma n A B -> a ∈ A ∧ b ∈ B a.
Proof.
  intro H0. pose proof H0 as H. apply ZFincomp in H. destruct H as [ H _ ].
  assert (a ∈ A) as Ha.
  { apply setMkPair_detyping in H. now destruct H. }
  split. exact Ha.
  assert (setFstSigma n A B ⟨ a ; b ⟩ ≡ a) as Ha2.
  { now apply setPairβ1'. }
  assert (setSndSigma n A B ⟨ a ; b ⟩ ≡ b) as Hb.
  { now apply setPairβ2'. }
  refine (transp2S (fun X Y => X ∈ B Y) Hb Ha2 _).
  now apply setSndSigma_typing. 
Qed.

Lemma setSigma_pretyping (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  setSigma n A B ⊂ A × 𝕍 n.
Proof.
  intros x Hx. apply ZFincomp in Hx.
  destruct Hx as [ Hx _ ]. unshelve eapply (setProd_incl _ _ x Hx).
  - easy.
  - intros y Hy. apply (ZFuniv_trans _ _ _ Hy). now apply setFamUnion_typing.
Qed.

Lemma setSigma_typing (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  setSigma n A B ∈ 𝕍 n.
Proof.
  unfold setSigma. apply setComp_sorting. apply setProd_typing.
  assumption. now apply setFamUnion_typing.
Qed.

(* Function types (exponentials) as sets of graphs *)

Definition graphToRel (R : ZFSet) : setRel := fun a b => ⟨ a ; b ⟩ ∈ R.

Definition setArr (A B : ZFSet) := { R ϵ 𝒫 (A × B) ∣ isFunRel A B (graphToRel R) }.
Notation "A ⇒ B" := (setArr A B) (at level 26, right associativity).

Definition setAppArr (A B f x : ZFSet) := funRelApp A B (graphToRel f) x.

Definition relToGraph (A B : ZFSet) (φ : setRel) : ZFSet := { x ϵ A × B ∣ φ (setFstPair A B x) (setSndPair A B x) }.

Definition setIdArr (A : ZFSet) := relToGraph A A (fun x y => x ≡ y).

Definition setCompArr' (A B C f g : ZFSet) := relToGraph A C (relComp A B C (graphToRel f) (graphToRel g)).
Definition setCompArr (A B C f g : ZFSet) := relToGraph A C (funRelComp A B C (graphToRel f) (graphToRel g)).

Lemma graphToRel_typing {A B f} (Hf : f ∈ A ⇒ B) : isFunRel A B (graphToRel f).
Proof.
  apply ZFincomp in Hf. exact (sndS Hf).
Qed.

Lemma setAppArr_typing {A B f a : ZFSet} (Hf : f ∈ A ⇒ B) (Ha : a ∈ A) : setAppArr A B f a ∈ B.
Proof.
  exact (funRelApp_typing (graphToRel_typing Hf) Ha).
Qed.

Lemma setAppArr_inRel {A B f a : ZFSet} (Hf : f ∈ A ⇒ B) (Ha : a ∈ A) : graphToRel f a (setAppArr A B f a).
Proof.
  exact (funRelApp_inRel (graphToRel_typing Hf) Ha).
Qed.

Lemma graphToRelToGraph {A B f : ZFSet} (Hf : f ∈ A ⇒ B) : relToGraph A B (graphToRel f) ≡ f.
Proof.
  apply ZFincomp in Hf. destruct Hf as [ Hf Hf2 ]. apply ZFext.
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx Hx2 ]. unfold graphToRel in Hx2.
    apply (transpS (fun x => x ∈ f) (sym (setPairη Hx))). exact Hx2.
  - intros x Hx. apply ZFincomp. apply ZFinpower in Hf. split.
    + exact (Hf x Hx).
    + unfold graphToRel. apply (transpS (fun x => x ∈ f) (setPairη (Hf x Hx))). exact Hx.
Qed.

Lemma relToGraphToRel {A B a b : ZFSet} {f : setRel} (Hf : isFunRel A B f) (Ha : a ∈ A) (Hb : b ∈ B) :
  (graphToRel (relToGraph A B f)) a b ↔ f a b.
Proof.
  split.
  - intro H. unfold graphToRel in H. apply ZFincomp in H. destruct H as [ H H2 ].
    apply (transpS (fun x => f x b) (setPairβ1 Ha Hb)).
    apply (transpS (fun x => f (setFstPair A B ⟨ a; b ⟩) x) (setPairβ2 Ha Hb)). exact H2.
  - intro H. unfold graphToRel. apply ZFincomp. split.
    + exact (setMkPair_typing Ha Hb).
    + apply (transpS (fun x => f x (setSndPair A B ⟨ a; b ⟩)) (sym (setPairβ1 Ha Hb))).
      apply (transpS (fun x => f a x) (sym (setPairβ2 Ha Hb))). exact H.
Qed.

Lemma relToGraph_typing {A B : ZFSet} {φ : setRel} (Hφ : isFunRel A B φ) : relToGraph A B φ ∈ A ⇒ B.
Proof.
  apply ZFincomp. split.
  - apply ZFinpower. intros x Hx. apply ZFincomp in Hx. exact (fstS Hx).
  - intros a Ha. exists (funRelApp A B φ a). split.
    + split. exact (funRelApp_typing Hφ Ha). apply (relToGraphToRel Hφ Ha (funRelApp_typing Hφ Ha)).
      exact (funRelApp_inRel Hφ Ha).
    + intros b [ Hb Hb2 ]. apply (relToGraphToRel Hφ Ha Hb) in Hb2.
      apply (funRel_unique Hφ Ha (funRelApp_typing Hφ Ha) Hb). exact (funRelApp_inRel Hφ Ha). exact Hb2.
Qed.

Lemma setAppArr_rel {A B a : ZFSet} {f : setRel} (Hf : isFunRel A B f) (Ha : a ∈ A) :
  f a (setAppArr A B (relToGraph A B f) a).
Proof.
  pose proof (setAppArr_inRel (relToGraph_typing Hf) Ha).
  unshelve eapply (relToGraphToRel Hf Ha _).
  apply setAppArr_typing. now apply relToGraph_typing. assumption.
  exact H.
Qed.

Lemma setAppArr_HO {A B a : ZFSet} {f : ZFSet -> ZFSet} (Hf : ∀ a ∈ A, f a ∈ B) (Ha : a ∈ A) :
  setAppArr A B (relToGraph A B (HO_rel f)) a ≡ f a.
Proof.
  pose proof (HO_rel_typing A B f Hf) as Hf'.
  apply (funRel_unique Hf' Ha).
  - apply setAppArr_typing. now apply relToGraph_typing. assumption.
  - now apply Hf.
  - apply (setAppArr_rel Hf' Ha).
  - unfold HO_rel. reflexivity.
Qed.

Lemma relToGraphToRel_app {A B a : ZFSet} {f : setRel} (Hf : isFunRel A B f) (Ha : a ∈ A) :
  funRelApp A B (graphToRel (relToGraph A B f)) a ≡ funRelApp A B f a.
Proof.
  pose proof (relToGraph_typing Hf) as Hf'. pose proof (graphToRel_typing Hf') as Hf''.
  pose proof (funRelApp_inRel Hf Ha) as H1. pose proof (funRelApp_inRel Hf'' Ha) as H2.
  apply (relToGraphToRel Hf Ha (funRelApp_typing Hf'' Ha)) in H2.
  apply (funRel_unique Hf Ha (funRelApp_typing Hf'' Ha) (funRelApp_typing Hf Ha) H2 H1).
Qed.

Lemma inSetArr_l {A B f x : ZFSet} (Hf : f ∈ A ⇒ B) :
  x ∈ f -> setSndPair A B x ≡ setAppArr A B f (setFstPair A B x).
Proof.
  intro H. apply (transpS (fun f => x ∈ f) (sym (graphToRelToGraph Hf))) in H.
  apply ZFincomp in H. destruct H as [ Hx H ].
  apply (funRel_unique (graphToRel_typing Hf) (setFstPair_typing Hx) (setSndPair_typing Hx) (setAppArr_typing Hf (setFstPair_typing Hx)) H).
  exact (setAppArr_inRel Hf (setFstPair_typing Hx)).
Qed.

Lemma inSetArr_r {A B f x : ZFSet} (Hf : f ∈ A ⇒ B) (Hx : x ∈ A × B) :
  setSndPair A B x ≡ setAppArr A B f (setFstPair A B x) -> x ∈ f.
Proof.
  intro H. apply (transpS (fun f => x ∈ f) (graphToRelToGraph Hf)).
  apply ZFincomp. split. exact Hx.
  pose proof Hf as Hf0. apply ZFincomp in Hf. destruct Hf as [ Hf1 Hf2 ]. specialize (Hf2 (setFstPair A B x) (setFstPair_typing Hx)).
  destruct Hf2 as [ b [ [ Hb Hab ] _ ] ].
  assert (b ≡ setSndPair A B x). { refine (trans _ (sym H)).
    apply (funRel_unique (graphToRel_typing Hf0) (setFstPair_typing Hx) Hb (setAppArr_typing Hf0 (setFstPair_typing Hx)) Hab).
    exact (setAppArr_inRel Hf0 (setFstPair_typing Hx)). }
  apply (transpS (fun y => graphToRel f (setFstPair A B x) y) H0). exact Hab.
Qed.

Lemma setArr_typing {n : nat} {A B : ZFSet} (HA : A ∈ 𝕍 n) (HB : B ∈ 𝕍 n) : A ⇒ B ∈ 𝕍 n.
Proof.
  apply setComp_sorting. apply ZFuniv_power. now apply setProd_typing.
Qed.

Lemma setArr_big_typing {n : nat} {A B : ZFSet} (HA : A ∈ 𝕍 n) (HB : B ⊂ 𝕍 n) : A ⇒ B ⊂ 𝕍 n.
Proof.
  intros f Hf. assert (f ≡ ⋃ { x ϵ 𝕍 n ∣ ∃ a ∈ A, x ≡ setSingl ⟨ a ; setAppArr A B f a ⟩ }) as H.
  { apply ZFext.
    - intros x Hx. pose proof Hf as H. apply ZFincomp in H. destruct H as [ H _ ].
      apply ZFinpower in H. specialize (H _ Hx). apply (inSetArr_l Hf) in Hx.
      apply ZFinunion. exists (setSingl x). split ; [ | now apply inSetSingl ]. apply ZFincomp. split.
      + apply setSingl_sorting. refine (transpS (fun X => X ∈ 𝕍 n) (sym (setPairη H)) _).
        apply setMkPair_sorting. eapply ZFuniv_trans. now apply setFstPair_typing. assumption.
        apply HB. now apply setSndPair_typing.
      + exists (setFstPair A B x). split. now apply setFstPair_typing. apply fequal.
        refine (transpS (fun X => x ≡ ⟨ _ ; X ⟩) Hx _). now apply setPairη.
    - intros x Hx. apply ZFinunion in Hx. destruct Hx as [ y [ Hy Hxy ] ].
      apply ZFincomp in Hy. destruct Hy as [ _ [ a [ Ha Hy ] ] ]. assert (x ≡ ⟨ a ; setAppArr A B f a ⟩).
      { apply inSetSingl. exact (transpS (fun X => x ∈ X) Hy Hxy). } apply (inSetArr_r Hf).
      + refine (transpS (fun X => X ∈ A × B) (sym H) _).
        apply setMkPair_typing. assumption. now apply setAppArr_typing.
      + refine (transpS (fun X => setSndPair A B X ≡ setAppArr A B f (setFstPair A B X)) (sym H) _).
        refine (trans _ _). apply setPairβ2. assumption. now apply setAppArr_typing.
        refine (fequal (setAppArr A B f) _). refine (sym _). apply setPairβ1.
        assumption. now apply setAppArr_typing. }
  refine (transpS (fun X => X ∈ 𝕍 n) (sym H) _). apply ZFuniv_union.
  assumption. intros a Ha. exists (setSingl ⟨ a; setAppArr A B f a ⟩). split.
  - split ; [ | reflexivity ]. apply setSingl_sorting. apply setMkPair_sorting.
    + eapply ZFuniv_trans. exact Ha. exact HA.
    + apply HB. now apply setAppArr_typing.
  - intros y [ _ Hy ]. exact (sym Hy).
Qed.

Lemma setArr_funext {A B f g : ZFSet} (Hf : f ∈ A ⇒ B) (Hg : g ∈ A ⇒ B) :
  (∀ a ∈ A, setAppArr A B f a ≡ setAppArr A B g a) -> f ≡ g.
Proof.
  intro H. pose proof Hf as Hf0. pose proof Hg as Hg0.
  apply ZFincomp in Hf. destruct Hf as [ Hf _ ]. apply ZFinpower in Hf.
  apply ZFincomp in Hg. destruct Hg as [ Hg _ ]. apply ZFinpower in Hg.
  apply ZFext.
  - intros x Hx. pose proof (trans (inSetArr_l Hf0 Hx) (H (setFstPair A B x) (setFstPair_typing (Hf x Hx)))) as H1.
    exact (inSetArr_r Hg0 (Hf x Hx) H1).
  - intros x Hx. pose proof (trans (inSetArr_l Hg0 Hx) (sym (H (setFstPair A B x) (setFstPair_typing (Hg x Hx))))) as H1.
    exact (inSetArr_r Hf0 (Hg x Hx) H1).
Qed.

Lemma setIdArr_typing (A : ZFSet) : setIdArr A ∈ A ⇒ A.
Proof.
  apply relToGraph_typing. exact (funRelId_typing A).
Qed.

Lemma setIdArr_app {A a : ZFSet} (Ha : a ∈ A) : setAppArr A A (setIdArr A) a ≡ a.
Proof.
  pose proof (setAppArr_inRel (setIdArr_typing A) Ha). unfold setIdArr in H.
  apply (relToGraphToRel (funRelId_typing A) Ha (setAppArr_typing (setIdArr_typing A) Ha)) in H.
  exact (sym H).
Qed.

Lemma setCompArr_typing {A B C f g : ZFSet} (Hf : f ∈ A ⇒ B) (Hg : g ∈ B ⇒ C) : setCompArr A B C f g ∈ A ⇒ C.
Proof.
  apply relToGraph_typing. apply funRelComp_typing.
  - exact (graphToRel_typing Hf).
  - exact (graphToRel_typing Hg).
Qed.

Lemma setCompArr_app {A B C f g a : ZFSet} (Hf : f ∈ A ⇒ B) (Hg : g ∈ B ⇒ C) (Ha : a ∈ A) :
  setAppArr A C (setCompArr A B C f g) a ≡ setAppArr B C g (setAppArr A B f a).
Proof.
  unfold setAppArr. unfold setCompArr.
  refine (trans (relToGraphToRel_app (funRelComp_typing (graphToRel_typing Hf) (graphToRel_typing Hg)) Ha) _).
  exact (funRelComp_eval (graphToRel_typing Hf) (graphToRel_typing Hg) Ha).
Qed.

Lemma setCompId_left {A B f : ZFSet} (Hf : f ∈ A ⇒ B) : setCompArr A A B (setIdArr A) f ≡ f.
Proof.
  apply (setArr_funext (setCompArr_typing (setIdArr_typing A) Hf) Hf).
  intros a Ha. refine (trans (setCompArr_app (setIdArr_typing A) Hf Ha) _).
  apply (transpS (fun x => setAppArr A B f x ≡ setAppArr A B f a) (sym (setIdArr_app Ha))).
  reflexivity.
Qed.

Lemma setCompId_right {A B f : ZFSet} (Hf : f ∈ A ⇒ B) : setCompArr A B B f (setIdArr B) ≡ f.
Proof.
  apply (setArr_funext (setCompArr_typing Hf (setIdArr_typing B)) Hf).
  intros a Ha. refine (trans (setCompArr_app Hf (setIdArr_typing B) Ha) _).
  exact (setIdArr_app (setAppArr_typing Hf Ha)).
Qed.

Lemma setCompAssoc {A B C D f g h : ZFSet} (Hf : f ∈ A ⇒ B) (Hg : g ∈ B ⇒ C) (Hh : h ∈ C ⇒ D) :
  setCompArr A B D f (setCompArr B C D g h) ≡ setCompArr A C D (setCompArr A B C f g) h.
Proof.
  apply (setArr_funext (setCompArr_typing Hf (setCompArr_typing Hg Hh)) (setCompArr_typing (setCompArr_typing Hf Hg) Hh)).
  intros a Ha. refine (trans (setCompArr_app Hf (setCompArr_typing Hg Hh) Ha) _).
  refine (trans (setCompArr_app Hg Hh (setAppArr_typing Hf Ha)) _).
  refine (trans _ (sym (setCompArr_app (setCompArr_typing Hf Hg) Hh Ha))).
  apply (transpS (fun x => _ ≡ setAppArr C D h x) (sym (setCompArr_app Hf Hg Ha))).
  reflexivity.
Qed.

(* Dependent products *)

Definition setPi (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) : ZFSet :=
  { f ϵ A ⇒ 𝕍 n ∣ ∀ a ∈ A, setAppArr A (𝕍 n) f a ∈ B a }.

Definition setPi' (n : nat) (A : ZFSet) (B : ZFSet -> ZFSet) : ZFSet :=
  { R ϵ 𝒫 (setSigma n A B) ∣ isFunRel A (𝕍 n) (graphToRel R) }.

Lemma setPi_in_setPi' (n : nat) {A f : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  f ∈ setPi n A B -> f ∈ setPi' n A B.
Proof.
  intro Hf. apply ZFincomp in Hf. destruct Hf as [ Hf Hf3 ].
  pose proof Hf as Hf0. apply ZFincomp in Hf. destruct Hf as [ Hf1 Hf2 ]. apply ZFinpower in Hf1.
  apply ZFincomp. split.
  - apply ZFinpower. intros p Hp. pose proof (Hf1 _ Hp) as Hp2. pose proof (setPairη Hp2) as Hp3.
    refine (transpS (fun X => X ∈ setSigma n A B) (sym Hp3) _).
    apply setMkSigma_typing. exact HB. now apply setFstPair_typing.
    specialize (Hf3 (setFstPair A (𝕍 n) p) (setFstPair_typing Hp2)).
    refine (transpS (fun X => X ∈ B (setFstPair A (𝕍 n) p)) (sym _) Hf3).
    apply (inSetArr_l Hf0). exact Hp.
  - exact Hf2.
Qed.

Lemma setPi'_in_setPi (n : nat) {A f : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  f ∈ setPi' n A B -> f ∈ setPi n A B.
Proof.
  intro Hf. apply ZFincomp in Hf. destruct Hf as [ Hf1 Hf2 ]. apply ZFinpower in Hf1.
  assert (f ∈ A ⇒ 𝕍 n) as Hf3.
  { apply ZFincomp. split. apply ZFinpower. eapply subset_trans. exact Hf1.
    now apply setSigma_pretyping. exact Hf2. }
  apply ZFincomp. split. exact Hf3.
  intros a Ha. assert (⟨ a ; setAppArr A (𝕍 n) f a ⟩ ∈ f) as Hp.
  { apply (@inSetArr_r A (𝕍 n) f).
    - exact Hf3.
    - apply setMkPair_typing. exact Ha. now apply setAppArr_typing.
    - refine (transp2S (fun X Y => X ≡ setAppArr A (𝕍 n) f Y) _ _ (eqS_refl _)).
      + apply sym. apply setPairβ2. exact Ha. now apply setAppArr_typing.
      + apply sym. apply setPairβ1. exact Ha. now apply setAppArr_typing. }
  apply Hf1 in Hp. apply (setMkSigma_detyping HB) in Hp. now destruct Hp as [ _ Hp ].
Qed.

Lemma setPi_coincide (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet} (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) :
  setPi n A B ≡ setPi' n A B.
Proof.
  apply ZFext.
  - intros f Hf. now apply setPi_in_setPi'.
  - intros f Hf. now apply setPi'_in_setPi.
Qed.

Lemma setPi'_typing (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet}
  (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) : setPi' n A B ∈ 𝕍 n.
Proof.
  unfold setPi'. apply setComp_sorting. apply ZFuniv_power.
  now apply setSigma_typing.
Qed.

Lemma setPi_typing (n : nat) {A : ZFSet} {B : ZFSet -> ZFSet}
  (HA : A ∈ 𝕍 n) (HB : ∀ a ∈ A, B a ∈ 𝕍 n) : setPi n A B ∈ 𝕍 n.
Proof.
  refine (transpS (fun X => X ∈ 𝕍 n) (sym (setPi_coincide n HA HB)) _).
  apply (setPi'_typing n HA HB).
Qed.

(* Natural numbers *)

Definition ZFzero  := ∅.             (* nat *)
Definition ZFone   := ZFsuc ZFzero.  (* pi *)
Definition ZFtwo   := ZFsuc ZFone.   (* sigma *)
Definition ZFthree := ZFsuc ZFtwo.   (* type *)
Definition ZFfour  := ZFsuc ZFthree. (* prop *)
Definition ZFfive  := ZFsuc ZFfour.  (* box *)

Lemma zero_typing : ZFzero ∈ ω.
Proof.
  now apply ZFininfinity. 
Qed.

Lemma suc_typing {n : ZFSet} (Hn : n ∈ ω) : ZFsuc n ∈ ω.
Proof.
  apply ZFininfinity. intros P Pz Ps.
  apply Ps. now eapply ZFininfinity.
Qed.

Lemma one_typing : ZFone ∈ ω.
Proof.
  apply suc_typing. apply zero_typing.
Qed.

Lemma two_typing : ZFtwo ∈ ω.
Proof.
  apply suc_typing. apply one_typing.
Qed.

Lemma three_typing : ZFthree ∈ ω.
Proof.
  apply suc_typing. apply two_typing.
Qed.

Lemma four_typing : ZFfour ∈ ω.
Proof.
  apply suc_typing. apply three_typing.
Qed.

Lemma five_typing : ZFfive ∈ ω.
Proof.
  apply suc_typing. apply four_typing.
Qed.

Lemma zero_ne_suc (x : ZFSet) : ∅ ≡ ZFsuc x -> FalseS.
Proof.
  intro H. eapply ZFinempty.
  refine (transpS (fun X => x ∈ X) (sym H) _).
  apply ZFinpairing. left. reflexivity.
Qed.

Lemma nat_ind {x : ZFSet} (Hx : x ∈ ω) (P : ZFSet -> SProp) (pz : P ∅) (ps : ∀ x ∈ ω, P x -> P (ZFsuc x)) : P x.
Proof.
  apply (fstS (ZFininfinity x) Hx (fun n => n ∈ ω ∧ P n)).
  - split. apply zero_typing. exact pz.
  - intros n [ Hn IH ]. split. now apply suc_typing. now apply ps.
Qed.

Lemma suc_inj {x y : ZFSet} (Hx : x ∈ ω) (Hy : y ∈ ω) : ZFsuc x ≡ ZFsuc y -> x ≡ y.
Proof.
  revert y Hy. apply (fstS (ZFininfinity x) Hx (fun a => ∀ y ∈ ω, ZFsuc a ≡ ZFsuc y -> a ≡ y)).
  - intros y Hy H. assert (y ∈ {∅; setSingl ∅}) as H0.
    { refine (transpS (fun X => y ∈ X) (sym H) _). apply ZFinpairing. now left. }
    apply ZFinpairing in H0. destruct H0 as [ H0 | H0 ].
    + exact (sym H0).
    + apply (transpS (fun X => ZFsuc ∅ ≡ ZFsuc X) H0) in H. assert (∅ ∈ ZFsuc (setSingl ∅)).
      { refine (transpS (fun X => ∅ ∈ X) H _). apply ZFinpairing. now left. }
      apply ZFinpairing in H1. destruct H1 as [ H1 | H1 ].
      * assert (∅ ∈ ∅). { refine (transpS (fun X => ∅ ∈ X) (sym H1) _). apply ZFinpairing. now left. }
        apply ZFinempty in H2. destruct H2.
      * assert (setSingl ∅ ∈ ∅). { refine (transpS (fun X => setSingl ∅ ∈ X) (sym H1) _). apply ZFinpairing. now left. }
        apply ZFinempty in H2. destruct H2.
  - clear x Hx. intros x IH y Hy H. assert (ZFsuc x ∈ ZFsuc y) as H0.
    { refine (transpS (fun X => ZFsuc x ∈ X) H _). apply ZFinpairing. now left. }
    apply ZFinpairing in H0. destruct H0 as [ H0 | H0 ].
    + exact H0.
    + assert (x ≡ y).
      { apply inSetSingl. refine (transpS (fun X => x ∈ X) H0 _). apply ZFinpairing. now left. }
      destruct H1. assert (setSingl x ≡ x).
      { apply inSetSingl. refine (transpS (fun X => setSingl x ∈ X) H0 _). apply ZFinpairing. now right. }
      exact (trans H0 H1).      (* there's probably a shorter proof... *)
Qed.

(* Definition of the recursor *)

Definition natrel (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) :=
  { x ϵ setSigma n ω P ∣
      ∀ X ∈ 𝒫 (setSigma n ω P), ⟨ ∅ ; pz ⟩ ∈ X
      -> (∀ y ∈ X, ⟨ ZFsuc (setFstSigma n ω P y) ; ps (setSndSigma n ω P y) ⟩ ∈ X)
      -> x ∈ X }.

Lemma zero_in_natrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) : ⟨ ∅ ; pz ⟩ ∈ natrel n P pz ps. 
Proof.
  apply ZFincomp. split.
  - apply setMkSigma_typing. exact HP. apply zero_typing. exact Hpz.
  - intros X HX Hz Hs. exact Hz.
Qed.

Lemma suc_in_natrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {x : ZFSet} (Hx : x ∈ natrel n P pz ps) :
  ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setSndSigma n ω P x) ⟩ ∈ natrel n P pz ps. 
Proof.
  apply ZFincomp. split.
  - apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply setMkSigma_typing.
    + exact HP.
    + apply suc_typing. apply setFstSigma_typing. exact HP. exact Hx1.
    + apply Hps.
      * apply setFstSigma_typing. exact HP. exact Hx1.
      * apply setSndSigma_typing. exact HP. exact Hx1.
  - intros X HS Hz Hs. apply Hs. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. now apply Hx2.
Qed.

Lemma suc_in_natrel' {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m pm : ZFSet} (Hm : m ∈ ω) (Hpm : pm ∈ P m) (H : ⟨ m ; pm ⟩ ∈ natrel n P pz ps) :
  ⟨ ZFsuc m ; ps pm ⟩ ∈ natrel n P pz ps. 
Proof.
  refine (transpS (fun X => X ∈ _) _ (suc_in_natrel (x := ⟨ m ; pm ⟩) HP Hpz Hps _)).
  - refine (fequal2 (fun x y => ⟨ ZFsuc x ; ps y ⟩) _ _).
    + apply setSigmaβ1. exact HP. assumption. assumption.
    + apply setSigmaβ2. exact HP. assumption. assumption.
  - exact H.
Qed.

Definition natrelU_zero (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) :=
  { x ϵ natrel n P pz ps ∣ setFstSigma n ω P x ≡ ∅ -> setSndSigma n ω P x ≡ pz }.

Lemma zero_in_natrelU_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) 
  : ⟨ ∅ ; pz ⟩ ∈ natrelU_zero n P pz ps.
Proof.
  apply ZFincomp. split.
  - now apply zero_in_natrel.
  - intros _. apply setSigmaβ2 ; try assumption. apply zero_typing.
Qed.

Lemma suc_in_natrelU_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {x : ZFSet} (Hx : x ∈ natrelU_zero n P pz ps) :
  ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setSndSigma n ω P x) ⟩ ∈ natrelU_zero n P pz ps. 
Proof.
  apply ZFincomp. split.
  - apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. now apply suc_in_natrel.
  - assert (x ∈ setSigma n ω P) as Hx2.
    { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. exact Hx. }
    intro H. assert (ZFsuc (setFstSigma n ω P x) ≡ ∅).
    { refine (trans (sym _) H). apply setSigmaβ1. apply HP.
      - apply suc_typing. apply setFstSigma_typing. exact HP. exact Hx2.
      - apply Hps.
        + apply setFstSigma_typing. exact HP. exact Hx2.
        + apply setSndSigma_typing. exact HP. exact Hx2. }
    pose proof (zero_ne_suc _ (sym H0)) as Habs. destruct Habs.
Qed.

Lemma natrel_incl_natrelU_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  natrel n P pz ps ⊂ natrelU_zero n P pz ps.
Proof.
  intros x Hx. pose proof Hx as Hx2. apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. apply Hx3.
  - clear x Hx Hx2 Hx3. apply ZFinpower. intros x Hx. apply ZFincomp in Hx.
    destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ].
  - apply (zero_in_natrelU_zero HP Hpz).
  - intros x' Hx'. apply (suc_in_natrelU_zero HP Hpz Hps Hx').
Qed.

Lemma natrel_funrel_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  ∃! x ∈ P ∅, ⟨ ∅ ; x ⟩ ∈ natrel n P pz ps.
Proof.
  exists pz. split.
  - split. exact Hpz. now apply zero_in_natrel.
  - intros x Hx. destruct Hx as [ Hx1 Hx2 ]. apply natrel_incl_natrelU_zero in Hx2 ; try assumption.
    apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. refine (trans (sym (Hx3 _)) _).
    + apply setSigmaβ1. exact HP. apply zero_typing. assumption.
    + apply setSigmaβ2. exact HP. apply zero_typing. assumption.
Qed.

Definition natrelU_suc (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) (m pm : ZFSet) :=
  { x ϵ natrel n P pz ps ∣ setFstSigma n ω P x ≡ m -> setSndSigma n ω P x ≡ pm }.

Lemma zero_in_natrelU_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {m pm : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) 
  : ⟨ ∅ ; pz ⟩ ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm).
Proof.
  apply ZFincomp. split.
  - now apply zero_in_natrel.
  - intro H. assert (∅ ≡ ZFsuc m) as Habs.
    { refine (trans (sym _) H). apply setSigmaβ1 ; try assumption. apply zero_typing. }
    apply zero_ne_suc in Habs. destruct Habs.
Qed.

Lemma suc_in_natrelU_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {m pm : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hm : m ∈ ω)
  (Hpm : pm ∈ P m) (IH1 : ⟨ m ; pm ⟩ ∈ natrel n P pz ps) (IH2 : ∀ pm' ∈ P m, ⟨ m ; pm' ⟩ ∈ natrel n P pz ps -> pm ≡ pm')
  {x : ZFSet} (Hx : x ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm)) :
  ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setSndSigma n ω P x) ⟩ ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm).
Proof.
  apply ZFincomp. split.
  - apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. now apply suc_in_natrel.
  - intro H. assert (x ∈ setSigma n ω P) as Hx0.
    { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ]. }
    assert (setFstSigma n ω P x ∈ ω) as Hx1.
    { now apply setFstSigma_typing. }
    assert (setSndSigma n ω P x ∈ P (setFstSigma n ω P x)) as Hx2.
    { now apply setSndSigma_typing. }
    assert (setFstSigma n ω P x ≡ m) as Hx3.
    { apply suc_inj ; try assumption. refine (trans (sym _) H).
      apply setSigmaβ1 ; try assumption. now apply suc_typing. now apply Hps. }
    clear H. set (pm' := setSndSigma n ω P x). assert (x ≡ ⟨ m ; pm' ⟩) as Hx4.
    { refine (trans _ (fequal (fun X => ⟨ X ; pm' ⟩) Hx3)). now apply setSigmaη. }
    assert (⟨ m ; pm' ⟩ ∈ natrel n P pz ps) as H0.
    { refine (transpS (fun X => X ∈ _) Hx4 _). apply ZFincomp in Hx. now destruct Hx as [ Hx _ ]. }
    apply IH2 in H0.
    2:{ refine (transpS (fun X => pm' ∈ P X) Hx3 _). now apply setSndSigma_typing. }
    refine (trans _ (fequal ps (sym H0))). apply setSigmaβ2 ; try assumption.
    + apply suc_typing. now apply setFstSigma_typing.
    + apply Hps. now apply setFstSigma_typing. now apply setSndSigma_typing.
Qed.

Lemma natrel_incl_natrelU_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {m pm : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hm : m ∈ ω)
  (Hpm : pm ∈ P m) (IH1 : ⟨ m ; pm ⟩ ∈ natrel n P pz ps) (IH2 : ∀ pm' ∈ P m, ⟨ m ; pm' ⟩ ∈ natrel n P pz ps -> pm ≡ pm') :
  natrel n P pz ps ⊂ natrelU_suc n P pz ps (ZFsuc m) (ps pm).
Proof.
  intros x Hx. pose proof Hx as Hx2. apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. apply Hx3.
  - clear x Hx Hx2 Hx3. apply ZFinpower. intros x Hx. apply ZFincomp in Hx.
    destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ].
  - apply (zero_in_natrelU_suc HP Hpz).
  - intros x' Hx'. now apply (suc_in_natrelU_suc HP Hpz Hps).
Qed.

Lemma natrel_funrel_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m : ZFSet} (Hm : m ∈ ω) (IH : ∃! x ∈ P m, ⟨ m ; x ⟩ ∈ natrel n P pz ps) :
  ∃! x ∈ P (ZFsuc m), ⟨ ZFsuc m ; x ⟩ ∈ natrel n P pz ps.
Proof.
  destruct IH as [ pm [ [ Hpm Hpm1 ] Hpm2 ] ]. exists (ps pm). split.
  - split. now apply Hps. now apply suc_in_natrel'.
  - intros y [ Hy1 Hy2 ]. assert (⟨ ZFsuc m; y ⟩ ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm)) as Hy3.
    { apply (natrel_incl_natrelU_suc HP Hpz Hps) ; try assumption. intros pm' Hpm' H. now apply Hpm2. }
    apply ZFincomp in Hy3. destruct Hy3 as [ Hy3 Hy4 ]. refine (trans (sym (Hy4 _)) _).
    + apply setSigmaβ1. exact HP. apply suc_typing. assumption. assumption.
    + apply setSigmaβ2. exact HP. apply suc_typing. assumption. assumption.
Qed.

Lemma natrel_funrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  ∀ m ∈ ω, ∃! x ∈ P m, ⟨ m ; x ⟩ ∈ natrel n P pz ps.
Proof.
  intros m0 Hm0. cbn. apply (nat_ind Hm0). 
  - now apply natrel_funrel_zero.
  - intros m Hm IH. now apply natrel_funrel_suc.
Qed.

Lemma natrel_funrel' {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  isFunRel ω (setFamUnion n ω P) (graphToRel (natrel n P pz ps)).
Proof.
  intros m Hm. pose proof (natrel_funrel HP Hpz Hps m Hm) as H. cbn in H.
  destruct H as [ pm [ [ Hpm H1 ] H2 ] ]. exists pm. split.
  - split.
    + exact (inSetFamUnion HP Hm Hpm).
    + exact H1.
  - intros y [ Hy1 Hy2 ]. apply H2. unfold graphToRel in Hy2. split.
    + apply ZFincomp in Hy2. destruct Hy2 as [ Hy2 _ ]. apply setMkSigma_detyping in Hy2.
      now destruct Hy2. exact HP.
    + exact Hy2.
Qed.

Lemma natrel_funrel'' {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m x y : ZFSet} (Hm : m ∈ ω) : ⟨ m ; x ⟩ ∈ natrel n P pz ps -> ⟨ m ; y ⟩ ∈ natrel n P pz ps -> x ≡ y.
Proof.
  intros Hx Hy. pose proof (natrel_funrel HP Hpz Hps m Hm) as H. destruct H as [ z [ [ Hz H1 ] H2 ] ].
  assert (x ∈ P m).
  { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply setMkSigma_detyping in Hx. now destruct Hx. exact HP. }
  assert (y ∈ P m).
  { apply ZFincomp in Hy. destruct Hy as [ Hy _ ]. apply setMkSigma_detyping in Hy. now destruct Hy. exact HP. }
  refine (trans (b := z) _ _).
  - refine (sym _). apply H2. now split.
  - apply H2. now split.
Qed.

Definition natrec (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) (x : ZFSet) : ZFSet :=
  funRelApp ω (setFamUnion n ω P) (graphToRel (natrel n P pz ps)) x.

Lemma natrec_inrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {x : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hx : x ∈ ω) :
  ⟨ x ; natrec n P pz ps x ⟩ ∈ natrel n P pz ps.
Proof.
  change (graphToRel (natrel n P pz ps) x (natrec n P pz ps x)).
  apply funRelApp_inRel. now apply natrel_funrel'. assumption.
Qed.

Lemma natrec_typing {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {x : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hx : x ∈ ω) :
  natrec n P pz ps x ∈ P x.
Proof.
  pose proof (natrec_inrel HP Hpz Hps Hx).
  unfold graphToRel in H. apply ZFincomp in H. destruct H as [ H _ ].
  apply setMkSigma_detyping in H. now destruct H. exact HP.
Qed.

Lemma natrec_β1 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  natrec n P pz ps ∅ ≡ pz.
Proof.
  pose proof (natrec_inrel HP Hpz Hps zero_typing) as H.
  assert (⟨ ∅ ; pz ⟩ ∈ natrel n P pz ps) as H0. { now apply zero_in_natrel. }
  unshelve eapply (natrel_funrel'' HP Hpz Hps _ H H0). now apply zero_typing.
Qed.

Lemma natrec_β2 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m : ZFSet} (Hm : m ∈ ω) :
  natrec n P pz ps (ZFsuc m) ≡ ps (natrec n P pz ps m).
Proof.
  pose proof (natrec_inrel HP Hpz Hps (suc_typing Hm)) as H.
  assert (⟨ ZFsuc m ; ps (natrec n P pz ps m) ⟩ ∈ natrel n P pz ps) as H0.
  { apply suc_in_natrel' ; try assumption. now apply natrec_typing. now apply natrec_inrel. }
  unshelve eapply (natrel_funrel'' HP Hpz Hps _ H H0). now apply suc_typing.
Qed.

(* Variation on natrec where the successor case has an extra argument *)

Definition natrec2_pred (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet -> ZFSet) (m : ZFSet) : ZFSet :=
  { x ϵ setSigma n ω P ∣ setFstSigma n ω P x ≡ m }.

Definition natrec2_aux (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet -> ZFSet) (m : ZFSet) : ZFSet :=
  natrec n (natrec2_pred n P pz ps) ⟨ ∅ ; pz ⟩
           (fun x => ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setFstSigma n ω P x) (setSndSigma n ω P x) ⟩) m.

Definition natrec2 (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet -> ZFSet) (m : ZFSet) : ZFSet :=
  setSndSigma n ω P (natrec2_aux n P pz ps m).

Lemma natrec2_typing_aux1 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  ∀ m ∈ ω, natrec2_pred n P pz ps m ∈ 𝕍 n.
Proof.
  intros x Hx. apply setComp_sorting. apply setSigma_typing. 2:assumption. now apply ZFuniv_uncountable.
Qed.

Lemma natrec2_typing_aux2 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  ⟨ ∅; pz ⟩ ∈ natrec2_pred n P pz ps ∅.
Proof.
  apply ZFincomp. split.
  - apply setMkSigma_typing ; try assumption. now apply zero_typing.
  - apply setSigmaβ1 ; try assumption. now apply zero_typing.
Qed.

Lemma natrec2_typing_aux3 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  ∀ m ∈ ω, ∀ x ∈ natrec2_pred n P pz ps m,
    ⟨ ZFsuc (setFstSigma n ω P x); ps (setFstSigma n ω P x) (setSndSigma n ω P x) ⟩ ∈ natrec2_pred n P pz ps (ZFsuc m).
Proof.
  intros m Hm x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ].
  unshelve epose proof (Hps (setFstSigma n ω P x) _ (setSndSigma n ω P x) _).
  now apply setFstSigma_typing. now apply setSndSigma_typing. cbn in H. apply ZFincomp. split.
  - apply setMkSigma_typing ; try assumption. apply suc_typing. now apply setFstSigma_typing.
  - refine (trans (setSigmaβ1 HP _ H) (fequal ZFsuc Hx2)). apply suc_typing. now apply setFstSigma_typing.
Qed.

Lemma natrec2_aux_typing {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} {m : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) (Hm : m ∈ ω) :
  natrec2_aux n P pz ps m ∈ natrec2_pred n P pz ps m.
Proof.
  apply (natrec_typing (P := natrec2_pred n P pz ps)) ; try assumption.
  - apply (natrec2_typing_aux1 HP Hpz Hps).
  - apply (natrec2_typing_aux2 HP Hpz Hps).
  - apply (natrec2_typing_aux3 HP Hpz Hps).
Qed.

Lemma natrec2_typing {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} {m : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) (Hm : m ∈ ω) :
  natrec2 n P pz ps m ∈ P m.
Proof.
  pose proof (natrec2_aux_typing HP Hpz Hps Hm) as H. apply ZFincomp in H. destruct H as [ H1 H2 ].
  unfold natrec2. refine (transpS (fun X => setSndSigma n ω P (natrec2_aux n P pz ps m) ∈ P X) H2 _).
  now apply setSndSigma_typing.
Qed.

Lemma natrec2_β1 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  natrec2 n P pz ps ∅ ≡ pz.
Proof.
  refine (trans (fequal (setSndSigma n ω P) _) _).
  - apply (natrec_β1 (natrec2_typing_aux1 HP Hpz Hps) (natrec2_typing_aux2 HP Hpz Hps) (natrec2_typing_aux3 HP Hpz Hps)).
  - apply setSigmaβ2 ; try assumption. now apply zero_typing.
Qed.

Lemma natrec2_β2 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} {m : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) (Hm : m ∈ ω) :
  natrec2 n P pz ps (ZFsuc m) ≡ ps m (natrec2 n P pz ps m).
Proof.
  refine (trans (fequal (setSndSigma n ω P) _) _).
  { apply (natrec_β2 (natrec2_typing_aux1 HP Hpz Hps) (natrec2_typing_aux2 HP Hpz Hps) (natrec2_typing_aux3 HP Hpz Hps) Hm). }
  change (setSndSigma n ω P ⟨ ZFsuc (setFstSigma n ω P (natrec2_aux n P pz ps m)) ;
                              ps (setFstSigma n ω P (natrec2_aux n P pz ps m)) (natrec2 n P pz ps m) ⟩
            ≡ ps m (natrec2 n P pz ps m)).
  assert (setFstSigma n ω P (natrec2_aux n P pz ps m) ≡ m) as H.
  { pose proof (natrec2_aux_typing HP Hpz Hps Hm). apply ZFincomp in H. now destruct H. }
  refine (trans (fequal (fun X => setSndSigma n ω P ⟨ ZFsuc X ; ps X (natrec2 n P pz ps m) ⟩) H) _).
  apply setSigmaβ2 ; try assumption.
  - now apply suc_typing.
  - apply Hps. assumption. now apply natrec2_typing.
Qed.

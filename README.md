# Formalization for the paper "Bla"

This repository contains the formalization of most proofs given in the paper "Bla".

## How to install

autosubst, blabla

## Overview

### Preliminary files

autosubst files?

- [BasicAST.v](theories/BasicAST.v): Definition of universe levels and of its basic operations

- [Util.v](theories/Util.v): @Theo, I copied this file from one of your projects, what does it contain?

- [Typing.v](theories/Typing.v): Typing rules of $\mathcal{T}_=$ and $\mathcal{T}_\equiv$. We use a single mutual inductive family parametrized by a mode `M`, which can be either `mdef` for the definitional theory ($\mathcal{T}_\equiv$), or `mprop` for the propositional theory ($\mathcal{T}_=$). The rule for `accelcomp` then requires a proof that `M = mdef`.

- [BasicMetaTheory.v](theories/BasicMetaTheory.v): Basic metatheoretic properties of the two systems, including stability under weakening and substitution, validity, type inversion and some more economical versions of the typing and conversion rules.

- [AccConstructions.v](theories/AccConstructions.v): Working internally to $\mathcal{T}_\equiv$ or $\mathcal{T}_=$, we show that the usual elimination principle for accessibility can be derived from the weaker one we have in the definition of the theories.

### Canonicity of $\mathcal{T}_\equiv$

- [Reduction.v](theories/Reduction.v): Definition of a typed and deterministic weak-head reduction relation for $\mathcal{T}_\equiv$, needed for defining the logical relation. We also prove some of its basic properties.


- [LRDef.v](theories/LRDef.v): Definition of the logical relation for proving canonicity of $\mathcal{T}_\equiv$. We use a module to hide the definition of the logical relation, which has some technical aspects.

- [LRBasicProps.v](theories/LRBasicProps.v): Basic properties of the logical relation, including escape, closure under reduction and anti-reduction, stability under annotation exchange, inversion, irrelevance, symmetry and transitivity. We also extend the logical relation to substitutions, define validity, and prove that they both also satisfy symmetry and transitivity.

- [FundamentalAux.v](theories/FundamentalAux.v): Auxiliary lemmas for proving the fundamental theorem of the logical relation.

- [FundamentalPi.v](theories/FundamentalPi.v), [FundamentalNat.v](theories/FundamentalNat.v), [FundamentalAcc.v](theories/FundamentalAcc.v), [FundamentalCast.v](theories/FundamentalCast.v): Cases of proof of fundamental theorem for function types, natural numbers, accessibility and observational equality.

- [Fundamental.v](theories/Fundamental.v): Proof of the fundamental theorem of the logical relation. As a corollary, we derive canonicity for $\mathcal{T}_\equiv$.

- [CompCanonicity.v](theories/CompCanonicity.v): Proof of computational canonicity for $\mathcal{T}_\equiv$, in which the natural number is computed through untyped reduction on the erasure of the term.


### Conservativity of $\mathcal{T}_\equiv$ over $\mathcal{T}_=$


- [HEq.v](theories/HEq.v): Definition of heterogeneous equality in $\mathcal{T}_=$ and proofs of its important properties. To make the proofs practically feasible, here we work internally to the object theory: we postulate sufficiently many primitives to turn Rocq into a proof assistant for $\mathcal{T}_=$.

- [CHEqProps.v](theories/CHEqProps.v): Postulates of the external versions of the terms and proofs constructed internally in the file [HEq.v](theories/HEq.v).

- [CDecoration.v](theories/CDecoration.v): Definition of the decoration relation and proof of the fundamental lemma of the translation, stating that related well-typed terms in $\mathcal{T}_=$ are heterogeneously equal.

- [CTranslation.v](theories/CTranslation.v): Proof of the decorating translation from  $\mathcal{T}_\equiv$ to $\mathcal{T}_=$. As a corollary, we deduce the conservativity $\mathcal{T}_\equiv$ over $\mathcal{T}_=$. Combined with the result of [CompCanonicity.v](theories/CompCanonicity.v), we derive propositional canonicity for $\mathcal{T}_=$.

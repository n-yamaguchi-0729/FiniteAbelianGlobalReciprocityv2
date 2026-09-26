# Global class field theory in Lean 4.35.0-rc2

This repository includes the complete [ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/7713795234690681b4406ae198b07aa95e82716a)
source tree under [`Lean4/`](Lean4/) and presents its finite norm-quotient form
of global class field theory. The bundled sources correspond to upstream commit
[`7713795`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/commit/7713795234690681b4406ae198b07aa95e82716a).

The compared declaration is
`ClassFieldTheory.GlobalClassFieldComparison.finiteAbelianGlobalReciprocity_relativeNormQuotient`.
For a finite abelian extension `L / K` of number fields, it states

```text
C_K / N_{L/K}(C_L) ≃ₜ* Gal(L/K).
```

Here `≃ₜ*` is an isomorphism of topological multiplicative groups. The
Mathlib-only Challenge constructs the relative idèle-class norm as the
determinant norm on `𝔸_K ⊗[K] L`, descended through principal idèles. The
corresponding ordinary idèle-class norm is defined in
[`IdeleNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/IdeleNorm.lean),
and its range is identified with the relative determinant norm's range in
[`NormComparison.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/NormComparison.lean).
The Solution uses this comparison and the ordinary-norm theorem in
[`MathlibGlobalReciprocity.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/MathlibGlobalReciprocity.lean).

## Additional proved results

The same CFT development also proves:

- a surjective finite Artin map, an unramified modulus, and arithmetic
  Frobenius normalization in
  [`FiniteAbelianGlobalReciprocity.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean);
- the norm-kernel theorem in
  [`FinitePlaceRayArtinNormKernel.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FinitePlaceRayArtinNormKernel.lean);
- local values and decomposition-group compatibility in
  [`FinitePlaceRayArtinLocalValue.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FinitePlaceRayArtinLocalValue.lean)
  and
  [`FinitePlaceRayArtinDecomposition.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/7713795234690681b4406ae198b07aa95e82716a/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FinitePlaceRayArtinDecomposition.lean).

The theorem placeholder in `Challenge.lean` is deliberate; `Solution.lean`
contains the completed proof, and the norm has no definition hole.

## Authorship

Astra GPT-6 Codex assisted with Lean development, statement review, and
preparation of this submission interface. Naganori Yamaguchi is the
human author and responsible maintainer.

Licensed under Apache-2.0.

## Pinned Mathlib definitions behind the compared statement

The Challenge uses [Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55), as recorded in `lake-manifest.json`. The following are unmodified excerpts of the imported definitions that determine its hypotheses, idèle-class norm, and topological groups. Surrounding implicit parameters are in the linked files. These excerpts add no assumptions or declarations to the Challenge.

**Number fields and finite places.** [`NumberField`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/NumberField/Basic.lean#L45-L48) means a characteristic-zero field finite-dimensional over `ℚ`. The notation `𝓞 K` denotes the [integral closure of `ℤ` in `K`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/NumberField/Basic.lean#L104-L108). [`HeightOneSpectrum R`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L493-L496) consists of nonzero prime ideals; these index the finite places used in the Challenge.

```lean
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]

def RingOfIntegers : Type _ :=
  integralClosure ℤ K
deriving CommRing, IsDomain, Nontrivial

structure HeightOneSpectrum where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  ne_bot : asIdeal ≠ ⊥
```

The local factor [`v.adicCompletion K`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L603-L608) wraps the completion for the `v`-adic valuation, and [`v.adicCompletionIntegers K`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L803-L804) is its valuation subring:

```lean
structure adicCompletion where
  /-- Wrap an element of the underlying completion `(v.valuation K).Completion` into
  `adicCompletion`. -/
  ofCompletion ::
  /-- The underlying element of the completion `(v.valuation K).Completion`. -/
  toCompletion : (v.valuation K).Completion

def adicCompletionIntegers : ValuationSubring (v.adicCompletion K) :=
  Valued.v.valuationSubring
```

**Adèles and the topology on idèle classes.** [`RestrictedProduct`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean#L79) consists of tuples in the specified subsets at almost all places for the chosen filter. Its [topology](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L147-L149) is assembled from the inclusion maps for sets admitted by that filter. [`FiniteAdeleRing`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L94-L101) takes this restricted product over finite places with its topology:

```lean
def RestrictedProduct (𝓕 : Filter ι) : Type _ := {x : Π i, R i // ∀ᶠ i in 𝓕, x i ∈ A i}

instance topologicalSpace : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕]) :=
  ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance)

def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

instance : TopologicalSpace (FiniteAdeleRing R K) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
```

The [infinite adèles](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean#L52-L53) are a product of completions at infinite places. The [adèle ring](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/NumberField/AdeleRing.lean#L50-L51) is the product of its infinite and finite parts; both derive their topologies:

```lean
def InfiniteAdeleRing (K : Type*) [Field K] := (v : InfinitePlace K) → v.Completion
deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing R K
deriving CommRing, TopologicalSpace, IsTopologicalRing, Algebra K
```

The Challenge's infinite idèles and each finite local factor are units, whose topology comes from their [embedding into the corresponding ring and its inverses](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Constructions.lean#L101-L102). Finite idèles have the restricted-product topology on those local unit groups, and the full idèle group has the product topology. The idèle class group and the final norm quotient use the [quotient-group topology](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Group/Quotient.lean#L32-L33), with its [underlying coinduced topology](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean#L58-L60). The `equivAdeleRingUnits` used to define the norm is an algebraic equivalence; it does not define the idèle topology:

```lean
instance instTopologicalSpaceUnits : TopologicalSpace Mˣ :=
  TopologicalSpace.induced (embedProduct M) inferInstance

instance instTopologicalSpace (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  instTopologicalSpaceQuotient

instance instTopologicalSpaceQuotient {s : Setoid X} [t : TopologicalSpace X] :
    TopologicalSpace (Quotient s) :=
  coinduced Quotient.mk' t
```

**Relative norm and Galois side.** The Challenge defines the relative adèle algebra `𝔸_K ⊗[K] L` and its descended class norm explicitly. The imported [`Algebra.norm`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Norm/Defs.lean#L61-L62) is the determinant of multiplication:

```lean
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom
```

[`IsAbelianGalois`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Galois/Abelian.lean#L25-L26) means a Galois extension with commutative Galois group; [`IsGalois`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Galois/Basic.lean#L57-L59) supplies separability and normality, and [`IsMulCommutative`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Semigroup.lean#L174-L175) supplies commutativity. The theorem separately assumes `FiniteDimensional K L`:

```lean
class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, IsMulCommutative Gal(L/K)

class IsGalois : Prop where
  [to_isSeparable : Algebra.IsSeparable F E]
  [to_normal : Normal F E]

class IsMulCommutative (M : Type*) [Mul M] : Prop where
  is_comm : Std.Commutative (α := M) (· * ·)
```

The Galois group has the [Krull topology](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/KrullTopology.lean#L131-L135) induced by fixing subgroups of finite intermediate extensions; it is [discrete for finite-dimensional `L/K`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/KrullTopology.lean#L247-L251). The notation `≃ₜ*` is [`ContinuousMulEquiv`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean#L307-L319), combining a group equivalence and homeomorphism, so both directions are continuous:

```lean
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace Gal(L/K) :=
  GroupFilterBasis.topology (galGroupBasis K L)

structure ContinuousMulEquiv [Mul G] [Mul H] extends G ≃* H, G ≃ₜ H
```

Mathlib is distributed under [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/LICENSE), the same license provided in this repository. No excerpt above is modified. The original source-file copyright notices are retained here:

| Excerpt source in `Mathlib/` | Original copyright notice |
| --- | --- |
| `NumberTheory/NumberField/Basic.lean` | Copyright (c) 2021 Ashvni Narayanan. All rights reserved. |
| `RingTheory/DedekindDomain/Ideal/Lemmas.lean` | Copyright (c) 2020 Kenji Nakagawa. All rights reserved. |
| `RingTheory/DedekindDomain/AdicValuation.lean` | Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved. |
| `Topology/Algebra/RestrictedProduct/Basic.lean`, `Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` | Copyright (c) 2025 Anatole Dedecker. All rights reserved. |
| `RingTheory/DedekindDomain/FiniteAdeleRing.lean` | Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved. |
| `NumberTheory/NumberField/InfiniteAdeleRing.lean`, `NumberTheory/NumberField/AdeleRing.lean` | Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved. |
| `Topology/Algebra/Constructions.lean` | Copyright (c) 2021 Nicolò Cavalleri. All rights reserved. |
| `Topology/Algebra/Group/Quotient.lean`, `Topology/Constructions.lean` | Copyright (c) 2017 Johannes Hölzl. All rights reserved. |
| `RingTheory/Norm/Defs.lean` | Copyright (c) 2021 Anne Baanen. All rights reserved. |
| `FieldTheory/Galois/Abelian.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. |
| `FieldTheory/Galois/Basic.lean` | Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved. |
| `Algebra/Group/Semigroup.lean` | Copyright (c) 2014 Jeremy Avigad. All rights reserved. |
| `FieldTheory/KrullTopology.lean` | Copyright (c) 2022 Sebastian Monnet. All rights reserved. |
| `Topology/Algebra/ContinuousMonoidHom.lean` | Copyright (c) 2022 Thomas Browning. All rights reserved. |

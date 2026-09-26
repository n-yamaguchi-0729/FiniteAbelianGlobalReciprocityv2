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

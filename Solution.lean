import Definitions
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity

set_option autoImplicit false

/-!
The Challenge fixes the determinant norm itself. The proof below uses the
pinned CFT theorem for the ordinary idèle-class norm and the proved equality
between its range and the range of the relative determinant norm.
-/

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

/-- Finite abelian global reciprocity in determinant norm-quotient form. -/
theorem finiteAbelianGlobalReciprocity_relativeNormQuotient
    (K L : Type)
    [fieldK : Field K] [numberFieldK : NumberField K]
    [fieldL : Field L] [numberFieldL : NumberField L]
    [algebraKL : Algebra K L]
    [finiteDimensionalKL : FiniteDimensional K L]
    [abelianGaloisKL : IsAbelianGalois K L] :
    FiniteAbelianGlobalReciprocity.Statement K L := by
  change
    Nonempty
      ((IdeleClassGroup K ⧸ (RelativeIdeleGroup.classNorm K L).range) ≃ₜ*
        (L ≃ₐ[K] L))
  rw [← ordinaryIdeleClassNorm_range_eq_relative (K := K) (L := L)]
  exact finiteAbelianGlobalReciprocity K L

end ClassFieldTheory.GlobalClassFieldComparison

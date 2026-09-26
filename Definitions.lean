import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Maps

set_option autoImplicit false

/-!
# Definitions for finite abelian global reciprocity

This block gives a Mathlib-only presentation of the idèle class group and of
the determinant norm on the relative adèle algebra. The same declarations are
used by the solution so that Comparator also checks the complete definition
closure of the selected theorem.
-/

open scoped NumberField RestrictedProduct TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace FiniteAbelianGlobalReciprocity

variable (K : Type*) [fieldK : Field K] [numberFieldK : NumberField K]

/-- The finite idèle group over a Dedekind domain and its fraction field. -/
abbrev FiniteIdeleGroupOf
    (R : Type*) [commRingR : CommRing R]
    [isDedekindDomainR : IsDedekindDomain R]
    (F : Type*) [fieldF : Field F] [algebraRF : Algebra R F]
    [isFractionRingRF : IsFractionRing R F] :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]

/-- The finite idèle group of a number field. -/
abbrev FiniteIdeleGroup := FiniteIdeleGroupOf (𝓞 K) K

/-- The product of the multiplicative groups at the infinite places. -/
abbrev InfiniteIdeleGroup := (NumberField.InfiniteAdeleRing K)ˣ

/-- The idèle group `I_K`. -/
abbrev IdeleGroup := InfiniteIdeleGroup K × FiniteIdeleGroup K

namespace IdeleGroup

variable {K}

/-- Algebraically, finite idèles are the units of the finite adèle ring. -/
def finiteEquivFiniteAdeleUnitsOf
    (R : Type*) [commRingR : CommRing R]
    [isDedekindDomainR : IsDedekindDomain R]
    (F : Type*) [fieldF : Field F] [algebraRF : Algebra R F]
    [isFractionRingRF : IsFractionRing R F] :
    FiniteIdeleGroupOf R F ≃*
      (IsDedekindDomain.FiniteAdeleRing R F)ˣ :=
  (RestrictedProduct.unitsEquiv
    (ι := HeightOneSpectrum R)
    (S := fun v : HeightOneSpectrum R ↦ ValuationSubring (v.adicCompletion F))
    (B := fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers F)
    (𝓕 := Filter.cofinite)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion F)).symm

/-- Algebraically, finite idèles are the units of the finite adèle ring. -/
def finiteEquivFiniteAdeleUnits :
    FiniteIdeleGroup K ≃*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteEquivFiniteAdeleUnitsOf (𝓞 K) K

/-- Algebraically, the idèle group is the unit group of the adèle ring. -/
def equivAdeleRingUnits :
    IdeleGroup K ≃* (NumberField.AdeleRing (𝓞 K) K)ˣ :=
  ((MulEquiv.refl (InfiniteIdeleGroup K)).prodCongr
      (finiteEquivFiniteAdeleUnits (K := K))).trans
    MulEquiv.prodUnits.symm

variable (K)

/-- The diagonal embedding of `Kˣ` into the idèle group. -/
def principalIdele : Kˣ →* IdeleGroup K :=
  (equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)))

/-- The subgroup of principal idèles. -/
def principalSubgroup : Subgroup (IdeleGroup K) :=
  (principalIdele K).range

end IdeleGroup

/-- The idèle class group `C_K = I_K / Kˣ`. -/
abbrev IdeleClassGroup :=
  IdeleGroup K ⧸ IdeleGroup.principalSubgroup K

variable
    (K L : Type*) [fieldK : Field K] [numberFieldK : NumberField K]
    [fieldL : Field L] [numberFieldL : NumberField L]
    [algebraKL : Algebra K L]
    [finiteDimensionalKL : FiniteDimensional K L]

/-- The adèle algebra of `L` in its canonical relative presentation
`𝔸_K ⊗_K L`. -/
abbrev RelativeAdeleRing :=
  NumberField.AdeleRing (𝓞 K) K ⊗[K] L

/-- The idèle group of the relative adèle algebra. -/
abbrev RelativeIdeleGroup :=
  (RelativeAdeleRing K L)ˣ

namespace RelativeIdeleGroup

instance baseAdeleRingNontrivial :
    Nontrivial (NumberField.AdeleRing (𝓞 K) K) :=
  Function.Injective.nontrivial
    (NumberField.AdeleRing.algebraMap_injective
      (R := 𝓞 K) (K := K))

/-- The extension field embedded diagonally in the relative adèle algebra. -/
def fieldInclusion :
    L →+* RelativeAdeleRing K L :=
  (Algebra.TensorProduct.includeRight
    (R := K) (A := NumberField.AdeleRing (𝓞 K) K)
    (B := L)).toRingHom

/-- The diagonal embedding of `Lˣ` into the relative idèle group. -/
def principalIdele :
    Lˣ →* RelativeIdeleGroup K L :=
  Units.map (fieldInclusion K L)

/-- The relative idèle norm, defined as the determinant over `𝔸_K`. -/
def norm :
    RelativeIdeleGroup K L →* IdeleGroup K :=
  (IdeleGroup.equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map
      (Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)))

omit [NumberField L] in
/-- The determinant norm of a diagonal element is its field norm. -/
theorem norm_fieldInclusion (x : L) :
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L x) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange
    (NumberField.AdeleRing (𝓞 K) K)
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b,
    (algebraMap K
      (NumberField.AdeleRing (𝓞 K) K)).map_det]
  congr 1
  ext i j
  simp [bA, b, fieldInclusion,
    Algebra.smul_def,
    Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField L] in
/-- The relative idèle norm sends principal idèles to principal idèles. -/
@[simp]
theorem norm_principalIdele (x : Lˣ) :
    norm K L (principalIdele K L x) =
      IdeleGroup.principalIdele K
        (Units.map (Algebra.norm K) x) := by
  apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L (x : L)) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K (x : L))
  exact norm_fieldInclusion K L (x : L)

/-- The subgroup of principal relative idèles. -/
def principalSubgroup :
    Subgroup (RelativeIdeleGroup K L) :=
  (principalIdele K L).range

/-- The idèle class group of `L` in the relative presentation
`(𝔸_K ⊗_K L)ˣ / Lˣ`. -/
abbrev ClassGroup :=
  RelativeIdeleGroup K L ⧸ principalSubgroup K L

/-- The determinant norm descended to relative idèle classes. -/
noncomputable def classNorm :
    ClassGroup K L →* IdeleClassGroup K :=
  QuotientGroup.map
    (principalSubgroup K L)
    (IdeleGroup.principalSubgroup K)
    (norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      refine ⟨Units.map (Algebra.norm K) x, ?_⟩
      exact (norm_principalIdele K L x).symm)

end RelativeIdeleGroup

/-- The idèle class group is commutative. -/
theorem ideleClassGroupIsMulCommutative
    (K : Type) [fieldK : Field K] [numberFieldK : NumberField K] :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance 2000] ideleClassGroupIsMulCommutative

/-- The finite abelian global reciprocity statement in determinant
norm-quotient form. -/
def Statement
    (K L : Type)
    [fieldK : Field K] [numberFieldK : NumberField K]
    [fieldL : Field L] [_numberFieldL : NumberField L]
    [algebraKL : Algebra K L]
    [finiteDimensionalKL : FiniteDimensional K L]
    [_abelianGaloisKL : IsAbelianGalois K L] : Prop :=
  Nonempty
    ((IdeleClassGroup K ⧸ (RelativeIdeleGroup.classNorm K L).range) ≃ₜ*
      (L ≃ₐ[K] L))

end FiniteAbelianGlobalReciprocity

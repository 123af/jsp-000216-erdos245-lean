import Jsp000216.CyclicDenseCoreFromBohr
import Jsp000216.GAPCoverReduction

namespace Jsp000216

noncomputable section

/-- Existentially package the explicit GAP-cover constants while they are still
variables.  Keeping this wrapper generic is important: after specialization to
Erdős #245 the coarse explicit exponent is astronomically large, but its value
is irrelevant to the infinite argument. -/
theorem exists_uniformGAPCoverF_of_denseCore {K R D : ℕ}
    (hK : 1 ≤ K) (hcore : DenseGAPCoreF K R D) :
    ∃ R' C' : ℕ, UniformGAPCoverF K R' C' := by
  exact ⟨R + K ^ 5 * D, 2 ^ (R + K ^ 5 * D) * K ^ 4,
    uniformGAPCoverF_of_denseCore hK hcore⟩

/-- Cyclic density parameter required by the Ruzsa-model reduction at
integer doubling constant `12`. -/
def erdos245CyclicDensityQF : ℕ := 32 * 12 ^ 16

/-- Rank of the proper dense integer GAP core obtained from the cyclic Bohr
progression. -/
def erdos245DenseRankF : ℕ := bohrCoreRankF erdos245CyclicDensityQF

/-- Cardinality factor of the proper dense integer GAP core. -/
def erdos245DenseFactorF : ℕ := 16 * bohrCoreCardFactorF erdos245CyclicDensityQF

/-- The structural input previously isolated as an assumption is now
unconditional: there exist fixed rank and box-cardinality constants such that
every finite integer set of doubling at most `12` is contained in a GAP with
those uniform bounds. -/
theorem erdos245_exists_uniformGAPCoverF :
    ∃ R C : ℕ, UniformGAPCoverF 12 R C := by
  have hqpos : 0 < erdos245CyclicDensityQF := by
    dsimp [erdos245CyclicDensityQF]
    positivity
  have hq : 1 ≤ erdos245CyclicDensityQF := Nat.one_le_iff_ne_zero.mpr hqpos.ne'
  have hcyc :
      UniformCyclicDenseCoreF erdos245CyclicDensityQF
        (bohrCoreRankF erdos245CyclicDensityQF)
        (bohrCoreCardFactorF erdos245CyclicDensityQF) :=
    uniformCyclicDenseCoreF_from_bohr erdos245CyclicDensityQF hq
  have hcyc' :
      UniformCyclicDenseCoreF (32 * 12 ^ 16)
        (bohrCoreRankF erdos245CyclicDensityQF)
        (bohrCoreCardFactorF erdos245CyclicDensityQF) := by
    rw [← show erdos245CyclicDensityQF = 32 * 12 ^ 16 by rfl]
    exact hcyc
  have hcore0 :=
    denseGAPCoreF_of_cyclicDenseCore
      (K := 12)
      (R := bohrCoreRankF erdos245CyclicDensityQF)
      (D := bohrCoreCardFactorF erdos245CyclicDensityQF)
      (by omega)
      hcyc'
  have hcore : DenseGAPCoreF 12 erdos245DenseRankF erdos245DenseFactorF := by
    exact hcore0
  exact exists_uniformGAPCoverF_of_denseCore (by omega) hcore

end

end Jsp000216

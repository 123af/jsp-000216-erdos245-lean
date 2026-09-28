import Jsp000216.CyclicDenseCoreFromBohr
import Jsp000216.GAPCoverReduction

namespace Jsp000216

noncomputable section

/-- Cyclic density parameter required by the Ruzsa-model reduction at
integer doubling constant `12`. -/
def erdos245CyclicDensityQF : ℕ := 32 * 12 ^ 16

/-- Rank of the proper dense integer GAP core obtained from the cyclic Bohr
progression. -/
def erdos245DenseRankF : ℕ := bohrCoreRankF erdos245CyclicDensityQF

/-- Cardinality factor of the proper dense integer GAP core. -/
def erdos245DenseFactorF : ℕ := 16 * bohrCoreCardFactorF erdos245CyclicDensityQF

/-- Rank budget for one explicit final (not necessarily proper) GAP cover. -/
def erdos245CoverRankF : ℕ :=
  erdos245DenseRankF + 12 ^ 5 * erdos245DenseFactorF

/-- Box-cardinality factor for the same explicit final GAP cover.

This value is intentionally not unfolded in the final structural theorem:
its exponent is astronomically large, while the infinite argument only needs
existence of some uniform constants. -/
def erdos245CoverFactorF : ℕ :=
  2 ^ erdos245CoverRankF * 12 ^ 4

/-- The structural input previously isolated as an assumption is now
unconditional: there exist fixed rank and box-cardinality constants such that
every finite integer set of doubling at most `12` is contained in a GAP with
those uniform bounds.

The constants are existentially packaged so the kernel never needs to reduce
the enormous closed exponent occurring in one coarse explicit choice. -/
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
  have hcover :=
    uniformGAPCoverF_of_denseCore
      (K := 12)
      (R := erdos245DenseRankF)
      (D := erdos245DenseFactorF)
      (by omega)
      hcore
  exact ⟨_, _, hcover⟩

end

end Jsp000216

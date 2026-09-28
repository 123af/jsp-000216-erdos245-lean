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

/-- Rank budget for the final (not necessarily proper) GAP cover used by the
infinite counting argument. -/
def erdos245CoverRankF : ℕ :=
  erdos245DenseRankF + 12 ^ 5 * erdos245DenseFactorF

/-- Box-cardinality factor for the final GAP cover. -/
def erdos245CoverFactorF : ℕ :=
  2 ^ erdos245CoverRankF * 12 ^ 4

/-- The structural input previously isolated as an assumption is now an
unconditional theorem: every finite integer set of doubling at most `12` is
contained in a uniformly bounded-rank GAP of uniformly linear box size. -/
theorem erdos245_uniformGAPCoverF :
    UniformGAPCoverF 12 erdos245CoverRankF erdos245CoverFactorF := by
  have hq : 1 ≤ erdos245CyclicDensityQF := by
    dsimp [erdos245CyclicDensityQF]
    positivity
  have hcyc :
      UniformCyclicDenseCoreF erdos245CyclicDensityQF
        (bohrCoreRankF erdos245CyclicDensityQF)
        (bohrCoreCardFactorF erdos245CyclicDensityQF) :=
    uniformCyclicDenseCoreF_from_bohr erdos245CyclicDensityQF hq
  have hcore : DenseGAPCoreF 12 erdos245DenseRankF erdos245DenseFactorF := by
    dsimp [erdos245DenseRankF, erdos245DenseFactorF]
    apply denseGAPCoreF_of_cyclicDenseCore (K := 12) (by omega)
    simpa [erdos245CyclicDensityQF] using hcyc
  have hcover := uniformGAPCoverF_of_denseCore (K := 12)
    (R := erdos245DenseRankF) (D := erdos245DenseFactorF) (by omega) hcore
  simpa [erdos245CoverRankF, erdos245CoverFactorF] using hcover

end

end Jsp000216

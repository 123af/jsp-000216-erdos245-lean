import Jsp000216.BohrMinkowskiProgression
import Jsp000216.CyclicCoreReduction

open scoped BigOperators Pointwise

namespace Jsp000216

noncomputable section

/-- Rank budget coming from the large-spectrum cardinality bound. -/
def bohrCoreRankF (q : ℕ) : ℕ := 16 * q ^ 3 + 1

/-- A deliberately coarse fixed cardinality factor.  It is a finite sum of
all dimension constants that can occur below the rank budget, so the actual
constant is literally one nonnegative summand. -/
def bohrCoreCardFactorF (q : ℕ) : ℕ :=
  ∑ m in Finset.range (bohrCoreRankF q + 1),
    (16 * m) ^ m * 2 ^ (m * (m - 1) / 2)

/-- The Fourier large-spectrum bound plus the box-Minkowski Bohr progression
close the uniform cyclic dense-core input with explicit, if very coarse,
constants. -/
theorem uniformCyclicDenseCoreF_from_bohr (q : ℕ) (hq : 1 ≤ q) :
    UniformCyclicDenseCoreF q (bohrCoreRankF q) (bohrCoreCardFactorF q) := by
  intro N inst hN B hB hdense
  let Gamma : Finset (ZMod N) :=
    cyclicLargeSpectrumF B ((B.card : ℝ) / (4 * q))
  have hGcard : Gamma.card ≤ 16 * q ^ 3 := by
    dsimp [Gamma]
    exact card_largeSpectrumF_le_of_density q hq B hB hdense
  obtain ⟨Q, hQrank, hQproper, hQbohr, hNbound⟩ :=
    exists_proper_bohr_progression_dimension_boundF Gamma hN
  have hQsub : Q.carrier ⊆ 2 • B - 2 • B := by
    apply hQbohr.trans
    dsimp [Gamma]
    exact cyclicBohrSetF_subset_fourfoldDifference q hq B hB hdense
  have hmM : Gamma.card + 1 ≤ bohrCoreRankF q := by
    dsimp [bohrCoreRankF]
    omega
  have hQrank' : Q.rank ≤ bohrCoreRankF q := by
    rw [hQrank]
    exact hmM
  let m := Gamma.card + 1
  have hmmem : m ∈ Finset.range (bohrCoreRankF q + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (by simpa [m] using hmM)
  have hterm :
      (16 * m) ^ m * 2 ^ (m * (m - 1) / 2) ≤ bohrCoreCardFactorF q := by
    dsimp [bohrCoreCardFactorF]
    exact Finset.single_le_sum (fun i hi => Nat.zero_le _) hmmem
  have hKleD :
      (16 * (m : ℝ)) ^ m * minkowskiBoxConstantF m ≤
        (bohrCoreCardFactorF q : ℝ) := by
    rw [minkowskiBoxConstantF]
    exact_mod_cast hterm
  have hNbound' :
      (N : ℝ) ≤ (bohrCoreCardFactorF q : ℝ) * (Q.carrier.card : ℝ) := by
    calc
      (N : ℝ) ≤
          ((16 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1) *
            minkowskiBoxConstantF (Gamma.card + 1)) * (Q.carrier.card : ℝ) := hNbound
      _ = ((16 * (m : ℝ)) ^ m * minkowskiBoxConstantF m) *
            (Q.carrier.card : ℝ) := by rfl
      _ ≤ (bohrCoreCardFactorF q : ℝ) * (Q.carrier.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right hKleD (by positivity)
  have hNboundNat : N ≤ bohrCoreCardFactorF q * Q.carrier.card := by
    exact_mod_cast hNbound'
  have hBcardN : B.card ≤ N := by
    calc
      B.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ B
      _ = N := by simp
  exact ⟨Q, hQrank', hQproper, hQsub, hBcardN.trans hNboundNat⟩

end

end Jsp000216

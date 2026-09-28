import Jsp000216.BohrMinkowski
import Jsp000216.BohrProgression

open scoped BigOperators Matrix Pointwise

namespace Jsp000216

noncomputable section

/-- At the natural scale `N/4`, the Minkowski certificate already yields a
proper progression inside the radius-`1/2` Bohr neighborhood. -/
theorem exists_proper_bohr_progressionF {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    ∃ Q : CyclicGAPF N,
      Q.rank = Gamma.card + 1 ∧
      Q.Proper ∧
      Q.carrier ⊆ cyclicBohrSetF Gamma (1 / 2) := by
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (Nat.zero_lt_one.trans hN)
  have hR : (0 : ℝ) < (N : ℝ) / 4 := by positivity
  let C := bohrLatticeCertificateF_of_minkowski Gamma hN ((N : ℝ) / 4) hR
  refine ⟨C.progression, ?_, ?_, ?_⟩
  · exact C.progression_rank
  · apply C.progression_proper hN hR
    dsimp [C]
    nlinarith
  · apply C.progression_carrier_subset_bohr hN hR
    dsimp [C]
    nlinarith

/-- At scale `N/4`, the denominator in the raw progression lower bound has
one residual factor `1/N`; everything else depends only on the dimension. -/
lemma bohrMinkowski_raw_denominator_eqF {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    ((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiBoxConstantF (Gamma.card + 1) * (N : ℝ) ^ Gamma.card /
          ((N : ℝ) / 4) ^ (Gamma.card + 1)) =
      ((16 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1) *
          minkowskiBoxConstantF (Gamma.card + 1)) / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (Nat.zero_lt_one.trans hN)
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  rw [div_pow]
  field_simp [hN0]
  rw [pow_succ]
  ring

/-- The same progression carries the raw quantitative lower bound supplied by
the certificate layer, before simplifying the dimension-only constant. -/
theorem exists_proper_bohr_progression_raw_boundF {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    ∃ Q : CyclicGAPF N,
      Q.rank = Gamma.card + 1 ∧
      Q.Proper ∧
      Q.carrier ⊆ cyclicBohrSetF Gamma (1 / 2) ∧
      ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
          (minkowskiBoxConstantF (Gamma.card + 1) * (N : ℝ) ^ Gamma.card /
            ((N : ℝ) / 4) ^ (Gamma.card + 1)))⁻¹) ≤
        (Q.carrier.card : ℝ) := by
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (Nat.zero_lt_one.trans hN)
  have hR : (0 : ℝ) < (N : ℝ) / 4 := by positivity
  let C := bohrLatticeCertificateF_of_minkowski Gamma hN ((N : ℝ) / 4) hR
  refine ⟨C.progression, C.progression_rank, ?_, ?_, ?_⟩
  · apply C.progression_proper hN hR
    dsimp [C]
    nlinarith
  · apply C.progression_carrier_subset_bohr hN hR
    dsimp [C]
    nlinarith
  · simpa [C] using C.progression_carrier_card_lower_bound hN hR (by
      dsimp [C]
      nlinarith)

end

end Jsp000216

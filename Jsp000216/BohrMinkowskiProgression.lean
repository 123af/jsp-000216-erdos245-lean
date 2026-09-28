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

end

end Jsp000216

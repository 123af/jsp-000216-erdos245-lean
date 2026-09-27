import MiscYD.AddCombi.Kneser.Kneser

open scoped Pointwise

namespace Jsp000216

/-- Kneser's addition theorem specialized to a self-sum in the cyclic group `ZMod n`.

This is a thin project-local wrapper around the Apache-2.0 formalization by
Mantas Bakšys and Yaël Dillies in `MiscYD.AddCombi.Kneser.Kneser`. -/
theorem zmod_self_kneser {n : ℕ} (A : Finset (ZMod n)) :
    2 * (A + (A + A).addStab).card ≤
      (A + A).card + (A + A).addStab.card := by
  simpa [two_mul] using Finset.add_kneser A A

end Jsp000216

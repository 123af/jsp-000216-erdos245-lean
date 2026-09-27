import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Tactic

open Set

namespace Jsp000216

variable (A : Set ℤ)

noncomputable def intervalHoles : Set ℤ :=
  {x | 0 ≤ x ∧ x ≤ sSup A ∧ x ∉ A}

noncomputable def lowerSumHoles : Set ℤ :=
  {x | x ∈ intervalHoles A ∧ x ∈ A + A}

noncomputable def upperSumHoles : Set ℤ :=
  {x | x ∈ intervalHoles A ∧ sSup A + x ∈ A + A}

noncomputable def stableHoles : Set ℤ :=
  intervalHoles A \ (lowerSumHoles A ∪ upperSumHoles A)

lemma stableHoles_empty_iff :
    stableHoles A = ∅ ↔ intervalHoles A ⊆ lowerSumHoles A ∪ upperSumHoles A := by
  constructor
  · intro h x hx
    by_contra hxlu
    have : x ∈ stableHoles A := by
      exact ⟨hx, hxlu⟩
    simpa [h] using this
  · intro h
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxH, hxnot⟩
      exact (hxnot (h hxH)).elim
    · intro hx
      simpa using hx

end Jsp000216

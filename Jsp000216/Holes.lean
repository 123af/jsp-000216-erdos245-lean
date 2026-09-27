import Mathlib

open Set
open scoped Pointwise

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
  change intervalHoles A \ (lowerSumHoles A ∪ upperSumHoles A) = ∅ ↔ _
  exact Set.sdiff_eq_empty

end Jsp000216

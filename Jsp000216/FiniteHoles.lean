import Mathlib

open scoped Pointwise

namespace Jsp000216

/-- Missing points of `A` inside the normalized interval `[0,n]`. -/
def intervalHolesF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  Finset.Icc 0 n \ A

/-- Interval holes already represented in the lower half of `A+A`. -/
def lowerSumHolesF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  intervalHolesF A n ∩ (A + A)

/-- Interval holes `x` for which `n+x` is represented in `A+A`. -/
def upperSumHolesF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  (intervalHolesF A n).filter fun x => n + x ∈ A + A

/-- Holes represented neither below nor above the midpoint `n`. -/
def stableHolesF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  intervalHolesF A n \ (lowerSumHolesF A n ∪ upperSumHolesF A n)

@[simp] lemma mem_intervalHolesF {A : Finset ℤ} {n x : ℤ} :
    x ∈ intervalHolesF A n ↔ 0 ≤ x ∧ x ≤ n ∧ x ∉ A := by
  simp [intervalHolesF, and_assoc]

@[simp] lemma mem_lowerSumHolesF {A : Finset ℤ} {n x : ℤ} :
    x ∈ lowerSumHolesF A n ↔ x ∈ intervalHolesF A n ∧ x ∈ A + A := by
  simp [lowerSumHolesF]

@[simp] lemma mem_upperSumHolesF {A : Finset ℤ} {n x : ℤ} :
    x ∈ upperSumHolesF A n ↔ x ∈ intervalHolesF A n ∧ n + x ∈ A + A := by
  simp [upperSumHolesF]

lemma stableHolesF_empty_iff {A : Finset ℤ} {n : ℤ} :
    stableHolesF A n = ∅ ↔
      intervalHolesF A n ⊆ lowerSumHolesF A n ∪ upperSumHolesF A n := by
  simp [stableHolesF]

lemma card_intervalHolesF_of_subset {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) :
    (intervalHolesF A n).card = (Finset.Icc 0 n).card - A.card := by
  exact Finset.card_sdiff_of_subset hA

lemma card_intervalHolesF_le_card_lower_add_upper_of_stable_empty
    {A : Finset ℤ} {n : ℤ} (hstable : stableHolesF A n = ∅) :
    (intervalHolesF A n).card ≤
      (lowerSumHolesF A n).card + (upperSumHolesF A n).card := by
  have hsub : intervalHolesF A n ⊆ lowerSumHolesF A n ∪ upperSumHolesF A n :=
    (stableHolesF_empty_iff).mp hstable
  calc
    (intervalHolesF A n).card ≤
        (lowerSumHolesF A n ∪ upperSumHolesF A n).card := Finset.card_le_card hsub
    _ ≤ (lowerSumHolesF A n).card + (upperSumHolesF A n).card :=
      Finset.card_union_le (lowerSumHolesF A n) (upperSumHolesF A n)

end Jsp000216

import Jsp000216.FiniteCount

open scoped Pointwise

namespace Jsp000216

lemma card_Icc_eq_card_add_holes {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) :
    (Finset.Icc 0 n).card = A.card + (intervalHolesF A n).card := by
  have hholes := card_intervalHolesF_of_subset hA
  have hcard : A.card ≤ (Finset.Icc 0 n).card := Finset.card_le_card hA
  omega

lemma card_Icc_le_card_add_lower_add_upper_of_no_stable
    {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (hstable : stableHolesF A n = ∅) :
    (Finset.Icc 0 n).card ≤
      A.card + (lowerSumHolesF A n).card + (upperSumHolesF A n).card := by
  have hIcc := card_Icc_eq_card_add_holes hA
  have hholes := card_intervalHolesF_le_card_lower_add_upper_of_stable_empty hstable
  omega

lemma no_stable_interval_length_le_sumset_sub_card_add_one
    {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (h0 : 0 ∈ A) (hn : n ∈ A)
    (hstable : stableHolesF A n = ∅) :
    (Finset.Icc 0 n).card ≤ (A + A).card - A.card + 1 := by
  have hIcc := card_Icc_le_card_add_lower_add_upper_of_no_stable hA hstable
  have hsum := two_card_add_holes_le_sumset_add_one hA h0 hn
  have hA_sum : A.card ≤ (A + A).card := by
    exact Finset.card_le_card (subset_self_sumset_of_zero h0)
  omega

end Jsp000216

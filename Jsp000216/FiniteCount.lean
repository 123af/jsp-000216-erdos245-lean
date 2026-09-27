import Jsp000216.FiniteRanges

open scoped Pointwise

namespace Jsp000216

lemma card_lower_union_upper_add_one {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (h0 : 0 ∈ A) (hn : n ∈ A) :
    (lowerPieceF A n ∪ upperPieceF A n).card + 1 =
      2 * A.card + (lowerSumHolesF A n).card + (upperSumHolesF A n).card := by
  have hcard := Finset.card_union_add_card_inter (lowerPieceF A n) (upperPieceF A n)
  rw [lowerPieceF_inter_upperPieceF hA h0 hn, Finset.card_singleton,
    card_lowerPieceF, card_upperPieceF] at hcard
  omega

lemma lower_union_upper_subset_sumset {A : Finset ℤ} {n : ℤ}
    (h0 : 0 ∈ A) (hn : n ∈ A) :
    lowerPieceF A n ∪ upperPieceF A n ⊆ A + A := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxL | hxU
  · exact lowerPieceF_subset_sumset h0 hxL
  · exact upperPieceF_subset_sumset hn hxU

lemma two_card_add_holes_le_sumset_add_one {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (h0 : 0 ∈ A) (hn : n ∈ A) :
    2 * A.card + (lowerSumHolesF A n).card + (upperSumHolesF A n).card ≤
      (A + A).card + 1 := by
  have hsub : lowerPieceF A n ∪ upperPieceF A n ⊆ A + A :=
    lower_union_upper_subset_sumset h0 hn
  have hcardle := Finset.card_le_card hsub
  have heq := card_lower_union_upper_add_one hA h0 hn
  omega

lemma hole_contribution_le_card_sub_three_of_small_doubling
    {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (h0 : 0 ∈ A) (hn : n ∈ A)
    (hcard : 3 ≤ A.card) (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    (lowerSumHolesF A n).card + (upperSumHolesF A n).card ≤ A.card - 3 := by
  have hbase := two_card_add_holes_le_sumset_add_one hA h0 hn
  omega

end Jsp000216

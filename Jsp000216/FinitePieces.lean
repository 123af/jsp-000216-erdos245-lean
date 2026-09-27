import Jsp000216.FiniteTranslate

open scoped Pointwise

namespace Jsp000216

/-- The lower half of the normalized sumset decomposition. -/
def lowerPieceF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  A ∪ lowerSumHolesF A n

/-- The unshifted base of the upper half of the normalized sumset decomposition. -/
def upperBaseF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  A ∪ upperSumHolesF A n

/-- The upper half of the normalized sumset decomposition. -/
def upperPieceF (A : Finset ℤ) (n : ℤ) : Finset ℤ :=
  translateF n (upperBaseF A n)

lemma disjoint_A_lowerSumHolesF (A : Finset ℤ) (n : ℤ) :
    Disjoint A (lowerSumHolesF A n) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxA hxL
  have hxH : x ∈ intervalHolesF A n := (mem_lowerSumHolesF.mp hxL).1
  exact (mem_intervalHolesF.mp hxH).2.2 hxA

lemma disjoint_A_upperSumHolesF (A : Finset ℤ) (n : ℤ) :
    Disjoint A (upperSumHolesF A n) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxA hxU
  have hxH : x ∈ intervalHolesF A n := (mem_upperSumHolesF.mp hxU).1
  exact (mem_intervalHolesF.mp hxH).2.2 hxA

lemma card_lowerPieceF (A : Finset ℤ) (n : ℤ) :
    (lowerPieceF A n).card = A.card + (lowerSumHolesF A n).card := by
  unfold lowerPieceF
  exact Finset.card_union_of_disjoint (disjoint_A_lowerSumHolesF A n)

lemma card_upperBaseF (A : Finset ℤ) (n : ℤ) :
    (upperBaseF A n).card = A.card + (upperSumHolesF A n).card := by
  unfold upperBaseF
  exact Finset.card_union_of_disjoint (disjoint_A_upperSumHolesF A n)

lemma card_upperPieceF (A : Finset ℤ) (n : ℤ) :
    (upperPieceF A n).card = A.card + (upperSumHolesF A n).card := by
  rw [upperPieceF, card_translateF, card_upperBaseF]

lemma lowerPieceF_subset_sumset {A : Finset ℤ} {n : ℤ} (h0 : 0 ∈ A) :
    lowerPieceF A n ⊆ A + A := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxA | hxL
  · exact (subset_self_sumset_of_zero h0) hxA
  · exact lowerSumHolesF_subset_sumset hxL

lemma upperPieceF_subset_sumset {A : Finset ℤ} {n : ℤ} (hn : n ∈ A) :
    upperPieceF A n ⊆ A + A := by
  intro y hy
  rcases mem_translateF.mp hy with ⟨x, hx, rfl⟩
  rcases Finset.mem_union.mp hx with hxA | hxU
  · exact Finset.mem_add.mpr ⟨n, hn, x, hxA, rfl⟩
  · exact (mem_upperSumHolesF.mp hxU).2

end Jsp000216

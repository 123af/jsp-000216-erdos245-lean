import Jsp000216.FinitePieces

open scoped Pointwise

namespace Jsp000216

lemma lowerPieceF_le_endpoint {A : Finset ℤ} {n x : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (hx : x ∈ lowerPieceF A n) :
    x ≤ n := by
  rcases Finset.mem_union.mp hx with hxA | hxL
  · exact (Finset.mem_Icc.mp (hA hxA)).2
  · have hxH : x ∈ intervalHolesF A n := (mem_lowerSumHolesF.mp hxL).1
    exact (mem_intervalHolesF.mp hxH).2.1

lemma endpoint_le_upperPieceF {A : Finset ℤ} {n y : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (hy : y ∈ upperPieceF A n) :
    n ≤ y := by
  rcases mem_translateF.mp hy with ⟨x, hx, rfl⟩
  have hx0 : 0 ≤ x := by
    rcases Finset.mem_union.mp hx with hxA | hxU
    · exact (Finset.mem_Icc.mp (hA hxA)).1
    · have hxH : x ∈ intervalHolesF A n := (mem_upperSumHolesF.mp hxU).1
      exact (mem_intervalHolesF.mp hxH).1
  omega

lemma lowerPieceF_inter_upperPieceF {A : Finset ℤ} {n : ℤ}
    (hA : A ⊆ Finset.Icc 0 n) (h0 : 0 ∈ A) (hn : n ∈ A) :
    lowerPieceF A n ∩ upperPieceF A n = {n} := by
  ext x
  constructor
  · intro hx
    have hxi := Finset.mem_inter.mp hx
    have hle : x ≤ n := lowerPieceF_le_endpoint hA hxi.1
    have hge : n ≤ x := endpoint_le_upperPieceF hA hxi.2
    have hxn : x = n := le_antisymm hle hge
    simpa [hxn]
  · intro hx
    have hxn : x = n := by simpa using hx
    subst x
    apply Finset.mem_inter.mpr
    constructor
    · simp [lowerPieceF, hn]
    · apply mem_translateF.mpr
      refine ⟨0, ?_, by simp⟩
      simp [upperBaseF, h0]

end Jsp000216

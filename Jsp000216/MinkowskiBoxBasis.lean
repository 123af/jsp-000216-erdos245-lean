import Jsp000216.MinkowskiBoxCore

open scoped BigOperators Matrix
open Module Submodule Set

namespace Jsp000216

noncomputable section

/-- Cast an integral coordinate vector to real coordinates. -/
def intCastVecF {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ := fun i => (z i : ℝ)

/-- A nonsingular matrix packages its columns as a real basis. -/
noncomputable def matrixBasisF {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map
    (D.toLinearEquiv' (D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hD)))

@[simp] lemma matrixBasisF_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) (j : Fin n) :
    matrixBasisF D hD j = fun i => D i j := by
  ext i
  rw [matrixBasisF, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.mulVec D (Pi.single j 1) i = D i j
  simp [Matrix.mulVec]

lemma projectedTailF_det_ne_zero {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    (projectedTailF h B).det ≠ 0 := by
  intro hq
  have habs := abs_det_eq_abs_pivot_mul_projectedTailF h B hB
  rw [hq, abs_zero, mul_zero] at habs
  exact hdet (abs_eq_zero.mp habs)

noncomputable def projectedTailBasisF {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  matrixBasisF (projectedTailF h B) (projectedTailF_det_ne_zero h B hdet hB)

@[simp] lemma projectedTailBasisF_apply {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) (j : Fin n) :
    projectedTailBasisF h B hdet hB j = (projectedTailF h B).col j := by
  simp [projectedTailBasisF, matrixBasisF_apply]

/-- Lift integral tail coordinates back to the original matrix columns. -/
def rawTailLiftF {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Matrix.mulVec B (Fin.cons 0 (intCastVecF z))

lemma deleteProjectionF_rawTailLiftF {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    deleteProjectionF h (fun i => B i 0) (rawTailLiftF B z) =
      Matrix.mulVec (projectedTailF h B) (intCastVecF z) := by
  funext i
  simp only [deleteProjectionF, rawTailLiftF, Matrix.mulVec, dotProduct,
    projectedTailF, intCastVecF]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Integral combinations of a matrix's columns lie in the integer span of
its column basis. -/
lemma matrix_mulVec_intCastVecF_mem_span {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (z : Fin n → ℤ) :
    Matrix.mulVec D (intCastVecF z) ∈
      Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨z, ?_⟩
  ext i
  simp [Matrix.mulVec, dotProduct, intCastVecF, mul_comm]

end

end Jsp000216

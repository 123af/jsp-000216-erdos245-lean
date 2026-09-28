import Jsp000216.MinkowskiBoxCore

open scoped BigOperators Matrix
open Module Submodule Set

namespace Jsp000216

noncomputable section

/-- Cast an integral coordinate vector to real coordinates. -/
def intCastVecF {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ := fun i => (z i : ℝ)

@[simp] lemma intCastVecF_cons {n : ℕ} (a : ℤ) (z : Fin n → ℤ) :
    intCastVecF (Fin.cons a z) = Fin.cons (a : ℝ) (intCastVecF z) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [intCastVecF]

lemma intCastVecF_ne_zero {n : ℕ} {z : Fin n → ℤ} (hz : z ≠ 0) :
    intCastVecF z ≠ 0 := by
  intro hzero
  apply hz
  funext i
  have hi := congrFun hzero i
  simpa [intCastVecF] using hi

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
  funext i
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
  dsimp [intCastVecF]
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

lemma matrix_mulVec_intCastVecF_ne_zero {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    {z : Fin n → ℤ} (hz : z ≠ 0) :
    Matrix.mulVec D (intCastVecF z) ≠ 0 := by
  intro hzero
  have hinj := Matrix.mulVec_injective_of_det_ne_zero hD
  have hzcast : intCastVecF z = 0 := hinj (by simpa using hzero)
  exact (intCastVecF_ne_zero hz) hzcast

/-- A raw tail lift is an honest point of the original integer lattice. -/
lemma rawTailLiftF_mem_span {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B.det ≠ 0)
    (z : Fin n → ℤ) :
    rawTailLiftF B z ∈
      Submodule.span ℤ (Set.range (matrixBasisF B hB)) := by
  simpa [rawTailLiftF] using
    (matrix_mulVec_intCastVecF_mem_span B hB (Fin.cons 0 z))

/-- Integer correction which moves a raw tail lift into the centred strip
around the hyperplane transverse to the first lattice vector. -/
noncomputable def reducedTailCoefficientF {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : ℤ :=
  -roundedCoefficientF ((rawTailLiftF B z) h / B h 0)

/-- Correct a raw tail lift by an integral multiple of the first column. -/
noncomputable def reducedTailLiftF {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  rawTailLiftF B z + reducedTailCoefficientF h B z • (fun i => B i 0)

lemma reducedTailLiftF_eq_add_real_smul {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) :
    reducedTailLiftF h B z =
      rawTailLiftF B z +
        (reducedTailCoefficientF h B z : ℝ) • (fun i => B i 0) := by
  rw [reducedTailLiftF, Int.cast_smul_eq_zsmul]

lemma reducedTailCoefficientF_rounding {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) :
    |(rawTailLiftF B z) h / B h 0 +
        (reducedTailCoefficientF h B z : ℝ)| ≤ (1 : ℝ) / 2 := by
  simpa [reducedTailCoefficientF, sub_eq_add_neg] using
    abs_sub_roundedCoefficientF_le_half ((rawTailLiftF B z) h / B h 0)

lemma reducedTailLiftF_mem_span {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B.det ≠ 0) (z : Fin n → ℤ) :
    reducedTailLiftF h B z ∈
      Submodule.span ℤ (Set.range (matrixBasisF B hB)) := by
  let L := Submodule.span ℤ (Set.range (matrixBasisF B hB))
  have hraw : rawTailLiftF B z ∈ L := rawTailLiftF_mem_span B hB z
  have hcol : (fun i => B i 0) ∈ L := by
    rw [← matrixBasisF_apply B hB 0]
    exact Submodule.subset_span (Set.mem_range_self 0)
  exact L.add_mem hraw (L.smul_mem (reducedTailCoefficientF h B z) hcol)

lemma deleteProjectionF_reducedTailLiftF {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB0 : B h 0 ≠ 0) (z : Fin n → ℤ) :
    deleteProjectionF h (fun i => B i 0) (reducedTailLiftF h B z) =
      Matrix.mulVec (projectedTailF h B) (intCastVecF z) := by
  rw [reducedTailLiftF_eq_add_real_smul]
  rw [deleteProjectionF_add_smul h _ _ _ hB0]
  exact deleteProjectionF_rawTailLiftF h B z

lemma reducedTailLiftF_ne_zero {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB0 : B h 0 ≠ 0)
    {z : Fin n → ℤ} (hz : z ≠ 0) :
    reducedTailLiftF h B z ≠ 0 := by
  intro hzero
  have hproj0 : Matrix.mulVec (projectedTailF h B) (intCastVecF z) = 0 := by
    rw [← deleteProjectionF_reducedTailLiftF h B hB0 z, hzero]
    funext i
    change (0 : ℝ) - ((0 : ℝ) / B h 0) * B (h.succAbove i) 0 = 0
    ring
  exact (matrix_mulVec_intCastVecF_ne_zero
    (projectedTailF h B) (projectedTailF_det_ne_zero h B hdet hB0) hz) hproj0

lemma norm_reducedTailLiftF_le {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hh : |B h 0| = ‖fun i => B i 0‖) (hB0 : B h 0 ≠ 0)
    (z : Fin n → ℤ) {t : ℝ}
    (hproj : ‖Matrix.mulVec (projectedTailF h B) (intCastVecF z)‖ ≤ t) :
    ‖reducedTailLiftF h B z‖ ≤ t + ‖fun i => B i 0‖ / 2 := by
  rw [reducedTailLiftF_eq_add_real_smul]
  have hproj' :
      ‖deleteProjectionF h (fun i => B i 0) (rawTailLiftF B z)‖ ≤ t := by
    rw [deleteProjectionF_rawTailLiftF]
    exact hproj
  exact reducedLift_apply_leF h (fun i => B i 0) (rawTailLiftF B z)
    t (reducedTailCoefficientF h B z : ℝ) hh hB0
    (reducedTailCoefficientF_rounding h B z) hproj'

/-- If the first column is a shortest nonzero lattice vector, every nonzero
projected tail vector has a reduced lift with at most twice its projected norm. -/
lemma norm_reducedTailLiftF_le_two_mul_projected {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB0 : B h 0 ≠ 0)
    (hh : |B h 0| = ‖fun i => B i 0‖)
    (hshort : ∀ x ∈ Submodule.span ℤ (Set.range (matrixBasisF B hdet)),
      x ≠ 0 → ‖fun i => B i 0‖ ≤ ‖x‖)
    {z : Fin n → ℤ} (hz : z ≠ 0) :
    ‖reducedTailLiftF h B z‖ ≤
      2 * ‖Matrix.mulVec (projectedTailF h B) (intCastVecF z)‖ := by
  let t := ‖Matrix.mulVec (projectedTailF h B) (intCastVecF z)‖
  have hupp : ‖reducedTailLiftF h B z‖ ≤
      t + ‖fun i => B i 0‖ / 2 :=
    norm_reducedTailLiftF_le h B hh hB0 z (t := t) le_rfl
  have hmem := reducedTailLiftF_mem_span h B hdet z
  have hne := reducedTailLiftF_ne_zero h B hdet hB0 hz
  have hlow := hshort (reducedTailLiftF h B z) hmem hne
  have ht : 0 ≤ t := norm_nonneg _
  dsimp [t] at hupp ⊢
  nlinarith

/-- Write an arbitrary integral basis of the column lattice as an ambient
real matrix, with the basis vectors as columns. -/
noncomputable def latticeBasisMatrixF {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (b : Basis (Fin n) ℤ
      (Submodule.span ℤ (Set.range (matrixBasisF D hD)))) :
    Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.of (fun j i => (b j : Fin n → ℝ) i)).transpose

@[simp] lemma latticeBasisMatrixF_apply {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (b : Basis (Fin n) ℤ
      (Submodule.span ℤ (Set.range (matrixBasisF D hD))))
    (i j : Fin n) :
    latticeBasisMatrixF D hD b i j = (b j : Fin n → ℝ) i := by
  rfl

/-- Changing from the original columns to any integral basis of the same full
lattice preserves the absolute determinant. -/
lemma abs_det_latticeBasisMatrixF {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (b : Basis (Fin n) ℤ
      (Submodule.span ℤ (Set.range (matrixBasisF D hD)))) :
    |(latticeBasisMatrixF D hD b).det| = |D.det| := by
  classical
  let L := Submodule.span ℤ (Set.range (matrixBasisF D hD))
  let b0 : Basis (Fin n) ℤ L := (matrixBasisF D hD).restrictScalars ℤ
  have hb := ZLattice.covolume_eq_det L b
  have hb0 := ZLattice.covolume_eq_det L b0
  change ZLattice.covolume L =
      |(Matrix.of (fun j i => (b j : Fin n → ℝ) i)).det| at hb
  change ZLattice.covolume L =
      |(Matrix.of (fun j i => (b0 j : Fin n → ℝ) i)).det| at hb0
  have hmat : Matrix.of (fun j i => (b0 j : Fin n → ℝ) i) = D.transpose := by
    ext i j
    dsimp [b0]
    change (matrixBasisF D hD i) j = D j i
    rw [matrixBasisF_apply]
  calc
    |(latticeBasisMatrixF D hD b).det| =
        |(Matrix.of (fun j i => (b j : Fin n → ℝ) i)).det| := by
          simp [latticeBasisMatrixF]
    _ = ZLattice.covolume L := hb.symm
    _ = |(Matrix.of (fun j i => (b0 j : Fin n → ℝ) i)).det| := hb0
    _ = |D.det| := by rw [hmat, Matrix.det_transpose]

end

end Jsp000216

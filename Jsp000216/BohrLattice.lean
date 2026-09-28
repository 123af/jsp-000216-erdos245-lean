import Jsp000216.CyclicBohr

open scoped BigOperators Matrix Pointwise

namespace Jsp000216

noncomputable section

/-- Enumerate the trivial character followed by the frequencies in `Gamma`. -/
noncomputable def indexedCyclicCharacterF {N : ℕ}
    (Gamma : Finset (ZMod N)) : Fin (Gamma.card + 1) → ZMod N :=
  Fin.cases 1 fun i => (Gamma.equivFin.symm i : Gamma)

@[simp] lemma indexedCyclicCharacterF_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) :
    indexedCyclicCharacterF Gamma 0 = 1 := rfl

lemma indexedCyclicCharacterF_succ_mem {N : ℕ}
    (Gamma : Finset (ZMod N)) (i : Fin Gamma.card) :
    indexedCyclicCharacterF Gamma i.succ ∈ Gamma := by
  change ((Gamma.equivFin.symm i : Gamma) : ZMod N) ∈ Gamma
  exact (Gamma.equivFin.symm i).property

/-- Integer basis matrix for the full congruence lattice attached to `Gamma`.
Its first column is `(1,k₁,…,k_d)` and the remaining columns are `N e_i`. -/
def bohrLatticeMatrixIntF {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℤ :=
  fun i j => if j = 0 then ((indexedCyclicCharacterF Gamma i).val : ℤ)
    else if i = j then (N : ℤ) else 0

/-- Realification of `bohrLatticeMatrixIntF`. -/
def bohrLatticeMatrixF {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℝ :=
  (bohrLatticeMatrixIntF Gamma).map (Int.castRingHom ℝ)

@[simp] lemma bohrLatticeMatrixIntF_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrixIntF Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrixIntF, (Fin.succ_ne_zero j).symm]

@[simp] lemma bohrLatticeMatrixF_zero_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    bohrLatticeMatrixF Gamma 0 0 = 1 := by
  simp [bohrLatticeMatrixF, bohrLatticeMatrixIntF,
    ZMod.val_one'' (by omega : N ≠ 1)]

@[simp] lemma bohrLatticeMatrixF_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrixF Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrixF]

@[simp] lemma bohrLatticeMatrixF_succ_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (i j : Fin Gamma.card) :
    bohrLatticeMatrixF Gamma i.succ j.succ =
      if i = j then (N : ℝ) else 0 := by
  simp [bohrLatticeMatrixF, bohrLatticeMatrixIntF, Fin.succ_inj]

/-- The congruence lattice has covolume `N ^ |Gamma|`. -/
lemma det_bohrLatticeMatrixF {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrixF Gamma).det = (N : ℝ) ^ Gamma.card := by
  have hminor :
      (bohrLatticeMatrixF Gamma).submatrix Fin.succ (Fin.succAbove 0) =
        Matrix.diagonal (fun _ : Fin Gamma.card => (N : ℝ)) := by
    ext i j
    rw [Matrix.diagonal_apply]
    simp [Matrix.submatrix]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [bohrLatticeMatrixF_zero_zero Gamma hN,
    bohrLatticeMatrixF_zero_succ]
  rw [hminor, Matrix.det_diagonal]
  simp

lemma det_bohrLatticeMatrixF_ne_zero {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrixF Gamma).det ≠ 0 := by
  rw [det_bohrLatticeMatrixF Gamma hN]
  positivity

/-- An integral point in the congruence lattice. -/
def bohrLatticePointF {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  Matrix.mulVec (bohrLatticeMatrixIntF Gamma) z

lemma bohrLatticePointF_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (z : Fin (Gamma.card + 1) → ℤ) :
    bohrLatticePointF Gamma z 0 = z 0 := by
  simp [bohrLatticePointF, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    bohrLatticeMatrixIntF, ZMod.val_one'' (by omega : N ≠ 1),
    (fun x : Fin Gamma.card => (Fin.succ_ne_zero x).symm)]

/-- Every lattice coordinate is congruent modulo `N` to the first coordinate
times the corresponding cyclic character. -/
lemma bohrLatticePointF_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (z : Fin (Gamma.card + 1) → ℤ)
    (hN : 1 < N) (i : Fin (Gamma.card + 1)) :
    (bohrLatticePointF Gamma z i : ZMod N) =
      (bohrLatticePointF Gamma z 0 : ZMod N) *
        indexedCyclicCharacterF Gamma i := by
  rw [bohrLatticePointF_zero Gamma hN]
  simp only [bohrLatticePointF, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  simp only [bohrLatticeMatrixIntF]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [mul_comm]

end

end Jsp000216

import Jsp000216.MinkowskiBoxBasis

open scoped BigOperators Matrix
open Module Submodule Set

namespace Jsp000216

noncomputable section

/-- The dimension loss used by the box induction satisfies the expected
one-step recurrence. -/
lemma minkowskiBoxConstantF_succ (n : ℕ) :
    minkowskiBoxConstantF (n + 1) =
      (2 : ℝ) ^ n * minkowskiBoxConstantF n := by
  simp only [minkowskiBoxConstantF, ← Nat.choose_two_right]
  rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

/-- The ambient matrix attached to an integral basis of the same lattice is
again nonsingular. -/
lemma latticeBasisMatrixF_det_ne_zero {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (b : Basis (Fin n) ℤ
      (Submodule.span ℤ (Set.range (matrixBasisF D hD)))) :
    (latticeBasisMatrixF D hD b).det ≠ 0 := by
  intro hzero
  have habs := abs_det_latticeBasisMatrixF D hD b
  rw [hzero, abs_zero] at habs
  exact hD (abs_eq_zero.mp habs.symm)

/-- The column lattice of a matrix obtained from an integral lattice basis is
contained in the original lattice. -/
lemma span_matrixBasis_latticeBasisMatrixF_le {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (b : Basis (Fin n) ℤ
      (Submodule.span ℤ (Set.range (matrixBasisF D hD)))) :
    Submodule.span ℤ
        (Set.range (matrixBasisF (latticeBasisMatrixF D hD b)
          (latticeBasisMatrixF_det_ne_zero D hD b))) ≤
      Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [matrixBasisF_apply]
  change (fun i => (b j : Fin n → ℝ) i) ∈
    Submodule.span ℤ (Set.range (matrixBasisF D hD))
  exact (b j).property

/-- Membership in the integer span of matrix columns is equivalent to having
integral column coordinates. -/
lemma mem_span_matrixBasisF_iff_exists_intCastVecF {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (x : Fin n → ℝ) :
    x ∈ Submodule.span ℤ (Set.range (matrixBasisF D hD)) ↔
      ∃ z : Fin n → ℤ, Matrix.mulVec D (intCastVecF z) = x := by
  constructor
  · intro hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, ?_⟩
    calc
      Matrix.mulVec D (intCastVecF z) =
          ∑ j, z j • matrixBasisF D hD j := by
            ext i
            simp [Matrix.mulVec, dotProduct, intCastVecF, mul_comm]
      _ = x := hz
  · rintro ⟨z, rfl⟩
    exact matrix_mulVec_intCastVecF_mem_span D hD z

end

end Jsp000216

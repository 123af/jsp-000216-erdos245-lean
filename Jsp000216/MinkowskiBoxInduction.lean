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

/-- Put a shortest nonzero lattice point in the first column of an integral
basis matrix, while preserving determinant and remembering a coordinate where
that first column attains its sup norm. -/
theorem exists_shortest_first_column_basisF {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hD : D.det ≠ 0) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : Fin (n + 1)),
      B.det ≠ 0 ∧
      |B.det| = |D.det| ∧
      (fun i => B i 0) ∈
        Submodule.span ℤ (Set.range (matrixBasisF D hD)) ∧
      (fun i => B i 0) ≠ 0 ∧
      (∀ x ∈ Submodule.span ℤ (Set.range (matrixBasisF D hD)),
        x ≠ 0 → ‖fun i => B i 0‖ ≤ ‖x‖) ∧
      |B h 0| = ‖fun i => B i 0‖ ∧
      B h 0 ≠ 0 ∧
      Submodule.span ℤ (Set.range (fun j => fun i => B i j)) ≤
        Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
  let bD := matrixBasisF D hD
  let L := Submodule.span ℤ (Set.range bD)
  obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_zspan_pointF bD
  let vL : L := ⟨v, hvL⟩
  have hvL0 : vL ≠ 0 := by
    intro hz
    apply hv0
    have hz' := congrArg Subtype.val hz
    simpa [vL] using hz'
  let mu : L → ℝ := fun x => ‖(x : Fin (n + 1) → ℝ)‖
  have hmupos : ∀ x ≠ 0, 0 < mu x := by
    intro x hx
    apply norm_pos_iff.mpr
    intro hcoe
    apply hx
    apply Subtype.ext
    simpa using hcoe
  have hmuhom : ∀ (c : ℤ), 0 < c → ∀ x, mu (c • x) = (c : ℝ) * mu x := by
    intro c hc x
    dsimp [mu]
    change ‖c • (x : Fin (n + 1) → ℝ)‖ =
      (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖
    rw [← Int.cast_smul_eq_zsmul ℝ c, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by exact_mod_cast hc : (0 : ℝ) < c)]
  have hmumin : ∀ x ≠ 0, mu vL ≤ mu x := by
    intro x hx
    dsimp [mu, vL]
    apply hvmin (x : Fin (n + 1) → ℝ) x.property
    intro hcoe
    apply hx
    apply Subtype.ext
    simpa using hcoe
  obtain ⟨b, hb0⟩ := shortest_zspan_vector_extendsF
    (Nat.succ_pos n) bD vL hvL0 mu hmupos hmuhom hmumin
  let B := latticeBasisMatrixF D hD b
  have hBdet : B.det ≠ 0 := by
    dsimp [B]
    exact latticeBasisMatrixF_det_ne_zero D hD b
  have habs : |B.det| = |D.det| := by
    dsimp [B]
    exact abs_det_latticeBasisMatrixF D hD b
  have hcol : (fun i => B i 0) = v := by
    funext i
    dsimp [B]
    rw [latticeBasisMatrixF_apply]
    have hb0' : b (0 : Fin (n + 1)) = vL := by simpa using hb0
    rw [hb0']
  have hcolmem : (fun i => B i 0) ∈
      Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
    rw [hcol]
    exact hvL
  have hcol0 : (fun i => B i 0) ≠ 0 := by
    rw [hcol]
    exact hv0
  have hshort : ∀ x ∈ Submodule.span ℤ (Set.range (matrixBasisF D hD)),
      x ≠ 0 → ‖fun i => B i 0‖ ≤ ‖x‖ := by
    intro x hx hx0
    rw [hcol]
    exact hvmin x hx hx0
  obtain ⟨h, hh0⟩ := (IsGreatest.pi_norm (fun i => B i 0)).1
  have hh : |B h 0| = ‖fun i => B i 0‖ := by
    simpa [Real.norm_eq_abs] using hh0
  have hB0 : B h 0 ≠ 0 := by
    intro hz
    apply hcol0
    apply norm_eq_zero.mp
    rw [← hh, hz, abs_zero]
  have hspan :
      Submodule.span ℤ (Set.range (fun j => fun i => B i j)) ≤
        Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    dsimp [B]
    change (b j : Fin (n + 1) → ℝ) ∈
      Submodule.span ℤ (Set.range (matrixBasisF D hD))
    exact (b j).property
  exact ⟨B, h, hBdet, habs, hcolmem, hcol0, hshort, hh, hB0, hspan⟩

end

end Jsp000216

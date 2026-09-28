import Jsp000216.LatticePrimitive
import Mathlib.Algebra.Module.ZLattice.Covolume

open scoped BigOperators Matrix
open Module Submodule Set

namespace Jsp000216

noncomputable section

/-- Dimension-only loss used in the box induction. -/
def minkowskiBoxConstantF (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n * (n - 1) / 2)

@[simp] lemma minkowskiBoxConstantF_zero : minkowskiBoxConstantF 0 = 1 := by
  simp [minkowskiBoxConstantF]

lemma minkowskiBoxConstantF_nonneg (n : ℕ) : 0 ≤ minkowskiBoxConstantF n :=
  pow_nonneg (by norm_num) _

/-- Every full integer span of a real basis has a shortest nonzero point for
the sup norm. -/
theorem exists_shortest_zspan_pointF {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ)) :
    ∃ v : Fin (n + 1) → ℝ,
      v ∈ Submodule.span ℤ (Set.range b) ∧ v ≠ 0 ∧
        ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  classical
  let e : Fin (n + 1) := 0
  have hbe_mem : b e ∈ Submodule.span ℤ (Set.range b) :=
    Submodule.subset_span ⟨e, rfl⟩
  have hbe_ne : b e ≠ 0 := b.ne_zero e
  let S : Set (Fin (n + 1) → ℝ) :=
    Metric.closedBall 0 ‖b e‖ ∩ Submodule.span ℤ (Set.range b)
  have hSfin : S.Finite := ZSpan.setFinite_inter b Metric.isBounded_closedBall
  let T : Set (Fin (n + 1) → ℝ) := {x ∈ S | x ≠ 0}
  have hTfin : T.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hbeS : b e ∈ S := by
    refine ⟨?_, hbe_mem⟩
    simp
  have hTne : T.Nonempty := ⟨b e, hbeS, hbe_ne⟩
  obtain ⟨v, hvT, hvmin⟩ := Set.exists_min_image T norm hTfin hTne
  refine ⟨v, hvT.1.2, hvT.2, ?_⟩
  intro x hxL hx0
  by_cases hxle : ‖x‖ ≤ ‖b e‖
  · exact hvmin x ⟨⟨by simpa [Metric.mem_closedBall] using hxle, hxL⟩, hx0⟩
  · have hvle : ‖v‖ ≤ ‖b e‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvT.1.1
    exact hvle.trans (le_of_not_ge hxle)

/-- Sup norm is membership in a constant symmetric coordinate box. -/
lemma mem_const_box_iff_norm_leF {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    x ∈ Set.Icc (-(fun _ => s)) (fun _ => s) ↔ ‖x‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs]
  constructor
  · intro hx i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    constructor <;> intro i
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.1
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.2

noncomputable def roundedCoefficientF (a : ℝ) : ℤ := round a

lemma abs_sub_roundedCoefficientF_le_half (a : ℝ) :
    |a - (roundedCoefficientF a : ℝ)| ≤ (1 : ℝ) / 2 := by
  simpa [roundedCoefficientF] using abs_sub_round a

/-- Delete coordinate `h` after projecting along `v`. -/
noncomputable def deleteProjectionF {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => x (h.succAbove i) - (x h / v h) * v (h.succAbove i)

noncomputable def deleteProjectionLinearF {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := deleteProjectionF h v
  map_add' x y := by
    funext i
    simp only [deleteProjectionF, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp [deleteProjectionF]
    ring

lemma deleteProjectionF_add_smul {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (a : ℝ) (hvh : v h ≠ 0) :
    deleteProjectionF h v (x + a • v) = deleteProjectionF h v x := by
  funext i
  simp only [deleteProjectionF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

lemma deleteProjectionF_self {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hvh : v h ≠ 0) :
    deleteProjectionF h v v = 0 := by
  funext i
  simp [deleteProjectionF, hvh]

lemma abs_apply_le_normF {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have hi := (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp (le_refl ‖x‖) i
  simpa only [Real.norm_eq_abs] using hi

/-- Rounding a lift along a shortest vector costs at most half that vector. -/
lemma reducedLift_apply_leF {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (t a : ℝ)
    (hh : |v h| = ‖v‖) (hvh : v h ≠ 0)
    (ha : |x h / v h + a| ≤ (1 : ℝ) / 2)
    (hx : ‖deleteProjectionF h v x‖ ≤ t) :
    ‖x + a • v‖ ≤ t + ‖v‖ / 2 := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hx
  rw [pi_norm_le_iff_of_nonneg (add_nonneg ht (by positivity))]
  rw [h.forall_iff_succAbove]
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have heq : x h + a * v h = (x h / v h + a) * v h := by field_simp
    rw [heq, abs_mul, hh]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg v)).trans (by linarith)
  · intro j
    have hproj : |deleteProjectionF h v x j| ≤ t := by
      simpa only [Real.norm_eq_abs] using
        (abs_apply_le_normF (deleteProjectionF h v x) j).trans hx
    have hv : |v (h.succAbove j)| ≤ ‖v‖ := abs_apply_le_normF v _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have hdecomp : x (h.succAbove j) + a * v (h.succAbove j) =
        deleteProjectionF h v x j +
          (x h / v h + a) * v (h.succAbove j) := by
      rw [deleteProjectionF]
      ring
    rw [hdecomp]
    calc
      |deleteProjectionF h v x j + (x h / v h + a) * v (h.succAbove j)| ≤
          |deleteProjectionF h v x j| +
            |x h / v h + a| * |v (h.succAbove j)| := by
              simpa only [abs_mul] using
                abs_add_le (deleteProjectionF h v x j)
                  ((x h / v h + a) * v (h.succAbove j))
      _ ≤ t + ((1 : ℝ) / 2) * ‖v‖ := by
        exact add_le_add hproj (mul_le_mul ha hv (abs_nonneg _) (by norm_num))
      _ = t + ‖v‖ / 2 := by ring

/-- Column shear killing the pivot row in all tail columns. -/
noncomputable def tailShearF {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if j = 0 then (if i = 0 then 1 else 0)
    else if i = 0 then -(B h j / B h 0)
    else if i = j then 1 else 0

lemma tailShearF_det {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (tailShearF h B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i hi
    by_cases hi0 : i = 0
    · subst i; simp [tailShearF]
    · simp [tailShearF, hi0]
  · intro i j hji
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      exact (not_lt_of_ge (Fin.zero_le j)) hji
    have hij : i ≠ j := ne_of_gt hji
    simp [tailShearF, hi0, hij]

/-- Projected tail matrix in the quotient by the pivot vector. -/
noncomputable def projectedTailF {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => B (h.succAbove i) j.succ -
    (B h j.succ / B h 0) * B (h.succAbove i) 0

lemma mul_tailShearF_apply_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    (B * tailShearF h B) i 0 = B i 0 := by
  simp [Matrix.mul_apply, tailShearF]

lemma mul_tailShearF_apply_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (j : Fin n) :
    (B * tailShearF h B) i j.succ =
      B i j.succ - (B h j.succ / B h 0) * B i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailShearF]
  ring

lemma mul_tailShearF_pivot_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (j : Fin n) : (B * tailShearF h B) h j.succ = 0 := by
  rw [mul_tailShearF_apply_succ]
  field_simp
  ring

lemma abs_det_eq_abs_pivot_mul_projectedTailF {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B h 0 ≠ 0) :
    |B.det| = |B h 0| * |(projectedTailF h B).det| := by
  have hdetC : (B * tailShearF h B).det = B.det := by
    simp [Matrix.det_mul, tailShearF_det]
  have hminor :
      (B * tailShearF h B).submatrix h.succAbove (Fin.succAbove 0) =
        projectedTailF h B := by
    ext i j
    simp [projectedTailF, mul_tailShearF_apply_succ]
  have hLaplace := Matrix.det_succ_row (B * tailShearF h B) h
  rw [Fin.sum_univ_succ] at hLaplace
  rw [mul_tailShearF_apply_zero] at hLaplace
  simp_rw [mul_tailShearF_pivot_succ h B hB] at hLaplace
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hLaplace
  rw [hdetC, hminor] at hLaplace
  rw [hLaplace, abs_mul, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]

end

end Jsp000216

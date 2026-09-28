import Jsp000216.MinkowskiBoxLift

open scoped BigOperators Matrix
open Module Submodule Set

namespace Jsp000216

noncomputable section

/-- A nonsingular full integer lattice in `ℝ^n` contains `n` real-linearly
independent lattice vectors whose sup-norm product is controlled by the
box-Minkowski dimension constant times the lattice determinant. -/
theorem exists_minkowskiBox_familyF :
    ∀ n (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0),
      ∃ v : Fin n → (Fin n → ℝ),
        (∀ i, v i ∈ Submodule.span ℤ (Set.range (matrixBasisF D hD))) ∧
        LinearIndependent ℝ v ∧
        (∏ i, ‖v i‖) ≤ minkowskiBoxConstantF n * |D.det| := by
  intro n
  induction n with
  | zero =>
      intro D hD
      refine ⟨fun i => Fin.elim0 i, ?_, linearIndependent_empty_type, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [minkowskiBoxConstantF]
  | succ n ih =>
      intro D hD
      obtain ⟨B, h, hBdet, habs, hcolmem, hcol0, hshortD, hh, hB0, hspanRaw⟩ :=
        exists_shortest_first_column_basisF D hD
      have hspanB :
          Submodule.span ℤ (Set.range (matrixBasisF B hBdet)) ≤
            Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        rw [matrixBasisF_apply]
        exact hspanRaw (Submodule.subset_span (Set.mem_range_self j))
      have hshortB : ∀ x ∈ Submodule.span ℤ (Set.range (matrixBasisF B hBdet)),
          x ≠ 0 → ‖fun i => B i 0‖ ≤ ‖x‖ := by
        intro x hx hx0
        exact hshortD x (hspanB hx) hx0
      have hPdet : (projectedTailF h B).det ≠ 0 :=
        projectedTailF_det_ne_zero h B hBdet hB0
      obtain ⟨w, hwmem, hwli, hwprod⟩ := ih (projectedTailF h B) hPdet
      have hex : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec (projectedTailF h B) (intCastVecF z) = w j := by
        intro j
        exact (mem_span_matrixBasisF_iff_exists_intCastVecF
          (projectedTailF h B) hPdet (w j)).mp (hwmem j)
      choose z hz using hex
      have hz0 : ∀ j, z j ≠ 0 := by
        intro j hzj
        apply hwli.ne_zero j
        rw [← hz j]
        funext i
        simp [hzj, intCastVecF, Matrix.mulVec]
      let v : Fin (n + 1) → (Fin (n + 1) → ℝ) :=
        Fin.cons (fun i => B i 0) (fun j => reducedTailLiftF h B (z j))
      have hvmem : ∀ i, v i ∈
          Submodule.span ℤ (Set.range (matrixBasisF D hD)) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [v] using hcolmem
        · have hlift := reducedTailLiftF_mem_span h B hBdet (z j)
          have := hspanB hlift
          simpa [v] using this
      have hprojLI : LinearIndependent ℝ (fun j =>
          Matrix.mulVec (projectedTailF h B) (intCastVecF (z j))) := by
        have heq : (fun j => Matrix.mulVec (projectedTailF h B) (intCastVecF (z j))) = w := by
          funext j
          exact hz j
        rw [heq]
        exact hwli
      have hvli : LinearIndependent ℝ v := by
        dsimp [v]
        exact linearIndependent_finCons_reducedTailLiftF h B hB0 z hprojLI
      have htail := prod_norm_reducedTailLiftF_le_two_pow
        h B hBdet hB0 hh hshortB z hz0
      have htail' :
          (∏ j, ‖reducedTailLiftF h B (z j)‖) ≤
            (2 : ℝ) ^ n * ∏ j, ‖w j‖ := by
        calc
          (∏ j, ‖reducedTailLiftF h B (z j)‖) ≤
              (2 : ℝ) ^ n * ∏ j,
                ‖Matrix.mulVec (projectedTailF h B) (intCastVecF (z j))‖ := htail
          _ = (2 : ℝ) ^ n * ∏ j, ‖w j‖ := by
            congr 1
            apply Finset.prod_congr rfl
            intro j hj
            rw [hz j]
      have hdetProd :
          ‖fun i => B i 0‖ * |(projectedTailF h B).det| = |D.det| := by
        rw [← hh, ← abs_det_eq_abs_pivot_mul_projectedTailF h B hB0, habs]
      refine ⟨v, hvmem, hvli, ?_⟩
      calc
        (∏ i, ‖v i‖) =
            ‖fun i => B i 0‖ * ∏ j, ‖reducedTailLiftF h B (z j)‖ := by
              simp [v, Fin.prod_univ_succ]
        _ ≤ ‖fun i => B i 0‖ * ((2 : ℝ) ^ n * ∏ j, ‖w j‖) :=
          mul_le_mul_of_nonneg_left htail' (norm_nonneg _)
        _ ≤ ‖fun i => B i 0‖ *
            ((2 : ℝ) ^ n * (minkowskiBoxConstantF n * |(projectedTailF h B).det|)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left hwprod
          exact pow_nonneg (by norm_num) n
        _ = minkowskiBoxConstantF (n + 1) * |D.det| := by
          rw [minkowskiBoxConstantF_succ]
          calc
            ‖fun i => B i 0‖ *
                ((2 : ℝ) ^ n * (minkowskiBoxConstantF n * |(projectedTailF h B).det|)) =
              (2 : ℝ) ^ n * minkowskiBoxConstantF n *
                (‖fun i => B i 0‖ * |(projectedTailF h B).det|) := by ring
            _ = (2 : ℝ) ^ n * minkowskiBoxConstantF n * |D.det| := by rw [hdetProd]
            _ = ((2 : ℝ) ^ n * minkowskiBoxConstantF n) * |D.det| := by ring

end

end Jsp000216

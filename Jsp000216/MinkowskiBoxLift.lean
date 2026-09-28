import Jsp000216.MinkowskiBoxInduction

open scoped BigOperators Matrix
open Module Submodule Set

namespace Jsp000216

noncomputable section

/-- A linearly independent projected family remains linearly independent after
reduced lifting, and adjoining the first pivot vector preserves independence. -/
theorem linearIndependent_finCons_reducedTailLiftF {n : ℕ}
    (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB0 : B h 0 ≠ 0)
    (z : Fin n → (Fin n → ℤ))
    (hproj : LinearIndependent ℝ (fun j =>
      Matrix.mulVec (projectedTailF h B) (intCastVecF (z j)))) :
    LinearIndependent ℝ
      (Fin.cons (fun i => B i 0) (fun j => reducedTailLiftF h B (z j))) := by
  let v0 : Fin (n + 1) → ℝ := fun i => B i 0
  let u : Fin n → (Fin (n + 1) → ℝ) := fun j => reducedTailLiftF h B (z j)
  let f : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    deleteProjectionLinearF h v0
  have himage : f ∘ u = fun j =>
      Matrix.mulVec (projectedTailF h B) (intCastVecF (z j)) := by
    funext j
    change deleteProjectionF h v0 (reducedTailLiftF h B (z j)) = _
    dsimp [v0]
    exact deleteProjectionF_reducedTailLiftF h B hB0 (z j)
  have htailImage : LinearIndependent ℝ (f ∘ u) := by
    rw [himage]
    exact hproj
  have htail : LinearIndependent ℝ u :=
    LinearIndependent.of_comp f htailImage
  have hdisj : Disjoint (Submodule.span ℝ (Set.range u)) (LinearMap.ker f) :=
    Submodule.range_ker_disjoint htailImage
  have hvker : v0 ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    change deleteProjectionF h v0 v0 = 0
    dsimp [v0]
    exact deleteProjectionF_self h (fun i => B i 0) hB0
  have hv0 : v0 ≠ 0 := by
    intro hz
    apply hB0
    have hh := congrFun hz h
    simpa [v0] using hh
  have hvnot : v0 ∉ Submodule.span ℝ (Set.range u) := by
    intro hvspan
    exact hv0 ((Submodule.disjoint_def.mp hdisj) v0 hvspan hvker)
  change LinearIndependent ℝ (Fin.cons v0 u)
  exact linearIndependent_finCons.mpr ⟨htail, hvnot⟩

/-- Multiplying the pointwise factor-two lift bound gives a total `2^n`
loss for an `n`-dimensional projected family. -/
lemma prod_norm_reducedTailLiftF_le_two_pow {n : ℕ}
    (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB0 : B h 0 ≠ 0)
    (hh : |B h 0| = ‖fun i => B i 0‖)
    (hshort : ∀ x ∈ Submodule.span ℤ (Set.range (matrixBasisF B hdet)),
      x ≠ 0 → ‖fun i => B i 0‖ ≤ ‖x‖)
    (z : Fin n → (Fin n → ℤ)) (hz : ∀ j, z j ≠ 0) :
    (∏ j, ‖reducedTailLiftF h B (z j)‖) ≤
      (2 : ℝ) ^ n *
        ∏ j, ‖Matrix.mulVec (projectedTailF h B) (intCastVecF (z j))‖ := by
  calc
    (∏ j, ‖reducedTailLiftF h B (z j)‖) ≤
        ∏ j, (2 : ℝ) *
          ‖Matrix.mulVec (projectedTailF h B) (intCastVecF (z j))‖ := by
      refine Finset.prod_le_prod₀ (fun j hj => norm_nonneg _) (fun j hj => ?_)
      exact norm_reducedTailLiftF_le_two_mul_projected
        h B hdet hB0 hh hshort (hz j)
    _ = (2 : ℝ) ^ n *
        ∏ j, ‖Matrix.mulVec (projectedTailF h B) (intCastVecF (z j))‖ := by
      rw [Finset.prod_mul_distrib]
      simp

end

end Jsp000216

import Jsp000216.MinkowskiBoxTheorem
import Jsp000216.BohrCertificate

open scoped BigOperators Matrix Pointwise

namespace Jsp000216

noncomputable section

/-- Realifying an integral Bohr lattice point agrees exactly with multiplying
the real Bohr lattice matrix by the realified integral coordinate vector. -/
lemma bohrLatticePointF_cast_real_eq_mulVec {N : ℕ}
    (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) :
    (fun i => (bohrLatticePointF Gamma z i : ℝ)) =
      Matrix.mulVec (bohrLatticeMatrixF Gamma) (intCastVecF z) := by
  funext i
  simp only [bohrLatticePointF, bohrLatticeMatrixF, Matrix.mulVec, dotProduct,
    intCastVecF, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
  rfl

/-- The box-Minkowski family for the Bohr congruence lattice gives exactly the
certificate consumed by the progression extraction layer. -/
theorem bohrLatticeCertificateF_of_minkowski {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (R : ℝ) (hR : 0 < R) :
    BohrLatticeCertificateF Gamma R
      (minkowskiBoxConstantF (Gamma.card + 1) * (N : ℝ) ^ Gamma.card /
        R ^ (Gamma.card + 1)) := by
  let D : Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℝ :=
    bohrLatticeMatrixF Gamma
  have hD : D.det ≠ 0 := by
    dsimp [D]
    exact det_bohrLatticeMatrixF_ne_zero Gamma hN
  obtain ⟨v, hvmem, hvli, hvprod⟩ :=
    exists_minkowskiBox_familyF (Gamma.card + 1) D hD
  have hex : ∀ i, ∃ z : Fin (Gamma.card + 1) → ℤ,
      Matrix.mulVec D (intCastVecF z) = v i := by
    intro i
    exact (mem_span_matrixBasisF_iff_exists_intCastVecF D hD (v i)).mp (hvmem i)
  choose coeff hcoeff using hex
  have hpoint (i : Fin (Gamma.card + 1)) :
      (fun j => (bohrLatticePointF Gamma (coeff i) j : ℝ)) = v i := by
    calc
      (fun j => (bohrLatticePointF Gamma (coeff i) j : ℝ)) =
          Matrix.mulVec (bohrLatticeMatrixF Gamma) (intCastVecF (coeff i)) :=
        bohrLatticePointF_cast_real_eq_mulVec Gamma (coeff i)
      _ = Matrix.mulVec D (intCastVecF (coeff i)) := by rfl
      _ = v i := hcoeff i
  let scale : Fin (Gamma.card + 1) → ℝ := fun i => ‖v i‖ / R
  refine
    { coeff := coeff
      scale := scale
      scale_pos := ?_
      independent := ?_
      point_bound := ?_
      product_le := ?_ }
  · intro i
    dsimp [scale]
    exact div_pos (norm_pos_iff.mpr (hvli.ne_zero i)) hR
  · have heq :
        (fun i => fun j => (bohrLatticePointF Gamma (coeff i) j : ℝ)) = v := by
      funext i
      exact hpoint i
    rw [heq]
    exact hvli
  · intro i j
    have hij := congrFun (hpoint i) j
    rw [hij]
    dsimp [scale]
    calc
      |v i j| ≤ ‖v i‖ := abs_apply_le_normF (v i) j
      _ = (‖v i‖ / R) * R := by
        exact (div_mul_cancel₀ _ hR.ne').symm
  · have hvprodN :
        (∏ i, ‖v i‖) ≤
          minkowskiBoxConstantF (Gamma.card + 1) * (N : ℝ) ^ Gamma.card := by
      calc
        (∏ i, ‖v i‖) ≤
            minkowskiBoxConstantF (Gamma.card + 1) * |D.det| := hvprod
        _ = minkowskiBoxConstantF (Gamma.card + 1) * (N : ℝ) ^ Gamma.card := by
          dsimp [D]
          rw [det_bohrLatticeMatrixF Gamma hN]
          rw [abs_of_nonneg (pow_nonneg (by positivity) Gamma.card)]
    dsimp [scale]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (div_le_div_iff_of_pos_right (pow_pos hR (Gamma.card + 1))).2 hvprodN

end

end Jsp000216

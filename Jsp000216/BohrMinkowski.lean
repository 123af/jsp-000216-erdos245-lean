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

end

end Jsp000216

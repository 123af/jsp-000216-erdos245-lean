import Jsp000216.ChainCore

open scoped BigOperators

namespace Jsp000216

/-- A columnwise bound on an integer square matrix gives a Leibniz-style
factorial times box-volume bound on the absolute determinant. -/
theorem natAbs_det_le_factorial_mul_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (B : ι → ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ B j) :
    M.det.natAbs ≤ (Fintype.card ι).factorial * ∏ j, B j := by
  have hNatAbsProd (f : ι → ℤ) :
      (∏ i, f i).natAbs = ∏ i, (f i).natAbs := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => simp [hx, Int.natAbs_mul, ih]
  rw [Matrix.det_apply']
  calc
    (∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i)).natAbs
        ≤ ∑ σ : Equiv.Perm ι,
          (((Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i).natAbs) :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, B i := by
      apply Finset.sum_le_sum
      intro σ _hσ
      rw [Int.natAbs_mul, hNatAbsProd (fun i => M (σ i) i)]
      have hsign : ((Equiv.Perm.sign σ : ℤ)).natAbs = 1 := by simp
      rw [hsign, one_mul]
      exact Finset.prod_le_prod' fun i _hi => hM (σ i) i
    _ = (Fintype.card ι).factorial * ∏ i, B i := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
      rfl

end Jsp000216

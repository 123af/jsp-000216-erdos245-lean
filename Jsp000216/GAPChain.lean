import Jsp000216.GAPBasic
import Jsp000216.ReducedChain

open scoped BigOperators

namespace Jsp000216

namespace GAPF

/-- Homogeneous integer coordinates for an affine GAP parameter. -/
def homParam (Q : GAPF) (x : Q.Param) : Fin (Q.rank + 1) → ℤ :=
  Fin.cases 1 fun i => (x i : ℕ)

@[simp] lemma homParam_zero (Q : GAPF) (x : Q.Param) :
    homParam Q x 0 = 1 := rfl

@[simp] lemma homParam_succ (Q : GAPF) (x : Q.Param) (i : Fin Q.rank) :
    homParam Q x i.succ = (x i : ℕ) := rfl

/-- Rational linear extension of affine GAP evaluation in homogeneous
coordinates. -/
def evalLinear (Q : GAPF) :
    (Fin (Q.rank + 1) → ℚ) →ₗ[ℚ] ℚ where
  toFun v := (Q.base : ℚ) * v 0 +
    ∑ i : Fin Q.rank, (Q.step i : ℚ) * v i.succ
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add,
      Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _hi
      ring

@[simp] lemma evalLinear_homParam (Q : GAPF) (x : Q.Param) :
    Q.evalLinear (castIntVec (Q.homParam x)) = (Q.eval x : ℚ) := by
  simp only [evalLinear, LinearMap.coe_mk, AddHom.coe_mk, homParam_zero,
    homParam_succ, castIntVec_apply, eval, Int.cast_add, Int.cast_sum,
    Int.cast_mul, Int.cast_natCast, Int.cast_one, mul_one]
  apply congrArg ((Q.base : ℚ) + ·)
  apply Finset.sum_congr rfl
  intro i _hi
  ring

lemma evalLinear_chain_zero
    (Q : GAPF) (x : ℕ → Q.Param) (n : ℕ) :
    Q.evalLinear
        (castIntVec
          (doublingChainGenInt (fun k => Q.homParam (x k)) n 0)) =
      (Q.eval (x 0) : ℚ) := by
  rw [castIntVec_doublingChainGenInt]
  simp [doublingChainGen]

lemma evalLinear_chain_succ
    (Q : GAPF) (x : ℕ → Q.Param) (n : ℕ) (j : Fin n) :
    Q.evalLinear
        (castIntVec
          (doublingChainGenInt (fun k => Q.homParam (x k)) n j.succ)) =
      (Q.eval (x (j + 1)) : ℚ) - 2 * (Q.eval (x j) : ℚ) := by
  rw [castIntVec_doublingChainGenInt]
  simp [doublingChainGen]

/-- Coordinatewise box bound for a homogeneous parameter. -/
lemma natAbs_homParam_le (Q : GAPF) (x : Q.Param)
    (j : Fin (Q.rank + 1)) :
    (Q.homParam x j).natAbs ≤
      Fin.cases 1 (fun i => 3 * (Q.length i + 1)) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp only [homParam_succ, Fin.cases_succ, Int.natAbs_natCast]
    have hx : (x i : ℕ) ≤ Q.length i := Q.param_le_length x i
    omega

/-- The successive doubling deviations stay in a box enlarged by a factor
three in every genuine GAP coordinate. -/
lemma natAbs_chain_homParam_le
    (Q : GAPF) (x : ℕ → Q.Param) (n : ℕ)
    (i : Fin (n + 1)) (j : Fin (Q.rank + 1)) :
    (doublingChainGenInt (fun k => Q.homParam (x k)) n i j).natAbs ≤
      Fin.cases 1 (fun q => 3 * (Q.length q + 1)) j := by
  refine Fin.cases ?_ (fun r => ?_) i
  · exact Q.natAbs_homParam_le (x 0) j
  · refine Fin.cases ?_ (fun q => ?_) j
    · simp [doublingChainGenInt, homParam]
    · simp only [doublingChainGenInt]
      rw [Fin.cases_succ]
      change
        (((x (r + 1) q : ℕ) : ℤ) -
          2 * ((x r q : ℕ) : ℤ)).natAbs ≤
            3 * (Q.length q + 1)
      have hx1 : (x (r + 1) q : ℕ) ≤ Q.length q :=
        Q.param_le_length (x (r + 1)) q
      have hx0 : (x r q : ℕ) ≤ Q.length q :=
        Q.param_le_length (x r) q
      have habs :
          (((x (r + 1) q : ℕ) : ℤ) -
            2 * ((x r q : ℕ) : ℤ)).natAbs ≤
            (x (r + 1) q : ℕ) + 2 * (x r q : ℕ) := by
        calc
          _ ≤ (((x (r + 1) q : ℕ) : ℤ)).natAbs +
              (2 * ((x r q : ℕ) : ℤ)).natAbs := Int.natAbs_sub_le _ _
          _ = (x (r + 1) q : ℕ) + 2 * (x r q : ℕ) := by
            rw [Int.natAbs_mul]
            simp
      exact habs.trans (by omega)

lemma prod_chain_bounds (Q : GAPF) :
    (∏ j : Fin (Q.rank + 1),
        Fin.cases 1 (fun i => 3 * (Q.length i + 1)) j) =
      3 ^ Q.rank * Q.boxCard := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, one_mul, boxCard,
    Finset.prod_mul_distrib]
  simp

/-- If a finite string of nonnegative elements represented in one GAP has no
factor-two gap, its endpoint is at most a fixed rank/box-volume multiple of
the initial value. -/
lemma no_gap_chain_diameter_bound
    (Q : GAPF) (x : ℕ → Q.Param) (n : ℕ)
    (hpos : ∀ i ≤ n, 0 ≤ Q.eval (x i))
    (hnogap : ∀ i < n, Q.eval (x (i + 1)) ≤ 2 * Q.eval (x i)) :
    (Q.eval (x n) : ℚ) ≤
      (((Q.rank + 1).factorial *
          (3 ^ Q.rank * Q.boxCard) : ℕ) : ℚ) *
        (Q.eval (x 0) : ℚ) := by
  let u : ℕ → Fin (Q.rank + 1) → ℤ := fun k => Q.homParam (x k)
  let B : Fin (Q.rank + 1) → ℕ :=
    Fin.cases 1 fun i => 3 * (Q.length i + 1)
  have hB : ∀ j, 1 ≤ B j := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [B]
    · simp only [B, Fin.cases_succ]
      omega
  obtain ⟨b, hb, hrel, hb0, hb0le⟩ :=
    exists_bounded_reduced_doublingChain_coefficients u n 0
      (by intro i; simp [u, homParam]) B hB
      (by intro i j; exact Q.natAbs_chain_homParam_le x n i j)
      (by intro j; exact Q.natAbs_homParam_le (x n) j)
  have hevalrel :
      (Q.eval (x n) : ℚ) =
        ∑ i, b i *
          Q.evalLinear
            (castIntVec (doublingChainGenInt u n i)) := by
    have h := congrArg Q.evalLinear hrel
    simpa [u] using h
  have hterm (i : Fin (n + 1)) :
      b i * Q.evalLinear (castIntVec (doublingChainGenInt u n i)) ≤
        if i = 0 then b 0 * (Q.eval (x 0) : ℚ) else 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [u, Q.evalLinear_chain_zero]
    · have hj : (j : ℕ) < n := j.isLt
      have hgap :
          (Q.eval (x (j + 1)) : ℚ) -
              2 * (Q.eval (x j) : ℚ) ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr (hnogap j hj)
      have hmul := mul_nonpos_of_nonneg_of_nonpos (hb j.succ) hgap
      simpa [u, Q.evalLinear_chain_succ, Fin.succ_ne_zero] using hmul
  have hsum :
      (∑ i, b i * Q.evalLinear
          (castIntVec (doublingChainGenInt u n i))) ≤
        b 0 * (Q.eval (x 0) : ℚ) := by
    calc
      _ ≤ ∑ i, if i = 0 then b 0 * (Q.eval (x 0) : ℚ) else 0 :=
        Finset.sum_le_sum fun i _hi => hterm i
      _ = b 0 * (Q.eval (x 0) : ℚ) := by simp
  rw [← hevalrel] at hsum
  have hx0 : (0 : ℚ) ≤ (Q.eval (x 0) : ℚ) := by
    exact_mod_cast hpos 0 (Nat.zero_le n)
  calc
    (Q.eval (x n) : ℚ) ≤ b 0 * (Q.eval (x 0) : ℚ) := hsum
    _ ≤ (((Q.rank + 1).factorial * ∏ j, B j : ℕ) : ℚ) *
        (Q.eval (x 0) : ℚ) := mul_le_mul_of_nonneg_right hb0le hx0
    _ = (((Q.rank + 1).factorial *
          (3 ^ Q.rank * Q.boxCard) : ℕ) : ℚ) *
        (Q.eval (x 0) : ℚ) := by rw [Q.prod_chain_bounds]

end GAPF

end Jsp000216

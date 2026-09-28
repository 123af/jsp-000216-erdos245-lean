import Jsp000216.ConicReduction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis

open scoped BigOperators

namespace Jsp000216

/-- Cramer's-rule coefficient bound for a linearly independent family of
integer vectors.  The family is extended to a rational basis using standard
basis vectors, so all rows remain integral and preserve the same columnwise
bounds. -/
theorem coefficient_le_of_integral_independent
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Fin d → ℤ) (v : Fin d → ℤ) (a : ι → ℚ) (i₀ : ι)
    (hli : LinearIndependent ℚ (fun i => castIntVec (w i)))
    (hrel : castIntVec v = ∑ i, a i • castIntVec (w i))
    (B : Fin d → ℕ) (hB : ∀ j, 1 ≤ B j)
    (hw : ∀ i j, (w i j).natAbs ≤ B j)
    (hv : ∀ j, (v j).natAbs ≤ B j) :
    a i₀ ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by
  classical
  let f : ι → (Fin d → ℚ) := fun i => castIntVec (w i)
  let s : Set (Fin d → ℚ) := Set.range f
  let stdZ : Fin d → Fin d → ℤ := fun j => Pi.single j 1
  let stdQ : Fin d → Fin d → ℚ := fun j => castIntVec (stdZ j)
  let t : Set (Fin d → ℚ) := s ∪ Set.range stdQ
  have hs : LinearIndepOn ℚ id s := by
    exact hli.linearIndepOn_id
  have hst : s ⊆ t := Set.subset_union_left
  have ht : (⊤ : Submodule ℚ (Fin d → ℚ)) ≤ Submodule.span ℚ t := by
    rw [← (Pi.basisFun ℚ (Fin d)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    apply Set.mem_union_right
    refine ⟨j, ?_⟩
    ext k
    by_cases hjk : j = k
    · subst k
      simp [stdQ, stdZ, Pi.basisFun_apply]
    · simp [stdQ, stdZ, Pi.basisFun_apply, hjk]
  let basis : Module.Basis (hs.extend hst) ℚ (Fin d → ℚ) :=
    Module.Basis.extendLe hs hst ht
  let I := hs.extend hst
  let : Fintype I := Fintype.ofFinite I
  have hIntegral (i : I) :
      ∃ z : Fin d → ℤ, castIntVec z = basis i := by
    have hi : basis i ∈ t := by
      apply Module.Basis.extendLe_subset hs hst ht
      exact Set.mem_range_self i
    rcases hi with hi | hi
    · obtain ⟨j, hj⟩ := hi
      exact ⟨w j, by simpa [f, s] using hj⟩
    · obtain ⟨j, hj⟩ := hi
      exact ⟨stdZ j, by simpa [stdQ] using hj⟩
  choose bz hbz using hIntegral
  have hcard : Fintype.card I = d := by
    rw [← Module.finrank_eq_card_basis basis]
    simp
  let e : I ≃ Fin d := Fintype.equivOfCardEq (by simpa using hcard)
  let A : Matrix I I ℤ := fun i j => bz i (e j)
  let AQ : Matrix I I ℚ := fun i j => basis i (e j)
  have hAmap : A.map (Int.castRingHom ℚ) = AQ := by
    ext i j
    exact congrFun (hbz i) (e j)
  let E : (Fin d → ℚ) ≃ₗ[ℚ] (I → ℚ) :=
    LinearEquiv.piCongrLeft' ℚ (fun _ : Fin d => ℚ) e.symm
  have hAQli : LinearIndependent ℚ (fun i => AQ i) := by
    have hmap := basis.linearIndependent.map' E.toLinearMap (by simp [E])
    have heq : (fun i => AQ i) = E ∘ basis := by
      funext i j
      rfl
    rw [heq]
    exact hmap
  have hAdetQ : AQ.det ≠ 0 := by
    have hunitA : IsUnit AQ :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hAQli
    exact ((Matrix.isUnit_iff_isUnit_det AQ).mp hunitA).ne_zero
  have hcast : (A.det : ℚ) = AQ.det :=
    (Int.cast_det A).trans (congrArg Matrix.det hAmap)
  have hAdet : A.det ≠ 0 := by
    intro hzero
    apply hAdetQ
    rw [← hcast, hzero]
    simp
  let ii : ι → I := fun i =>
    ⟨f i, hs.subset_extend hst (Set.mem_range_self i)⟩
  let ic : I := ii i₀
  have hbasis_ii (i : ι) : basis (ii i) = f i := by
    exact Module.Basis.extendLe_apply_self hs hst ht (ii i)
  have hii_injective : Function.Injective ii := by
    intro i j hij
    apply hli.injective
    have h := congrArg Subtype.val hij
    simpa [ii] using h
  have hrepr_w (i : ι) :
      basis.repr (castIntVec (w i)) ic = if i = i₀ then 1 else 0 := by
    rw [show castIntVec (w i) = basis (ii i) by
      simpa [f] using (hbasis_ii i).symm]
    rw [basis.repr_self_apply]
    by_cases hi : i = i₀
    · subst i
      simp [ic]
    · have hne : ii i ≠ ic := by
        simpa [ic] using fun h => hi (hii_injective h)
      simp [hne, hi]
  have hrepr : basis.repr (castIntVec v) ic = a i₀ := by
    calc
      basis.repr (castIntVec v) ic =
          basis.repr (∑ i, a i • castIntVec (w i)) ic := by rw [hrel]
      _ = ∑ i, a i * basis.repr (castIntVec (w i)) ic := by simp
      _ = a i₀ := by simp [hrepr_w]
  have hbzBound (i j : I) : (bz i (e j)).natAbs ≤ B (e j) := by
    have hi : basis i ∈ t := by
      apply Module.Basis.extendLe_subset hs hst ht
      exact Set.mem_range_self i
    rcases hi with hi | hi
    · obtain ⟨k, hk⟩ := hi
      have heq : bz i (e j) = w k (e j) := by
        have h := castIntVec_injective ((hbz i).trans hk.symm)
        exact congrFun h (e j)
      rw [heq]
      exact hw k (e j)
    · obtain ⟨k, hk⟩ := hi
      have heq : bz i (e j) = stdZ k (e j) := by
        have h := castIntVec_injective ((hbz i).trans hk.symm)
        exact congrFun h (e j)
      rw [heq]
      by_cases hkj : k = e j
      · subst k
        simpa [stdZ] using hB (e j)
      · simp [stdZ, hkj]
  let vRow : I → ℤ := fun j => v (e j)
  let Av : Matrix I I ℤ := A.updateRow ic vRow
  have hAvBound (i j : I) : (Av i j).natAbs ≤ B (e j) := by
    by_cases hi : i = ic
    · subst i
      simpa [Av, vRow, Matrix.updateRow_self] using hv (e j)
    · change ((A.updateRow ic vRow) i j).natAbs ≤ B (e j)
      rw [Matrix.updateRow_apply, if_neg hi]
      exact hbzBound i j
  have hAvdet : Av.det.natAbs ≤ d.factorial * ∏ j, B j := by
    have h := natAbs_det_le_factorial_mul_prod Av (fun j => B (e j)) hAvBound
    rw [hcard] at h
    simpa only [Equiv.prod_comp e] using h
  have hvrow : (fun j : I => (v (e j) : ℚ)) =
      ∑ i, (basis.repr (castIntVec v) i) • AQ i := by
    funext j
    have hsum := congrFun (basis.sum_repr (castIntVec v)) (e j)
    simpa [AQ] using hsum.symm
  have hAvmap : Av.map (Int.castRingHom ℚ) =
      AQ.updateRow ic (fun j => (v (e j) : ℚ)) := by
    ext i j
    by_cases hi : i = ic
    · subst i
      simp [Av, vRow, Matrix.updateRow_self]
    · change ((A.updateRow ic vRow i j : ℤ) : ℚ) =
          AQ.updateRow ic (fun j => (v (e j) : ℚ)) i j
      rw [Matrix.updateRow_apply, Matrix.updateRow_apply, if_neg hi, if_neg hi]
      change (bz i (e j) : ℚ) = basis i (e j)
      exact congrFun (hbz i) (e j)
  have hdetrel : (Av.det : ℚ) = a i₀ * (A.det : ℚ) := by
    calc
      (Av.det : ℚ) = (Av.map (Int.castRingHom ℚ)).det := Int.cast_det Av
      _ = (AQ.updateRow ic (fun j => (v (e j) : ℚ))).det := by rw [hAvmap]
      _ = (AQ.updateRow ic
          (∑ i, (basis.repr (castIntVec v) i) • AQ i)).det := by rw [hvrow]
      _ = basis.repr (castIntVec v) ic * AQ.det := by
        simpa only [smul_eq_mul] using
          Matrix.det_updateRow_sum AQ ic (fun i => basis.repr (castIntVec v) i)
      _ = a i₀ * (A.det : ℚ) := by
        rw [hrepr, ← hcast]
  have habs : |a i₀| * (A.det.natAbs : ℚ) = (Av.det.natAbs : ℚ) := by
    have h := congrArg abs hdetrel
    simpa [abs_mul, mul_comm] using h.symm
  have hdetOne : 1 ≤ A.det.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hAdet)
  calc
    a i₀ ≤ |a i₀| := le_abs_self _
    _ ≤ |a i₀| * (A.det.natAbs : ℚ) := by
      have h : (1 : ℚ) ≤ A.det.natAbs := by exact_mod_cast hdetOne
      nlinarith [abs_nonneg (a i₀)]
    _ = (Av.det.natAbs : ℚ) := habs
    _ ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by exact_mod_cast hAvdet

end Jsp000216

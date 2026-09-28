import Jsp000216.BohrCertificate

open scoped BigOperators Pointwise

namespace Jsp000216

noncomputable section

lemma int_eq_zero_of_cast_zmod_eq_zero_of_abs_ltF {N : ℕ} [NeZero N]
    {t : ℤ} (ht0 : (t : ZMod N) = 0) (htN : |(t : ℝ)| < N) : t = 0 := by
  have hdvd : (N : ℤ) ∣ t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd t N).mp ht0
  have habs : (t.natAbs : ℝ) = |(t : ℝ)| := by
    calc
      (t.natAbs : ℝ) = (((t.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|t| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(t : ℝ)| := Int.cast_abs
  have hnat : t.natAbs < N := by
    exact_mod_cast (habs.trans_lt htN)
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  simpa using hnat

namespace BohrLatticeCertificateF

variable {N : ℕ} {Gamma : Finset (ZMod N)} {R bound : ℝ}

/-- A certificate whose box is narrow compared with the modulus yields a
proper cyclic GAP. -/
theorem progression_proper [NeZero N]
    (C : BohrLatticeCertificateF Gamma R bound)
    (hN : 1 < N) (hR : 0 < R) (hsmall : R < 2 * N) :
    C.progression.Proper := by
  intro x y hxy
  let u : Fin (Gamma.card + 1) → ℤ :=
    fun i => C.progression.coeff x i - C.progression.coeff y i
  let v := C.combination u
  have hu (i : Fin (Gamma.card + 1)) :
      |u i| ≤ (2 * C.radius i : ℕ) := by
    have hx := C.progression.coeff_abs_le x i
    have hy := C.progression.coeff_abs_le y i
    rw [abs_le] at hx hy ⊢
    dsimp only [u]
    constructor <;> omega
  have hv0cast : (v 0 : ZMod N) = 0 := by
    have hx := C.eval_progression x
    have hy := C.eval_progression y
    have hvsub : (v 0 : ZMod N) =
        C.progression.eval x - C.progression.eval y := by
      rw [hx, hy]
      simp only [v, u, combination, Int.cast_sum, Int.cast_mul, Int.cast_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hvsub, hxy, sub_self]
  have hvcast (j : Fin (Gamma.card + 1)) : (v j : ZMod N) = 0 := by
    rw [C.combination_cast_coordinate hN u j, hv0cast, zero_mul]
  have hvabs (j : Fin (Gamma.card + 1)) : |(v j : ℝ)| ≤ R / 2 := by
    convert C.abs_combination_le hR 2 u hu j using 1 <;> norm_num <;> ring
  have hvzero : v = 0 := by
    funext j
    apply int_eq_zero_of_cast_zmod_eq_zero_of_abs_ltF (hvcast j)
    exact (hvabs j).trans_lt (by linarith)
  have hsum : ∑ i, (u i : ℝ) •
      (fun j => (C.point i j : ℝ)) = 0 := by
    funext j
    have hj := congrFun hvzero j
    have hjR : (v j : ℝ) = 0 := by exact_mod_cast hj
    simpa [v, combination] using hjR
  have huR : ∀ i, (u i : ℝ) = 0 :=
    (Fintype.linearIndependent_iff.mp C.independent) _ hsum
  have hu0 : u = 0 := by
    funext i
    change u i = 0
    exact_mod_cast huR i
  funext i
  apply Fin.ext
  have hi0 : u i = 0 := by
    change u i = (0 : Fin (Gamma.card + 1) → ℤ) i
    exact congrFun hu0 i
  have hi : (x i : ℤ) = (y i : ℤ) := by
    dsimp only [u] at hi0
    simp only [CyclicGAPF.coeff] at hi0
    omega
  exact_mod_cast hi

/-- The progression cut out by a short certificate lies in the radius-1/2
Bohr set. -/
theorem progression_carrier_subset_bohr [NeZero N]
    (C : BohrLatticeCertificateF Gamma R bound)
    (hN : 1 < N) (hR : 0 < R) (hsmall : 4 * R ≤ N) :
    C.progression.carrier ⊆ cyclicBohrSetF Gamma (1 / 2) := by
  intro z hz
  obtain ⟨x, hx⟩ := C.progression.mem_carrier_iff.mp hz
  rw [← hx, mem_cyclicBohrSetF]
  intro k hk
  let i : Fin Gamma.card := Gamma.equivFin ⟨k, hk⟩
  let u : Fin (Gamma.card + 1) → ℤ := C.progression.coeff x
  let v := C.combination u
  have hu (j : Fin (Gamma.card + 1)) :
      |u j| ≤ (C.radius j : ℕ) := by
    exact CyclicGAPF.coeff_abs_le C.progression x j
  have heval : C.progression.eval x = (v 0 : ZMod N) := C.eval_progression x
  have hchar : indexedCyclicCharacterF Gamma i.succ = k := by
    change ((Gamma.equivFin.symm i : Gamma) : ZMod N) = k
    simp [i]
  have hvchar : (v i.succ : ZMod N) = C.progression.eval x * k := by
    rw [C.combination_cast_coordinate hN u i.succ, hchar, heval]
  rw [← hvchar]
  apply stdAddChar_intCast_closeF
  have hvabs : |(v i.succ : ℝ)| ≤ R / 4 := by
    simpa using C.abs_combination_le hR 1 u (by simpa using hu) i.succ
  have habs : (v i.succ).natAbs = |(v i.succ : ℝ)| := by
    calc
      ((v i.succ).natAbs : ℝ) =
          ((((v i.succ).natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|v i.succ| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(v i.succ : ℝ)| := Int.cast_abs
  have hreal : (16 : ℝ) * (v i.succ).natAbs ≤ N := by
    rw [habs]
    nlinarith
  exact_mod_cast hreal

lemma inv_scale_le_two_mul_radius_add_one
    (C : BohrLatticeCertificateF Gamma R bound)
    (i : Fin (Gamma.card + 1)) :
    (((4 * (Gamma.card + 1) : ℝ) * C.scale i)⁻¹) ≤
      2 * (C.radius i : ℝ) + 1 := by
  have hlt := Nat.lt_floor_add_one
    (((4 * (Gamma.card + 1) : ℝ) * C.scale i)⁻¹)
  change (((4 * (Gamma.card + 1) : ℝ) * C.scale i)⁻¹) <
    (C.radius i : ℝ) + 1 at hlt
  have hradius : 0 ≤ (C.radius i : ℝ) := by positivity
  linarith

/-- Quantitative carrier lower bound extracted only from the certificate's
product bound. -/
theorem progression_card_lower_bound
    (C : BohrLatticeCertificateF Gamma R bound) :
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) * bound)⁻¹) ≤
      (∏ i : Fin (Gamma.card + 1),
        (2 * (C.radius i : ℝ) + 1)) := by
  let c : ℝ := 4 * (Gamma.card + 1)
  have hc : 0 < c := by positivity
  have hscale (i : Fin (Gamma.card + 1)) : 0 < C.scale i := C.scale_pos i
  have hprodscale : 0 < ∏ i, C.scale i := Finset.prod_pos fun i _ => hscale i
  have hbound : 0 < bound := lt_of_lt_of_le hprodscale C.product_le
  have hmul :
      c ^ (Gamma.card + 1) * (∏ i, C.scale i) ≤
        c ^ (Gamma.card + 1) * bound :=
    mul_le_mul_of_nonneg_left C.product_le (pow_nonneg hc.le _)
  have hreciprocal : (c ^ (Gamma.card + 1) * bound)⁻¹ ≤
      (c ^ (Gamma.card + 1) * ∏ i, C.scale i)⁻¹ := by
    exact one_div_le_one_div_of_le
      (mul_pos (pow_pos hc _) hprodscale) hmul
  have hproduct :
      (c ^ (Gamma.card + 1) * ∏ i, C.scale i)⁻¹ ≤
        ∏ i : Fin (Gamma.card + 1), (2 * (C.radius i : ℝ) + 1) := by
    calc
      (c ^ (Gamma.card + 1) * ∏ i, C.scale i)⁻¹ =
          (∏ i : Fin (Gamma.card + 1), c * C.scale i)⁻¹ := by
            congr 1
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin (Gamma.card + 1), (c * C.scale i)⁻¹ := by
            rw [Finset.prod_inv_distrib]
      _ ≤ ∏ i : Fin (Gamma.card + 1), (2 * (C.radius i : ℝ) + 1) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact inv_nonneg.mpr (mul_nonneg hc.le (C.scale_pos i).le)
            · intro i hi
              simpa [c] using C.inv_scale_le_two_mul_radius_add_one i
  simpa [c] using hreciprocal.trans hproduct

/-- Once properness is known, the previous product lower bound is literally a
lower bound for the carrier cardinality. -/
theorem progression_carrier_card_lower_bound [NeZero N]
    (C : BohrLatticeCertificateF Gamma R bound)
    (hN : 1 < N) (hR : 0 < R) (hsmall : R < 2 * N) :
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) * bound)⁻¹) ≤
      (C.progression.carrier.card : ℝ) := by
  have hproper := C.progression_proper hN hR hsmall
  have hcard := C.progression.card_carrier_of_proper hproper
  calc
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) * bound)⁻¹) ≤
        ∏ i : Fin (Gamma.card + 1), (2 * (C.radius i : ℝ) + 1) :=
      C.progression_card_lower_bound
    _ = (C.progression.carrier.card : ℝ) := by
      rw [hcard]
      norm_cast

end BohrLatticeCertificateF

end

end Jsp000216

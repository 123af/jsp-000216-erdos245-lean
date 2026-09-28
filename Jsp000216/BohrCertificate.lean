import Jsp000216.BohrLattice
import Jsp000216.CyclicGAP

open scoped BigOperators Pointwise

namespace Jsp000216

noncomputable section

/-- The exact output needed from a box-version of Minkowski's second theorem.
The certificate stores independent integral points of the Bohr congruence
lattice, their individual scales, and a product bound on those scales. -/
structure BohrLatticeCertificateF {N : ℕ} (Gamma : Finset (ZMod N))
    (R bound : ℝ) where
  coeff : Fin (Gamma.card + 1) → Fin (Gamma.card + 1) → ℤ
  scale : Fin (Gamma.card + 1) → ℝ
  scale_pos : ∀ i, 0 < scale i
  independent : LinearIndependent ℝ (fun i =>
    fun j => (bohrLatticePointF Gamma (coeff i) j : ℝ))
  point_bound : ∀ i j,
    |(bohrLatticePointF Gamma (coeff i) j : ℝ)| ≤ scale i * R
  product_le : (∏ i, scale i) ≤ bound

namespace BohrLatticeCertificateF

variable {N : ℕ} {Gamma : Finset (ZMod N)} {R bound : ℝ}

/-- The integral lattice point represented by one certificate vector. -/
def point (C : BohrLatticeCertificateF Gamma R bound)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  bohrLatticePointF Gamma (C.coeff i)

lemma point_cast_coordinate [NeZero N]
    (C : BohrLatticeCertificateF Gamma R bound) (hN : 1 < N)
    (i j : Fin (Gamma.card + 1)) :
    (C.point i j : ZMod N) =
      (C.point i 0 : ZMod N) * indexedCyclicCharacterF Gamma j := by
  exact bohrLatticePointF_cast_coordinate Gamma (C.coeff i) hN j

/-- Coordinate radius used for the progression extracted from a certificate. -/
noncomputable def radius (C : BohrLatticeCertificateF Gamma R bound)
    (i : Fin (Gamma.card + 1)) : ℕ :=
  ⌊((4 * (Gamma.card + 1) : ℝ) * C.scale i)⁻¹⌋₊

lemma radius_mul_scale_le
    (C : BohrLatticeCertificateF Gamma R bound)
    (i : Fin (Gamma.card + 1)) :
    (C.radius i : ℝ) * C.scale i ≤
      1 / (4 * (Gamma.card + 1) : ℝ) := by
  let s := C.scale i
  have hs : 0 < s := C.scale_pos i
  have hm : (0 : ℝ) < 4 * (Gamma.card + 1) := by positivity
  have hfloor :
      (C.radius i : ℝ) ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ := by
    apply Nat.floor_le
    positivity
  calc
    (C.radius i : ℝ) * C.scale i = (C.radius i : ℝ) * s := rfl
    _ ≤ ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ * s :=
      mul_le_mul_of_nonneg_right hfloor hs.le
    _ = 1 / (4 * (Gamma.card + 1) : ℝ) := by
      field_simp

/-- The centred cyclic GAP extracted from a certificate. -/
noncomputable def progression (C : BohrLatticeCertificateF Gamma R bound) :
    CyclicGAPF N where
  rank := Gamma.card + 1
  step i := (C.point i 0 : ZMod N)
  radius := C.radius

@[simp] lemma progression_rank
    (C : BohrLatticeCertificateF Gamma R bound) :
    C.progression.rank = Gamma.card + 1 := rfl

@[simp] lemma progression_radius
    (C : BohrLatticeCertificateF Gamma R bound)
    (i : Fin (Gamma.card + 1)) :
    C.progression.radius i = C.radius i := rfl

/-- Integral linear combination of the certificate lattice points. -/
def combination (C : BohrLatticeCertificateF Gamma R bound)
    (u : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  fun j => ∑ i, u i * C.point i j

lemma combination_cast_coordinate [NeZero N]
    (C : BohrLatticeCertificateF Gamma R bound) (hN : 1 < N)
    (u : Fin (Gamma.card + 1) → ℤ) (j : Fin (Gamma.card + 1)) :
    (C.combination u j : ZMod N) =
      (C.combination u 0 : ZMod N) * indexedCyclicCharacterF Gamma j := by
  simp only [combination, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [C.point_cast_coordinate hN i j]
  ring

/-- Coefficients bounded by `a` progression radii produce a short lattice
combination in every coordinate. -/
lemma abs_combination_le
    (C : BohrLatticeCertificateF Gamma R bound) (hR : 0 < R)
    (a : ℕ) (u : Fin (Gamma.card + 1) → ℤ)
    (hu : ∀ i, |u i| ≤ (a * C.radius i : ℕ))
    (j : Fin (Gamma.card + 1)) :
    |(C.combination u j : ℝ)| ≤ (a : ℝ) * R / 4 := by
  let m := Gamma.card + 1
  have hm : (0 : ℝ) < m := by positivity
  have hterm (i : Fin m) :
      |(u i : ℝ) * (C.point i j : ℝ)| ≤
        (a : ℝ) * R / (4 * m : ℝ) := by
    rw [abs_mul]
    have huR : |(u i : ℝ)| ≤ (a : ℝ) * C.radius i := by
      rw [← Int.cast_abs]
      exact_mod_cast hu i
    calc
      |(u i : ℝ)| * |(C.point i j : ℝ)| ≤
          ((a : ℝ) * C.radius i) * (C.scale i * R) := by
            gcongr
            exact C.point_bound i j
      _ = (a : ℝ) * ((C.radius i : ℝ) * C.scale i) * R := by ring
      _ ≤ (a : ℝ) * (1 / (4 * m : ℝ)) * R := by
        gcongr
        simpa [m, Nat.cast_add, Nat.cast_one] using C.radius_mul_scale_le i
      _ = (a : ℝ) * R / (4 * m : ℝ) := by ring
  have hcast : (C.combination u j : ℝ) =
      ∑ i, (u i : ℝ) * (C.point i j : ℝ) := by
    simp [combination, point]
  rw [hcast]
  calc
    |∑ i, (u i : ℝ) * (C.point i j : ℝ)| ≤
        ∑ i, |(u i : ℝ) * (C.point i j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ((a : ℝ) * R / (4 * m : ℝ)) := by
      exact Finset.sum_le_sum fun i hi => hterm i
    _ = (a : ℝ) * R / 4 := by
      simp [m]
      field_simp

lemma eval_progression [NeZero N]
    (C : BohrLatticeCertificateF Gamma R bound)
    (x : C.progression.Param) :
    C.progression.eval x =
      (C.combination (C.progression.coeff x) 0 : ZMod N) := by
  simp only [CyclicGAPF.eval, progression, combination, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

end BohrLatticeCertificateF

end

end Jsp000216

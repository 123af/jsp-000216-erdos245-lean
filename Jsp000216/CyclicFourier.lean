import Mathlib

open scoped BigOperators ComplexConjugate
open Finset

namespace Jsp000216

noncomputable section

/-- Unnormalised Fourier transform of a finite subset of a cyclic group. -/
def cyclicFinsetFourierF {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (k : ZMod N) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar (-(a * k))

@[simp] lemma cyclicFinsetFourierF_zero {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    cyclicFinsetFourierF A 0 = A.card := by
  simp [cyclicFinsetFourierF]

lemma cyclicCharacterOrthogonalityF {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (x * k)) =
      if x = 0 then (N : ℂ) else 0 := by
  simpa [mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

/-- Parseval for the unnormalised cyclic Fourier transform. -/
theorem sum_fourier_mul_conjF {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ k : ZMod N,
      cyclicFinsetFourierF A k * conj (cyclicFinsetFourierF A k)) =
      (N : ℂ) * A.card := by
  classical
  simp only [cyclicFinsetFourierF, map_sum, Finset.sum_mul_sum]
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp_rw [hconj]
  simp_rw [← AddChar.map_add_eq_mul]
  have harg (i j k : ZMod N) : -(i * k) + j * k = (j - i) * k := by ring
  simp_rw [harg]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y ∈ A, (N : ℂ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
      simp_rw [cyclicCharacterOrthogonalityF]
      rw [Finset.sum_eq_single y]
      · simp
      · intro b hb hby
        simp only [if_neg (sub_ne_zero.mpr hby)]
      · exact fun h => (h hy).elim
    _ = (N : ℂ) * A.card := by
      rw [Finset.sum_const]
      simp [mul_comm]

/-- Real Parseval identity. -/
theorem sum_norm_sq_cyclicFinsetFourierF {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ k : ZMod N, ‖cyclicFinsetFourierF A k‖ ^ 2) =
      (N : ℝ) * A.card := by
  have hc := sum_fourier_mul_conjF A
  have h := congrArg Complex.re hc
  have hre (z : ℂ) : (z * conj z).re = Complex.normSq z := by
    rw [Complex.mul_conj]
    simp
  rw [Complex.re_sum] at h
  simp_rw [hre] at h
  simpa [Complex.normSq_eq_norm_sq] using h

/-- Frequencies whose Fourier coefficient has norm at least `τ`. -/
def cyclicLargeSpectrumF {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (τ : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter fun k => τ ≤ ‖cyclicFinsetFourierF A k‖

/-- Parseval cardinality bound for the large spectrum. -/
theorem card_cyclicLargeSpectrumF_mul_sq_le {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((cyclicLargeSpectrumF A τ).card : ℝ) * τ ^ 2 ≤
      (N : ℝ) * A.card := by
  classical
  let Γ := cyclicLargeSpectrumF A τ
  have hpoint : ∀ k ∈ Γ, τ ^ 2 ≤ ‖cyclicFinsetFourierF A k‖ ^ 2 := by
    intro k hk
    have hk' : τ ≤ ‖cyclicFinsetFourierF A k‖ := by
      simpa [Γ, cyclicLargeSpectrumF] using hk
    nlinarith [norm_nonneg (cyclicFinsetFourierF A k)]
  have hlower := Finset.card_nsmul_le_sum Γ
    (fun k => ‖cyclicFinsetFourierF A k‖ ^ 2) (τ ^ 2) hpoint
  have hupper :
      (∑ k ∈ Γ, ‖cyclicFinsetFourierF A k‖ ^ 2) ≤
        ∑ k : ZMod N, ‖cyclicFinsetFourierF A k‖ ^ 2 := by
    exact Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _
  rw [sum_norm_sq_cyclicFinsetFourierF A] at hupper
  simpa [nsmul_eq_mul] using le_trans hlower hupper

end

end Jsp000216

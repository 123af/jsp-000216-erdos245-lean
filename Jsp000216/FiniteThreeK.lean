import Jsp000216.CanonicalNormalize

open scoped Pointwise

namespace Jsp000216

noncomputable section

/-- `A` is contained in the displayed positive-step arithmetic progression. -/
def ContainedInAPF (A : Finset ℤ) (start : ℤ) (step length : ℕ) : Prop :=
  0 < step ∧
    ∀ x ∈ A, ∃ i : ℕ, i < length ∧
      x = start + (i : ℤ) * (step : ℤ)

lemma ContainedInAPF.mono_length
    {A : Finset ℤ} {start : ℤ} {step length length' : ℕ}
    (hA : ContainedInAPF A start step length) (hlen : length ≤ length') :
    ContainedInAPF A start step length' := by
  refine ⟨hA.1, ?_⟩
  intro x hx
  rcases hA.2 x hx with ⟨i, hi, hxi⟩
  exact ⟨i, hi.trans_le hlen, hxi⟩

lemma ContainedInAPF.card_le
    {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAPF A start step length) : A.card ≤ length := by
  let coord : ℤ → ℕ := fun x =>
    if hx : x ∈ A then Classical.choose (hA.2 x hx) else 0
  have hcoord : ∀ x ∈ A, coord x < length ∧
      x = start + (coord x : ℤ) * (step : ℤ) := by
    intro x hx
    simpa [coord, hx] using Classical.choose_spec (hA.2 x hx)
  have hinj : Set.InjOn coord A := by
    intro x hx y hy hxy
    have hxrep := (hcoord x hx).2
    have hyrep := (hcoord y hy).2
    have hstepZ : (step : ℤ) ≠ 0 := by exact_mod_cast hA.1.ne'
    have heq : start + (coord x : ℤ) * (step : ℤ) =
        start + (coord y : ℤ) * (step : ℤ) := by
      calc
        start + (coord x : ℤ) * (step : ℤ) = x := hxrep.symm
        _ = y := hxy
        _ = start + (coord y : ℤ) * (step : ℤ) := hyrep
    have hmul : (coord x : ℤ) * (step : ℤ) =
        (coord y : ℤ) * (step : ℤ) := add_left_cancel heq
    have hc : (coord x : ℤ) = (coord y : ℤ) :=
      mul_right_cancel₀ hstepZ hmul
    exact_mod_cast hc
  have hmaps : Set.MapsTo coord A (Finset.range length) := by
    intro x hx
    exact Finset.mem_range.mpr (hcoord x hx).1
  simpa using Finset.card_le_card_of_injOn coord hmaps hinj

/-- Explicit finite Freiman `3k-4`: the progression starts at the least
member of `A`, has common difference equal to the gcd of offsets from that
member, and has exactly the sharp Freiman number of displayed terms. -/
theorem freiman_three_k_minus_four_explicitF
    {A : Finset ℤ} (hA : A.Nonempty) (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    ContainedInAPF A (A.min' hA) (differenceContentF A (A.min' hA))
      ((A + A).card - A.card + 1) := by
  let B := freimanNormalizeF A hA
  have hBcard : B.card = A.card := by
    exact card_freimanNormalizeF hA (by omega)
  have hBsum : (B + B).card = (A + A).card := by
    exact card_add_freimanNormalizeF hA (by omega)
  have hBgcd : B.gcd id = 1 := by
    exact gcd_freimanNormalizeF_eq_one hA (by omega)
  obtain ⟨p, hp, hBsub, hB0, hBp⟩ :=
    exists_endpoint_freimanNormalizeF hA hcard
  have hsmallB : (B + B).card ≤ 3 * B.card - 4 := by
    rw [hBsum, hBcard]
    exact hsmall
  have hdiam : p + 1 ≤ (B + B).card - B.card + 1 :=
    normalized_small_doubling_diameter_bound_sharp
      hp hBsub hB0 hBp hBgcd hsmallB
  have hdiamA : p + 1 ≤ (A + A).card - A.card + 1 := by
    rw [hBsum, hBcard] at hdiam
    exact hdiam
  have hstep : 0 < differenceContentF A (A.min' hA) :=
    differenceContentF_pos (Finset.min'_mem A hA) (by omega)
  refine ⟨hstep, ?_⟩
  intro x hx
  let z := normalizationCoordF A (A.min' hA) x
  have hzB : z ∈ B := by
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hzI := Finset.mem_Icc.mp (hBsub hzB)
  let i := z.natAbs
  have hicast : (i : ℤ) = z := by
    dsimp [i]
    exact Int.natAbs_of_nonneg hzI.1
  have hileZ : (i : ℤ) ≤ (p : ℤ) := by
    rw [hicast]
    exact hzI.2
  have hile : i ≤ p := by
    exact_mod_cast hileZ
  have hi : i < (A + A).card - A.card + 1 := by
    have hip : i < p + 1 := by omega
    exact hip.trans_le hdiamA
  refine ⟨i, hi, ?_⟩
  have hrec := add_content_mul_normalizationCoordF
    (A := A) (a := A.min' hA) hx
  calc
    x = A.min' hA +
        (differenceContentF A (A.min' hA) : ℤ) * z := hrec.symm
    _ = A.min' hA + (i : ℤ) *
        (differenceContentF A (A.min' hA) : ℤ) := by
      rw [← hicast]
      ring

/-- Existential packaging of the finite `3k-4` inverse theorem. -/
theorem freiman_three_k_minus_fourF
    {A : Finset ℤ} (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    ∃ start : ℤ, ∃ step : ℕ,
      ContainedInAPF A start step ((A + A).card - A.card + 1) := by
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨A.min' hA, differenceContentF A (A.min' hA),
    freiman_three_k_minus_four_explicitF hA hcard hsmall⟩

end

end Jsp000216

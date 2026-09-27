import Jsp000216.AffineNormalize

open scoped Pointwise

namespace Jsp000216

noncomputable section

/-- Canonical affine normalization: translate by the least element and divide
by the gcd of all offsets from it. -/
def freimanNormalizeF (A : Finset ℤ) (hA : A.Nonempty) : Finset ℤ :=
  normalizeAtF A (A.min' hA)

lemma card_freimanNormalizeF {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalizeF A hA).card = A.card := by
  exact card_normalizeAtF (Finset.min'_mem A hA) hcard

lemma zero_mem_freimanNormalizeF {A : Finset ℤ} (hA : A.Nonempty) :
    0 ∈ freimanNormalizeF A hA := by
  exact zero_mem_normalizeAtF (Finset.min'_mem A hA)

lemma freimanNormalizeF_nonneg {A : Finset ℤ} (hA : A.Nonempty)
    {z : ℤ} (hz : z ∈ freimanNormalizeF A hA) : 0 ≤ z := by
  apply normalizeAtF_nonneg (A := A) (a := A.min' hA)
  · intro x hx
    exact Finset.min'_le A x hx
  · exact hz

lemma gcd_freimanNormalizeF_eq_one {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalizeF A hA).gcd id = 1 := by
  exact gcd_normalizeAtF_eq_one (Finset.min'_mem A hA) hcard

lemma card_add_freimanNormalizeF {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 2 ≤ A.card) :
    (freimanNormalizeF A hA + freimanNormalizeF A hA).card =
      (A + A).card := by
  exact card_add_normalizeAtF (Finset.min'_mem A hA) hcard

/-- A normalized set with at least three points has a positive natural
endpoint `p` and is exactly positioned inside `[0,p]` with both endpoints
present. -/
lemma exists_endpoint_freimanNormalizeF {A : Finset ℤ} (hA : A.Nonempty)
    (hcard : 3 ≤ A.card) :
    ∃ p : ℕ, 0 < p ∧
      freimanNormalizeF A hA ⊆ Finset.Icc 0 (p : ℤ) ∧
      0 ∈ freimanNormalizeF A hA ∧
      (p : ℤ) ∈ freimanNormalizeF A hA := by
  let B := freimanNormalizeF A hA
  have hBcard : B.card = A.card := by
    exact card_freimanNormalizeF hA (by omega)
  have hBpos : 0 < B.card := by omega
  have hBne : B.Nonempty := Finset.card_pos.mp hBpos
  let qz := B.max' hBne
  have hqmem : qz ∈ B := Finset.max'_mem B hBne
  have hqnonneg : 0 ≤ qz := by
    exact freimanNormalizeF_nonneg hA hqmem
  let p := qz.natAbs
  have hpcast : (p : ℤ) = qz := by
    dsimp [p]
    exact Int.natAbs_of_nonneg hqnonneg
  have hp : 0 < p := by
    by_contra hnot
    have hp0 : p = 0 := Nat.eq_zero_of_not_pos hnot
    have hq0 : qz = 0 := by
      rw [← hpcast, hp0]
      norm_num
    have hsub0 : B ⊆ {0} := by
      intro z hz
      have hz0 : 0 ≤ z := freimanNormalizeF_nonneg hA hz
      have hzq : z ≤ qz := Finset.le_max' B z hz
      simp only [Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub0
    have hcle : B.card ≤ 1 := by simpa using hc
    omega
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · intro z hz
    have hz0 : 0 ≤ z := freimanNormalizeF_nonneg hA hz
    have hzq : z ≤ qz := Finset.le_max' B z hz
    rw [← hpcast] at hzq
    exact Finset.mem_Icc.mpr ⟨hz0, hzq⟩
  · exact zero_mem_freimanNormalizeF hA
  · rw [hpcast]
    exact hqmem

end

end Jsp000216

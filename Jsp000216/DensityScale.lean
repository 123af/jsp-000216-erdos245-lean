import Jsp000216.SetCount

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

/-- Zero natural density turns any fixed multiple of the counting function
into an eventual strict lower-order term. -/
lemma density_eventually_mul_ltF (a : ℕ → ℕ)
    (hden : Tendsto (fun N => (a N : ℝ) / N) atTop (𝓝 0))
    {M : ℕ} (hM : 0 < M) :
    ∀ᶠ N in atTop, M * a N < N := by
  have hratio : ∀ᶠ N in atTop, (a N : ℝ) / N < 1 / (M : ℝ) :=
    hden.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hcross : (a N : ℝ) * M < (N : ℝ) := by
    simpa only [one_mul] using (div_lt_div_iff₀ hNr hMr).mp hN
  have hcross' : (M : ℝ) * (a N : ℝ) < (N : ℝ) := by
    simpa only [mul_comm] using hcross
  exact_mod_cast hcross'

/-- For an infinite positive set of zero density, there are arbitrarily
large cutoffs where doubling the cutoff multiplies the counting function by
at most four. -/
lemma frequently_countInF_two_mul_le_four
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0)) :
    ∃ᶠ N in atTop, countInF S (2 * N) ≤ 4 * countInF S N := by
  by_contra hfreq
  have hgrow : ∀ᶠ N in atTop,
      4 * countInF S N < countInF S (2 * N) := by
    filter_upwards [(Filter.not_frequently.mp hfreq)] with N hN
    omega
  have hdense : ∀ᶠ N in atTop, 2 * countInF S N < N :=
    density_eventually_mul_ltF (countInF S) hden (by omega)
  have hpositive : ∀ᶠ N in atTop, 0 < countInF S N :=
    eventually_countInF_pos hS hpos
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hgrow.and (hdense.and hpositive))
  let N₀ := max 1 L
  have hN₀L : L ≤ N₀ := le_max_right _ _
  have hN₀pos : 0 < N₀ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have haN₀ : 0 < countInF S N₀ := (hL N₀ hN₀L).2.2
  have hiter : ∀ t : ℕ,
      4 ^ t * countInF S N₀ ≤ countInF S (2 ^ t * N₀) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hscale : L ≤ 2 ^ t * N₀ := by
          have hp : 1 ≤ 2 ^ t := by
            have : 0 < 2 ^ t := pow_pos (by omega) _
            omega
          calc
            L ≤ N₀ := hN₀L
            _ = 1 * N₀ := by simp
            _ ≤ 2 ^ t * N₀ := Nat.mul_le_mul_right N₀ hp
        have hstep := (hL (2 ^ t * N₀) hscale).1
        calc
          4 ^ (t + 1) * countInF S N₀ =
              4 * (4 ^ t * countInF S N₀) := by ring
          _ ≤ 4 * countInF S (2 ^ t * N₀) :=
            Nat.mul_le_mul_left 4 ih
          _ ≤ countInF S (2 * (2 ^ t * N₀)) := hstep.le
          _ = countInF S (2 ^ (t + 1) * N₀) := by ring_nf
  have hscale : L ≤ 2 ^ N₀ * N₀ := by
    have hp : 1 ≤ 2 ^ N₀ := by
      have : 0 < 2 ^ N₀ := pow_pos (by omega) _
      omega
    calc
      L ≤ N₀ := hN₀L
      _ = 1 * N₀ := by simp
      _ ≤ 2 ^ N₀ * N₀ := Nat.mul_le_mul_right N₀ hp
  have hsmall := (hL (2 ^ N₀ * N₀) hscale).2.1
  have hlower := hiter N₀
  have hpow : 2 ^ N₀ * N₀ < 4 ^ N₀ := by
    calc
      2 ^ N₀ * N₀ < 2 ^ N₀ * 2 ^ N₀ :=
        (Nat.mul_lt_mul_left (pow_pos (by omega) _)).2 N₀.lt_two_pow_self
      _ = 4 ^ N₀ := by rw [← Nat.mul_pow]
  have hfour : 4 ^ N₀ ≤ countInF S (2 ^ N₀ * N₀) := by
    calc
      4 ^ N₀ = 4 ^ N₀ * 1 := by simp
      _ ≤ 4 ^ N₀ * countInF S N₀ :=
        Nat.mul_le_mul_left _ haN₀
      _ ≤ countInF S (2 ^ N₀ * N₀) := hlower
  have hcontra : 2 * 4 ^ N₀ < 2 ^ N₀ * N₀ := by
    exact (Nat.mul_le_mul_left 2 hfour).trans_lt hsmall
  omega

end Jsp000216

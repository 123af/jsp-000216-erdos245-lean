import Jsp000216.DensityScale
import Jsp000216.InverseBridge

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- Once arbitrarily late doubling gaps are available, zero density is
incompatible with an eventual ratio separated from three by `1/m`.
The remaining infinite structural task is therefore exactly to manufacture
those gaps from the weaker eventual `< 3` hypothesis. -/
lemma contradiction_of_arbitrarily_late_doubling_gaps
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m)
    (hscaled : ∀ᶠ N in atTop,
      m * countInF (S + S) N + countInF S N <
        3 * m * countInF S N)
    (hgaps : ∀ s : ℕ, ∃ i ≥ s,
      2 * enumerateF S i < enumerateF S (i + 1)) : False := by
  let D := enumerateF S 0 + 2 * enumerateF S 1
  have hdense : ∀ᶠ N in atTop, (D + 1) * countInF S N < N :=
    density_eventually_mul_ltF (countInF S) hden (by omega)
  obtain ⟨Ld, hLd⟩ := eventually_atTop.1 hdense
  obtain ⟨Ls, hLs⟩ := eventually_atTop.1 hscaled
  let s := max 2 (max (3 * m) (max Ld Ls))
  obtain ⟨i, his, hgap⟩ := hgaps s
  have hi2 : 2 ≤ i := by
    dsimp [s] at his
    omega
  have hik : 3 * m ≤ i + 1 := by
    dsimp [s] at his
    omega
  have henum_ge : ∀ j : ℕ, j + 1 ≤ enumerateF S j := by
    intro j
    induction j with
    | zero =>
        simpa using hpos (enumerateF_mem hS 0)
    | succ j ih =>
        have hstep : enumerateF S j < enumerateF S (j + 1) :=
          enumerateF_strictMono hS (Nat.lt_succ_self j)
        have hstep' : enumerateF S j + 1 ≤ enumerateF S (j + 1) :=
          Nat.succ_le_of_lt hstep
        have hind : j + 2 ≤ enumerateF S j + 1 :=
          Nat.add_le_add_right ih 1
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hind.trans hstep'
  have hEiLd : Ld ≤ enumerateF S i := by
    have hei := henum_ge i
    dsimp [s] at his
    omega
  have hLs_le_i : Ls ≤ i := by
    dsimp [s] at his
    omega
  have hi_le_ei : i ≤ enumerateF S i := by
    have hei := henum_ge i
    omega
  have hLs_le_ei : Ls ≤ enumerateF S i := hLs_le_i.trans hi_le_ei
  have hei_le_two : enumerateF S i ≤ 2 * enumerateF S i := by
    omega
  have hTwoEiLs : Ls ≤ 2 * enumerateF S i := hLs_le_ei.trans hei_le_two
  have hscaled_i := hLs (2 * enumerateF S i) hTwoEiLs
  rw [countInF_two_enumerate_eq_at_doubling_gap hS hpos i hgap] at hscaled_i
  have hsmall :
      countInF (S + S) (2 * enumerateF S i) ≤ 3 * (i + 1) - 4 := by
    by_contra hnot
    have hsumlower :
        3 * (i + 1) - 3 ≤ countInF (S + S) (2 * enumerateF S i) := by
      omega
    have hsumplus :
        3 * (i + 1) ≤
          countInF (S + S) (2 * enumerateF S i) + 3 := by
      omega
    have hmul := Nat.mul_le_mul_left m hsumplus
    nlinarith
  have hlinear := enumerateF_linear_bound_at_gap hS hpos hi2 hgap hsmall
  have hdense_i := hLd (enumerateF S i) hEiLd
  rw [countInF_enumerate_eq hS hpos i] at hdense_i
  have hDlt :
      D * (i + 1) < (D + 1) * (i + 1) := by
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self D) (by omega)
  have hlinear' : enumerateF S i ≤ D * (i + 1) := by
    simpa [D] using hlinear
  exact (Nat.not_lt_of_ge hlinear') (hDlt.trans hdense_i)

end

end Jsp000216

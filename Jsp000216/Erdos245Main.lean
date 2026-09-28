import Jsp000216.Erdos245Cover
import Jsp000216.CoreAssembly

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- No fixed reciprocal-integer gap below `3` can eventually bound the
sumset/counting-function ratio.  This is the scale-free core of Erdős #245. -/
theorem erdos245_no_eventual_scaled_below_threeF
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    ¬ (∀ᶠ N in atTop,
      m * countInF (S + S) N + countInF S N <
        3 * m * countInF S N) := by
  intro hscaled
  exact contradiction_of_scaled_three_of_cover
    hS hpos hden hm erdos245_uniformGAPCoverF hscaled

/-- Equivalently, for every positive integer `m`, arbitrarily late cutoffs
satisfy the lower ratio bound `3 - 1/m` after clearing denominators. -/
theorem erdos245_frequently_scaled_threeF
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    ∃ᶠ N in atTop,
      3 * m * countInF S N ≤
        m * countInF (S + S) N + countInF S N := by
  by_contra hfreq
  have hscaled : ∀ᶠ N in atTop,
      m * countInF (S + S) N + countInF S N <
        3 * m * countInF S N := by
    filter_upwards [Filter.not_frequently.mp hfreq] with N hN
    omega
  exact erdos245_no_eventual_scaled_below_threeF hS hpos hden hm hscaled

end

end Jsp000216

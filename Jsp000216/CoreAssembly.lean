import Jsp000216.ConditionalGap
import Jsp000216.GapContradiction

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- The complete integer-counting core, conditional only on one uniform
Freiman/GAP covering theorem at doubling constant `12`.  An eventual ratio
separated from three by `1/m` both supplies the weaker `< 3` hypothesis that
manufactures doubling gaps and, at those gaps, contradicts zero density via
the finite `3k-4` theorem. -/
lemma contradiction_of_scaled_three_of_cover
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0))
    {R C m : ℕ} (hm : 0 < m)
    (hcover : UniformGAPCoverF 12 R C)
    (hscaled : ∀ᶠ N in atTop,
      m * countInF (S + S) N + countInF S N <
        3 * m * countInF S N) : False := by
  have hsum : ∀ᶠ N in atTop,
      countInF (S + S) N < 3 * countInF S N := by
    filter_upwards [hscaled] with N hN
    have hmul : m * countInF (S + S) N <
        m * (3 * countInF S N) := by
      nlinarith
    exact (Nat.mul_lt_mul_left hm).mp (by
      simpa [mul_assoc] using hmul)
  have hgaps :=
    exists_doubling_gap_of_eventually_three_of_cover
      hS hpos hden hcover hsum
  exact contradiction_of_arbitrarily_late_doubling_gaps
    hS hpos hden hm hscaled hgaps

end

end Jsp000216

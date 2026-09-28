import Jsp000216.Erdos245Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- The natural-cutoff sumset/counting ratio, regarded in the extended reals. -/
noncomputable def erdos245NatRatioF (S : Set ℕ) (N : ℕ) : EReal :=
  (((countInF (S + S) N : ℝ) / (countInF S N : ℝ)) : EReal)

/-- Every reciprocal-integer approximation to `3` is attained arbitrarily
far out by the natural-cutoff ratio. -/
theorem erdos245_frequently_ratio_geF
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    ∃ᶠ N in atTop,
      (((3 : ℝ) - 1 / (m : ℝ) : ℝ) : EReal) ≤ erdos245NatRatioF S N := by
  have hscaled := erdos245_frequently_scaled_threeF hS hpos hden hm
  have hcountpos := eventually_countInF_pos hS hpos
  exact (hscaled.and_eventually hcountpos).mono (fun N hN => by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have haR : (0 : ℝ) < countInF S N := by exact_mod_cast hN.2
    have hreal :
        (3 : ℝ) * (m : ℝ) * (countInF S N : ℝ) ≤
          (m : ℝ) * (countInF (S + S) N : ℝ) + (countInF S N : ℝ) := by
      exact_mod_cast hN.1
    have haux :
        ((3 : ℝ) * (countInF S N : ℝ) - (countInF (S + S) N : ℝ)) *
            (m : ℝ) ≤
          (countInF S N : ℝ) := by
      nlinarith
    have hfrac :
        (3 : ℝ) * (countInF S N : ℝ) - (countInF (S + S) N : ℝ) ≤
          (countInF S N : ℝ) / (m : ℝ) :=
      (le_div_iff₀ hmR).2 haux
    have hratio :
        (3 : ℝ) - 1 / (m : ℝ) ≤
          (countInF (S + S) N : ℝ) / (countInF S N : ℝ) := by
      rw [le_div_iff₀ haR]
      calc
        ((3 : ℝ) - 1 / (m : ℝ)) * (countInF S N : ℝ) =
            (3 : ℝ) * (countInF S N : ℝ) -
              (countInF S N : ℝ) / (m : ℝ) := by ring
        _ ≤ (countInF (S + S) N : ℝ) := by linarith
    dsimp [erdos245NatRatioF]
    exact_mod_cast hratio)

/-- Natural-cutoff form of Erdős #245 for positive infinite zero-density
sets: the extended-real limsup of the sumset/counting ratio is at least `3`. -/
theorem erdos245_nat_limsupF
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0)) :
    (3 : EReal) ≤ limsup (erdos245NatRatioF S) atTop := by
  let L : EReal := limsup (erdos245NatRatioF S) atTop
  have happrox (n : ℕ) :
      (((3 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal) ≤ L := by
    dsimp [L]
    exact le_limsup_of_frequently_le
      (erdos245_frequently_ratio_geF hS hpos hden (m := n + 1) (by omega))
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hlimR :
      Tendsto (fun n : ℕ => (3 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 3) := by
    simpa using tendsto_const_nhds.sub hone
  have hlimE :
      Tendsto
        (fun n : ℕ => (((3 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
        atTop (𝓝 (3 : EReal)) :=
    EReal.tendsto_coe.mpr hlimR
  change (3 : EReal) ≤ L
  apply ge_of_tendsto hlimE
  exact Filter.Eventually.of_forall happrox

end

end Jsp000216

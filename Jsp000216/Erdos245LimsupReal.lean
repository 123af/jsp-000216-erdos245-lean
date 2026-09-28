import Jsp000216.Erdos245LimsupNat

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- The exact real-cutoff ratio appearing in Erdős #245. -/
noncomputable def erdos245RealRatioF (S : Set ℕ) (x : ℝ) : EReal :=
  (((S + S) ∩ Set.Icc 1 ⌊x⌋₊).ncard : EReal) /
    ((S ∩ Set.Icc 1 ⌊x⌋₊).ncard : EReal)

lemma erdos245RealRatio_natCastF (S : Set ℕ) (N : ℕ) :
    erdos245RealRatioF S (N : ℝ) = erdos245NatRatioF S N := by
  simp [erdos245RealRatioF, erdos245NatRatioF, countInF_eq_ncard,
    Nat.floor_natCast, EReal.coe_div]

/-- A real-cutoff zero-density hypothesis restricts to the natural cutoffs
used by the combinatorial core. -/
lemma erdos245_density_nat_of_realF (S : Set ℕ)
    (hden : Tendsto
      (fun x : ℝ => ((S ∩ Set.Icc 1 ⌊x⌋₊).ncard : ℝ) / x)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (countInF S N : ℝ) / N) atTop (𝓝 0) := by
  have h := hden.comp tendsto_natCast_atTop_atTop
  simpa [countInF_eq_ncard, Nat.floor_natCast] using h

/-- The reciprocal-integer lower bounds occur frequently also on the real
cutoff filter, by the cofinal inclusion `ℕ → ℝ`. -/
theorem erdos245_frequently_real_ratio_geF
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto
      (fun x : ℝ => ((S ∩ Set.Icc 1 ⌊x⌋₊).ncard : ℝ) / x)
      atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    ∃ᶠ x : ℝ in atTop,
      (((3 : ℝ) - 1 / (m : ℝ) : ℝ) : EReal) ≤ erdos245RealRatioF S x := by
  have hdenNat := erdos245_density_nat_of_realF S hden
  have hfreq := erdos245_frequently_ratio_geF hS hpos hdenNat hm
  exact tendsto_natCast_atTop_atTop.frequently_map
    (fun N hN => by simpa [erdos245RealRatio_natCastF] using hN) hfreq

/-- Real-cutoff positive-set form of Erdős #245. -/
theorem erdos245_real_limsup_positiveF
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto
      (fun x : ℝ => ((S ∩ Set.Icc 1 ⌊x⌋₊).ncard : ℝ) / x)
      atTop (𝓝 0)) :
    (3 : EReal) ≤ limsup (erdos245RealRatioF S) atTop := by
  let L : EReal := limsup (erdos245RealRatioF S) atTop
  have happrox (n : ℕ) :
      (((3 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal) ≤ L := by
    dsimp [L]
    exact le_limsup_of_frequently_le
      (erdos245_frequently_real_ratio_geF hS hpos hden
        (m := n + 1) (by omega))
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
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
  apply le_of_tendsto hlimE
  exact Filter.Eventually.of_forall happrox

end

end Jsp000216

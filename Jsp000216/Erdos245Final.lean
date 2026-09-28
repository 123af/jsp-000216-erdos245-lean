import Jsp000216.Erdos245LimsupReal

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

lemma positivePart_inter_IccF (A : Set ℕ) (N : ℕ) :
    (A ∩ Set.Ici 1) ∩ Set.Icc 1 N = A ∩ Set.Icc 1 N := by
  ext x
  constructor
  · rintro ⟨⟨hxA, hx1⟩, hxIcc⟩
    exact ⟨hxA, hxIcc⟩
  · rintro ⟨hxA, hxIcc⟩
    exact ⟨⟨hxA, hxIcc.1⟩, hxIcc⟩

/-- Full real-cutoff statement of Erdős Problem #245 (without the external
`answer(True)` wrapper used by the Formal Conjectures repository). -/
theorem erdos245_limsupF
    (A : Set ℕ) (hA : A.Infinite)
    (hden : Tendsto
      (fun x : ℝ => ((A ∩ Set.Icc 1 ⌊x⌋₊).ncard : ℝ) / x)
      atTop (𝓝 0)) :
    (3 : EReal) ≤ limsup (erdos245RealRatioF A) atTop := by
  let S : Set ℕ := A ∩ Set.Ici 1
  have hSA : S ⊆ A := by
    intro x hx
    exact hx.1
  have hS : S.Infinite := by
    intro hSfin
    apply hA
    apply (hSfin.union (Set.finite_singleton 0)).subset
    intro x hx
    by_cases hx0 : x = 0
    · right
      simpa [hx0]
    · left
      exact ⟨hx, Nat.one_le_iff_ne_zero.mpr hx0⟩
  have hSpos : S ⊆ Set.Ici 1 := by
    intro x hx
    exact hx.2
  have hdenS : Tendsto
      (fun x : ℝ => ((S ∩ Set.Icc 1 ⌊x⌋₊).ncard : ℝ) / x)
      atTop (𝓝 0) := by
    simpa [S, positivePart_inter_IccF] using hden
  have hSmain := erdos245_real_limsup_positiveF hS hSpos hdenS
  have hratio (x : ℝ) : erdos245RealRatioF S x ≤ erdos245RealRatioF A x := by
    dsimp [erdos245RealRatioF]
    rw [show S ∩ Set.Icc 1 ⌊x⌋₊ = A ∩ Set.Icc 1 ⌊x⌋₊ by
      simpa [S] using positivePart_inter_IccF A ⌊x⌋₊]
    have hsum : S + S ⊆ A + A := Set.add_subset_add hSA hSA
    have hinter :
        (S + S) ∩ Set.Icc 1 ⌊x⌋₊ ⊆
          (A + A) ∩ Set.Icc 1 ⌊x⌋₊ := by
      intro z hz
      exact ⟨hsum hz.1, hz.2⟩
    have hfin : ((A + A) ∩ Set.Icc 1 ⌊x⌋₊).Finite :=
      (Set.finite_Icc 1 ⌊x⌋₊).subset Set.inter_subset_right
    have hn :
        ((S + S) ∩ Set.Icc 1 ⌊x⌋₊).ncard ≤
          ((A + A) ∩ Set.Icc 1 ⌊x⌋₊).ncard :=
      Set.ncard_le_ncard hinter hfin
    apply EReal.div_le_div_right_of_nonneg (by positivity)
    exact_mod_cast hn
  have hLmono :
      limsup (erdos245RealRatioF S) atTop ≤
        limsup (erdos245RealRatioF A) atTop :=
    limsup_le_limsup (Filter.Eventually.of_forall hratio)
  exact hSmain.trans hLmono

end

end Jsp000216

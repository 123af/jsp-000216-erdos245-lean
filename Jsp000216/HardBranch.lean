import Jsp000216.ModFiber

open Finset
open scoped Pointwise

namespace Jsp000216

/-- In the normalized gcd-one setting, the existence of a stable hole forces
self-sum growth all the way to the `3|A|-3` threshold. -/
lemma normalized_stable_branch_sumset_lower_bound
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1)
    (hstable : (stableHolesF A (p : ℤ)).Nonempty) :
    3 * A.card - 3 ≤ (A + A).card := by
  letI : NeZero p := ⟨Nat.ne_zero_of_lt hp⟩
  let B := modImageF p A
  let C := modSelfSumF p A
  let H := modStabF p A
  let Sat := modSatF p A
  have hAne : A.Nonempty := ⟨0, h0⟩
  have hHzero : (0 : ZMod p) ∈ H := by
    exact zero_mem_modStabF hAne
  have hHpos : 0 < H.card := Finset.card_pos.mpr ⟨0, hHzero⟩
  have hproper : H ≠ Finset.univ := by
    exact modStabF_ne_univ_of_stableHolesF_nonempty hp hAint h0 htop hstable
  have hnot : ¬ B ⊆ H := by
    exact not_modImageF_subset_modStabF_of_gcd_one_of_stab_ne_univ hAne hgcd hproper
  have hBsat : 2 * H.card ≤ Sat.card := by
    exact two_mul_modStab_card_le_modSat_card_of_not_subset h0 hnot
  have hk : 2 * Sat.card ≤ C.card + H.card := by
    exact modSat_kneser (p := p) A
  have hSatH : Sat.card + H.card ≤ C.card := by
    omega
  have hCnotSat : ¬ C ⊆ Sat := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  rcases Finset.not_subset.mp hCnotSat with ⟨c, hcC, hcSat⟩
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact modStabF_add_mem hAne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact modStabF_neg_mem hAne hx
  let D := c +ᵥ H
  have hDsubC : D ⊆ C := by
    have hs : D ⊆ C + H := by
      intro z hz
      rcases Finset.mem_vadd_finset.mp hz with ⟨h, hh, hhz⟩
      exact Finset.mem_add.mpr ⟨c, hcC, h, hh, hhz⟩
    change D ⊆ modSelfSumF p A + (modSelfSumF p A).addStab at hs
    change D ⊆ modSelfSumF p A
    simpa only [Finset.add_addStab] using hs
  have hDdisjSat : Disjoint D Sat := by
    exact disjoint_vadd_add_of_closed_not_memF hHadd hHneg hcSat
  have hDdisjB : Disjoint D B := by
    exact hDdisjSat.mono_right (modImageF_subset_modSatF hAne)
  change c ∈ B + B at hcC
  rcases Finset.mem_add.mp hcC with ⟨a, haB, b, hbB, hab⟩
  let R := residueFiberSetF p A (a +ᵥ H)
  let S := residueFiberSetF p A (b +ᵥ H)
  let F := sumsetOverResiduesF p A D
  have hRne : R.Nonempty := by
    rcases Finset.mem_image.mp haB with ⟨x, hxA, hxa⟩
    refine ⟨x, mem_residueFiberSetF.mpr ⟨hxA, ?_⟩⟩
    apply Finset.mem_vadd_finset.mpr
    exact ⟨0, hHzero, by simpa using hxa.symm⟩
  have hSne : S.Nonempty := by
    rcases Finset.mem_image.mp hbB with ⟨y, hyA, hyb⟩
    refine ⟨y, mem_residueFiberSetF.mpr ⟨hyA, ?_⟩⟩
    apply Finset.mem_vadd_finset.mpr
    exact ⟨0, hHzero, by simpa using hyb.symm⟩
  have hRF : R + S ⊆ F := by
    exact residueFiberSetF_add_subset_sumsetOverResiduesF hab hHadd
  have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hRne hSne
  have hFcard : R.card + S.card ≤ F.card + 1 := by
    have hs := Finset.card_le_card hRF
    change R.card + S.card - 1 ≤ (R + S).card at hcauchy
    have hRp : 0 < R.card := Finset.card_pos.mpr hRne
    have hSp : 0 < S.card := Finset.card_pos.mpr hSne
    omega
  have hAsatFiber : B.card + H.card ≤ Sat.card + R.card := by
    exact card_modImage_add_card_le_saturation_add_fiberF hHzero haB
  have hBsatFiber : B.card + H.card ≤ Sat.card + S.card := by
    exact card_modImage_add_card_le_saturation_add_fiberF hHzero hbB
  have hDcard : D.card = H.card := Finset.card_vadd_finset c H
  have hrefined : C.card + A.card + F.card ≤ (A + A).card + H.card := by
    have hr := card_modSelfSum_add_card_add_fiber_le D hp h0 htop hDsubC hDdisjB
    rw [hDcard] at hr
    exact hr
  have hBcard : B.card = A.card - 1 := by
    exact card_modImageF_normalized hp hAint h0 htop
  have hcard : 2 ≤ A.card := by
    have hne : (0 : ℤ) ≠ (p : ℤ) := by omega
    have hpair : ({0, (p : ℤ)} : Finset ℤ) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact htop
    have hc := Finset.card_le_card hpair
    simpa [hne] using hc
  omega

/-- Under normalized gcd-one small doubling, the stable-hole branch is
impossible. -/
lemma normalized_small_doubling_stableHolesF_empty
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    stableHolesF A (p : ℤ) = ∅ := by
  by_contra hne
  have hstable : (stableHolesF A (p : ℤ)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hlow := normalized_stable_branch_sumset_lower_bound
    hp hAint h0 htop hgcd hstable
  have hcard : 2 ≤ A.card := by
    have hnep : (0 : ℤ) ≠ (p : ℤ) := by omega
    have hpair : ({0, (p : ℤ)} : Finset ℤ) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact htop
    have hc := Finset.card_le_card hpair
    simpa [hnep] using hc
  omega

/-- Normalized finite `3k-4` diameter/progression-length bound. -/
lemma normalized_small_doubling_interval_bound
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    (Finset.Icc 0 (p : ℤ)).card ≤ 2 * A.card - 3 := by
  have hstable := normalized_small_doubling_stableHolesF_empty
    hp hAint h0 htop hgcd hsmall
  have hIcc := no_stable_interval_length_le_sumset_sub_card_add_one
    hAint h0 htop hstable
  have hAsum : A.card ≤ (A + A).card :=
    Finset.card_le_card (subset_self_sumset_of_zero h0)
  have hcard : 2 ≤ A.card := by
    have hnep : (0 : ℤ) ≠ (p : ℤ) := by omega
    have hpair : ({0, (p : ℤ)} : Finset ℤ) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact htop
    have hc := Finset.card_le_card hpair
    simpa [hnep] using hc
  have hsub : (A + A).card - A.card ≤ (3 * A.card - 4) - A.card :=
    Nat.sub_le_sub_right hsmall A.card
  have harith : (3 * A.card - 4) - A.card + 1 = 2 * A.card - 3 := by
    omega
  calc
    (Finset.Icc 0 (p : ℤ)).card
        ≤ (A + A).card - A.card + 1 := hIcc
    _ ≤ (3 * A.card - 4) - A.card + 1 := Nat.add_le_add_right hsub 1
    _ = 2 * A.card - 3 := harith

end Jsp000216

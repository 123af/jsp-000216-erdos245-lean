import Jsp000216.ModCard

open scoped Pointwise

namespace Jsp000216

lemma modSelfSum_card_ge_two_modImage_sub_one_of_stab_card_one
    {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty)
    (hstab : (modStabF p A).card = 1) :
    2 * (modImageF p A).card - 1 ≤ (modSelfSumF p A).card := by
  have hsub : modImageF p A ⊆ modSatF p A := modImageF_subset_modSatF hA
  have hcard : (modImageF p A).card ≤ (modSatF p A).card := Finset.card_le_card hsub
  have hk := modSat_kneser (p := p) A
  rw [hstab] at hk
  omega

lemma modSelfSum_card_ge_two_card_sub_three_of_stab_card_one
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hstab : (modStabF p A).card = 1) :
    2 * A.card - 3 ≤ (modSelfSumF p A).card := by
  have hAne : A.Nonempty := ⟨0, h0⟩
  have h := modSelfSum_card_ge_two_modImage_sub_one_of_stab_card_one
    (p := p) (A := A) hAne hstab
  rw [card_modImageF_normalized hp hAint h0 htop] at h
  have hcard : 2 ≤ A.card := by
    have hne : (0 : ℤ) ≠ (p : ℤ) := by omega
    exact Finset.two_le_card.mpr ⟨0, h0, (p : ℤ), htop, hne⟩
  omega

end Jsp000216

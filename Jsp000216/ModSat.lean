import Jsp000216.ModGcd

open scoped Pointwise

namespace Jsp000216

lemma modStabF_subset_modSatF_of_zero_mem {p : ℕ} {A : Finset ℤ}
    (h0 : 0 ∈ A) :
    modStabF p A ⊆ modSatF p A := by
  intro h hh
  exact Finset.mem_add.mpr
    ⟨0, zero_mem_modImageF h0, h, hh, by simp⟩

lemma modStab_card_add_one_le_modSat_card_of_not_subset
    {p : ℕ} {A : Finset ℤ} (h0 : 0 ∈ A)
    (hnot : ¬ modImageF p A ⊆ modStabF p A) :
    (modStabF p A).card + 1 ≤ (modSatF p A).card := by
  have hAne : A.Nonempty := ⟨0, h0⟩
  rcases Finset.not_subset.mp hnot with ⟨b, hbB, hbH⟩
  have hbSat : b ∈ modSatF p A := by
    exact Finset.mem_add.mpr
      ⟨b, hbB, 0, zero_mem_modStabF hAne, by simp⟩
  have hinsub : insert b (modStabF p A) ⊆ modSatF p A := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hbSat
    · exact modStabF_subset_modSatF_of_zero_mem h0 hx
  have hc := Finset.card_le_card hinsub
  simpa [hbH] using hc

lemma modStab_card_dvd_modSat_card (p : ℕ) (A : Finset ℤ) :
    (modStabF p A).card ∣ (modSatF p A).card := by
  simpa [modStabF, modSatF] using
    (Finset.card_addStab_dvd_card_add_addStab
      (modImageF p A) (modSelfSumF p A))

lemma two_mul_modStab_card_le_modSat_card_of_not_subset
    {p : ℕ} {A : Finset ℤ} (h0 : 0 ∈ A)
    (hnot : ¬ modImageF p A ⊆ modStabF p A) :
    2 * (modStabF p A).card ≤ (modSatF p A).card := by
  have hplus := modStab_card_add_one_le_modSat_card_of_not_subset h0 hnot
  have hdvd := modStab_card_dvd_modSat_card p A
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at hplus ⊢
  have hk2 : 2 ≤ k := by
    by_contra h
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · simp at hplus
    · omega
  have hm := Nat.mul_le_mul_left (modStabF p A).card hk2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hm

lemma two_mul_modStab_card_le_modSat_card_of_gcd_one_of_stab_ne_univ
    {p : ℕ} [NeZero p] {A : Finset ℤ}
    (h0 : 0 ∈ A) (hgcd : A.gcd id = 1)
    (hproper : modStabF p A ≠ Finset.univ) :
    2 * (modStabF p A).card ≤ (modSatF p A).card := by
  have hAne : A.Nonempty := ⟨0, h0⟩
  exact two_mul_modStab_card_le_modSat_card_of_not_subset h0
    (not_modImageF_subset_modStabF_of_gcd_one_of_stab_ne_univ hAne hgcd hproper)

lemma three_mul_modStab_card_le_modSelfSum_card_of_not_subset
    {p : ℕ} {A : Finset ℤ} (h0 : 0 ∈ A)
    (hnot : ¬ modImageF p A ⊆ modStabF p A) :
    3 * (modStabF p A).card ≤ (modSelfSumF p A).card := by
  have hsat := two_mul_modStab_card_le_modSat_card_of_not_subset h0 hnot
  have hk := modSat_kneser (p := p) A
  omega

lemma three_mul_modStab_card_le_modSelfSum_card_of_gcd_one_of_stab_ne_univ
    {p : ℕ} [NeZero p] {A : Finset ℤ}
    (h0 : 0 ∈ A) (hgcd : A.gcd id = 1)
    (hproper : modStabF p A ≠ Finset.univ) :
    3 * (modStabF p A).card ≤ (modSelfSumF p A).card := by
  have hAne : A.Nonempty := ⟨0, h0⟩
  exact three_mul_modStab_card_le_modSelfSum_card_of_not_subset h0
    (not_modImageF_subset_modStabF_of_gcd_one_of_stab_ne_univ hAne hgcd hproper)

lemma two_modSat_add_two_le_two_modImage_add_modStab_of_small_doubling
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    2 * (modSatF p A).card + 2 ≤
      2 * (modImageF p A).card + (modStabF p A).card := by
  have hlift := card_modSelfSum_add_card_le_sumset hp h0 htop
  have hk := modSat_kneser (p := p) A
  have hB := card_modImageF_normalized hp hAint h0 htop
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
  rw [hB]
  omega

lemma three_modStab_add_two_le_two_modImage_of_small_doubling_of_gcd_one
    {p : ℕ} [NeZero p] {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1) (hproper : modStabF p A ≠ Finset.univ)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    3 * (modStabF p A).card + 2 ≤ 2 * (modImageF p A).card := by
  have hlow := two_mul_modStab_card_le_modSat_card_of_gcd_one_of_stab_ne_univ
    h0 hgcd hproper
  have hupp := two_modSat_add_two_le_two_modImage_add_modStab_of_small_doubling
    hp hAint h0 htop hsmall
  omega

end Jsp000216

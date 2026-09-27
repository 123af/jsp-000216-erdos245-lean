import Jsp000216.HardBranch

open scoped Pointwise

namespace Jsp000216

/-- Sharp normalized finite `3k-4` interval bound: once the stable branch is
excluded, the ambient progression has at most `|A+A|-|A|+1` terms. -/
lemma normalized_small_doubling_interval_bound_sharp
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    (Finset.Icc 0 (p : ℤ)).card ≤ (A + A).card - A.card + 1 := by
  have hstable := normalized_small_doubling_stableHolesF_empty
    hp hAint h0 htop hgcd hsmall
  exact no_stable_interval_length_le_sumset_sub_card_add_one
    hAint h0 htop hstable

/-- Cardinal-free diameter form of the sharp normalized bound. -/
lemma normalized_small_doubling_diameter_bound_sharp
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    p + 1 ≤ (A + A).card - A.card + 1 := by
  have h := normalized_small_doubling_interval_bound_sharp
    hp hAint h0 htop hgcd hsmall
  simpa using h

end Jsp000216

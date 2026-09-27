import Jsp000216.ModInjective

open scoped Pointwise

namespace Jsp000216

lemma modImageF_eq_erase_top {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (h0 : 0 ∈ A) :
    modImageF p A = modImageF p (A.erase (p : ℤ)) := by
  unfold modImageF
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨x, hxA, hxz⟩
    by_cases hxp : x = (p : ℤ)
    · subst x
      refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
      · exact Finset.mem_erase.mpr ⟨by omega, h0⟩
      · simpa using hxz
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxp, hxA⟩, hxz⟩
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨x, hxA, hxz⟩
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_erase.mp hxA).2, hxz⟩

lemma card_modImageF_normalized {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hA : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A) :
    (modImageF p A).card = A.card - 1 := by
  rw [modImageF_eq_erase_top hp h0]
  rw [modImageF_erase_top_card hp hA]
  exact Finset.card_erase_of_mem htop

end Jsp000216

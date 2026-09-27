import Jsp000216.FiniteHoles

open scoped Pointwise

namespace Jsp000216

/-- Translation of a finite integer set by `n`. -/
def translateF (n : ℤ) (S : Finset ℤ) : Finset ℤ :=
  S.image fun x => n + x

@[simp] lemma mem_translateF {n y : ℤ} {S : Finset ℤ} :
    y ∈ translateF n S ↔ ∃ x ∈ S, n + x = y := by
  simp [translateF]

lemma card_translateF (n : ℤ) (S : Finset ℤ) :
    (translateF n S).card = S.card := by
  unfold translateF
  apply Finset.card_image_of_injective
  intro x y hxy
  exact add_left_cancel hxy

lemma subset_self_sumset_of_zero {A : Finset ℤ} (h0 : 0 ∈ A) :
    A ⊆ A + A := by
  intro x hx
  exact Finset.mem_add.mpr ⟨0, h0, x, hx, by simp⟩

lemma translate_subset_self_sumset_of_mem {A : Finset ℤ} {n : ℤ} (hn : n ∈ A) :
    translateF n A ⊆ A + A := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact Finset.mem_add.mpr ⟨n, hn, x, hx, rfl⟩

lemma lowerSumHolesF_subset_sumset {A : Finset ℤ} {n : ℤ} :
    lowerSumHolesF A n ⊆ A + A := by
  intro x hx
  exact (mem_lowerSumHolesF.mp hx).2

lemma translate_upperSumHolesF_subset_sumset {A : Finset ℤ} {n : ℤ} :
    translateF n (upperSumHolesF A n) ⊆ A + A := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact (mem_upperSumHolesF.mp hx).2

end Jsp000216

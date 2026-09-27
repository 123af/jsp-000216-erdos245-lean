import Mathlib
import Jsp000216.ModShadow

open scoped Pointwise

namespace Jsp000216

lemma intCast_zmod_injOn_Ico {p : ℕ} (hp : 0 < p) :
    Set.InjOn (fun x : ℤ => (x : ZMod p)) (Set.Ico 0 (p : ℤ)) := by
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hxp⟩
  rcases hy with ⟨hy0, hyp⟩
  have hdvd : (p : ℤ) ∣ y - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mp hxy
  have habs : |y - x| < (p : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

lemma modImageF_erase_top_card {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hA : A ⊆ Finset.Icc 0 (p : ℤ)) :
    (modImageF p (A.erase (p : ℤ))).card = (A.erase (p : ℤ)).card := by
  unfold modImageF
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
  have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
  have hxp : x ≠ (p : ℤ) := (Finset.mem_erase.mp hx).1
  have hyp : y ≠ (p : ℤ) := (Finset.mem_erase.mp hy).1
  have hxI := Finset.mem_Icc.mp (hA hxA)
  have hyI := Finset.mem_Icc.mp (hA hyA)
  apply intCast_zmod_injOn_Ico hp
  · exact ⟨hxI.1, by omega⟩
  · exact ⟨hyI.1, by omega⟩
  · exact hxy

end Jsp000216

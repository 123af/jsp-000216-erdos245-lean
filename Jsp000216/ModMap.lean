import Jsp000216.ModCard

open scoped Pointwise

namespace Jsp000216

lemma modImageF_add (p : ℕ) (A B : Finset ℤ) :
    modImageF p (A + B) = modImageF p A + modImageF p B := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, hsz⟩
    rcases Finset.mem_add.mp hs with ⟨a, ha, b, hb, rfl⟩
    apply Finset.mem_add.mpr
    refine ⟨(a : ZMod p), ?_, (b : ZMod p), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · simpa using hsz
  · intro hz
    rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, habz⟩
    rcases Finset.mem_image.mp ha with ⟨x, hx, hxa⟩
    rcases Finset.mem_image.mp hb with ⟨y, hy, hyb⟩
    apply Finset.mem_image.mpr
    refine ⟨x + y, Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
    rw [Int.cast_add, hxa, hyb]
    exact habz

lemma modSelfSumF_eq_modImageF_sumset (p : ℕ) (A : Finset ℤ) :
    modSelfSumF p A = modImageF p (A + A) := by
  rw [modSelfSumF, modImageF_add]

end Jsp000216

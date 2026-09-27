import Jsp000216.KneserBridge

open scoped Pointwise

namespace Jsp000216

/-- Reduction of a finite integer set modulo `p`. -/
def modImageF (p : ℕ) (A : Finset ℤ) : Finset (ZMod p) :=
  A.image (fun x : ℤ => (x : ZMod p))

/-- The reduced self-sum. -/
def modSelfSumF (p : ℕ) (A : Finset ℤ) : Finset (ZMod p) :=
  modImageF p A + modImageF p A

/-- The translation stabilizer of the reduced self-sum. -/
def modStabF (p : ℕ) (A : Finset ℤ) : Finset (ZMod p) :=
  (modSelfSumF p A).addStab

/-- Saturation of the reduced set by the self-sum stabilizer. -/
def modSatF (p : ℕ) (A : Finset ℤ) : Finset (ZMod p) :=
  modImageF p A + modStabF p A

lemma zero_mem_modImageF {p : ℕ} {A : Finset ℤ} (h0 : 0 ∈ A) :
    (0 : ZMod p) ∈ modImageF p A := by
  exact Finset.mem_image.mpr ⟨0, h0, by simp⟩

lemma modImageF_nonempty {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty) :
    (modImageF p A).Nonempty := by
  exact Finset.image_nonempty.mpr hA

lemma modSelfSumF_nonempty {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty) :
    (modSelfSumF p A).Nonempty := by
  exact (modImageF_nonempty hA).add (modImageF_nonempty hA)

lemma zero_mem_modStabF {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty) :
    (0 : ZMod p) ∈ modStabF p A := by
  exact Finset.zero_mem_addStab.mpr (modSelfSumF_nonempty hA)

lemma modImageF_subset_modSatF {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty) :
    modImageF p A ⊆ modSatF p A := by
  intro x hx
  exact Finset.mem_add.mpr ⟨x, hx, 0, zero_mem_modStabF hA, by simp⟩

lemma modSat_kneser {p : ℕ} (A : Finset ℤ) :
    2 * (modSatF p A).card ≤
      (modSelfSumF p A).card + (modStabF p A).card := by
  exact zmod_self_kneser (modImageF p A)

end Jsp000216

import Jsp000216.FiniteThreeK

open scoped Pointwise

namespace Jsp000216

/-- Cast a finite set of naturals into the integers. -/
def natToIntFinsetF (A : Finset ℕ) : Finset ℤ :=
  A.image fun n => (n : ℤ)

@[simp] lemma mem_natToIntFinsetF {A : Finset ℕ} {z : ℤ} :
    z ∈ natToIntFinsetF A ↔ ∃ n ∈ A, (n : ℤ) = z := by
  simp [natToIntFinsetF]

lemma card_natToIntFinsetF (A : Finset ℕ) :
    (natToIntFinsetF A).card = A.card := by
  rw [natToIntFinsetF, Finset.card_image_of_injective]
  exact Int.ofNat_injective

lemma natToIntFinsetF_add (A B : Finset ℕ) :
    natToIntFinsetF (A + B) = natToIntFinsetF A + natToIntFinsetF B := by
  ext z
  constructor
  · intro hz
    rcases mem_natToIntFinsetF.mp hz with ⟨n, hn, rfl⟩
    rcases Finset.mem_add.mp hn with ⟨a, ha, b, hb, hab⟩
    apply Finset.mem_add.mpr
    refine ⟨(a : ℤ), mem_natToIntFinsetF.mpr ⟨a, ha, rfl⟩,
      (b : ℤ), mem_natToIntFinsetF.mpr ⟨b, hb, rfl⟩, ?_⟩
    exact_mod_cast hab
  · intro hz
    rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, hab⟩
    rcases mem_natToIntFinsetF.mp ha with ⟨x, hx, hxa⟩
    rcases mem_natToIntFinsetF.mp hb with ⟨y, hy, hyb⟩
    apply mem_natToIntFinsetF.mpr
    refine ⟨x + y, Finset.add_mem_add hx hy, ?_⟩
    rw [← hab, ← hxa, ← hyb]
    norm_num

lemma card_add_natToIntFinsetF (A B : Finset ℕ) :
    (natToIntFinsetF A + natToIntFinsetF B).card = (A + B).card := by
  rw [← natToIntFinsetF_add, card_natToIntFinsetF]

lemma natCast_mem_natToIntFinsetF {A : Finset ℕ} {n : ℕ} (hn : n ∈ A) :
    (n : ℤ) ∈ natToIntFinsetF A :=
  mem_natToIntFinsetF.mpr ⟨n, hn, rfl⟩

end Jsp000216

import Jsp000216.ModMap
import Jsp000216.FiniteTranslate
import Jsp000216.TrivialStab

open scoped Pointwise

namespace Jsp000216

/-- The sums in `A+A` reducing to a prescribed residue modulo `p`. -/
def modFiberSumF (p : ℕ) (A : Finset ℤ) (c : ZMod p) : Finset ℤ :=
  (A + A).filter fun z => (z : ZMod p) = c

@[simp] lemma mem_modFiberSumF {p : ℕ} {A : Finset ℤ} {c : ZMod p} {z : ℤ} :
    z ∈ modFiberSumF p A c ↔ z ∈ A + A ∧ (z : ZMod p) = c := by
  simp [modFiberSumF]

lemma modFiberSumF_nonempty {p : ℕ} {A : Finset ℤ} {c : ZMod p}
    (hc : c ∈ modSelfSumF p A) : (modFiberSumF p A c).Nonempty := by
  have hc' : c ∈ modImageF p (A + A) := by
    rw [← modSelfSumF_eq_modImageF_sumset]
    exact hc
  rcases Finset.mem_image.mp hc' with ⟨z, hz, hzc⟩
  exact ⟨z, mem_modFiberSumF.mpr ⟨hz, hzc⟩⟩

/-- Least actual sum representing a residue of the reduced self-sum. -/
noncomputable def residueRepF (p : ℕ) (A : Finset ℤ)
    (c : ↑(modSelfSumF p A)) : ℤ :=
  (modFiberSumF p A c.1).min' (modFiberSumF_nonempty c.2)

lemma residueRepF_mem (p : ℕ) (A : Finset ℤ) (c : ↑(modSelfSumF p A)) :
    residueRepF p A c ∈ A + A := by
  exact (mem_modFiberSumF.mp
    ((modFiberSumF p A c.1).min'_mem (modFiberSumF_nonempty c.2))).1

lemma residueRepF_cast (p : ℕ) (A : Finset ℤ) (c : ↑(modSelfSumF p A)) :
    ((residueRepF p A c : ℤ) : ZMod p) = c.1 := by
  exact (mem_modFiberSumF.mp
    ((modFiberSumF p A c.1).min'_mem (modFiberSumF_nonempty c.2))).2

lemma residueRepF_le {p : ℕ} {A : Finset ℤ} (c : ↑(modSelfSumF p A))
    {z : ℤ} (hz : z ∈ A + A) (hzc : (z : ZMod p) = c.1) :
    residueRepF p A c ≤ z := by
  apply (modFiberSumF p A c.1).min'_le z
  exact mem_modFiberSumF.mpr ⟨hz, hzc⟩

lemma residueRepF_injective (p : ℕ) (A : Finset ℤ) :
    Function.Injective (residueRepF p A) := by
  intro c d hcd
  apply Subtype.ext
  rw [← residueRepF_cast p A c, ← residueRepF_cast p A d, hcd]

/-- One least integer lift for each residue occurring in `A+A`. -/
noncomputable def residueRepsF (p : ℕ) (A : Finset ℤ) : Finset ℤ :=
  (modSelfSumF p A).attach.image (residueRepF p A)

lemma card_residueRepsF (p : ℕ) (A : Finset ℤ) :
    (residueRepsF p A).card = (modSelfSumF p A).card := by
  rw [residueRepsF, Finset.card_image_of_injective _ (residueRepF_injective p A)]
  simp

lemma residueRepsF_subset_sumset (p : ℕ) (A : Finset ℤ) :
    residueRepsF p A ⊆ A + A := by
  intro z hz
  simp only [residueRepsF, Finset.mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact residueRepF_mem p A c

lemma cast_mem_modSelfSumF_of_mem {p : ℕ} {A : Finset ℤ} {a : ℤ}
    (h0 : 0 ∈ A) (ha : a ∈ A) :
    (a : ZMod p) ∈ modSelfSumF p A := by
  rw [modSelfSumF_eq_modImageF_sumset]
  exact Finset.mem_image.mpr ⟨a, by simpa using Finset.add_mem_add ha h0, rfl⟩

lemma residueRepsF_disjoint_translate {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (h0 : 0 ∈ A) :
    Disjoint (residueRepsF p A) (translateF (p : ℤ) A) := by
  refine Finset.disjoint_left.mpr ?_
  intro z hzR hzE
  simp only [residueRepsF, Finset.mem_image] at hzR
  obtain ⟨c, -, hcz⟩ := hzR
  rcases mem_translateF.mp hzE with ⟨a, ha, haz⟩
  let ca : ↑(modSelfSumF p A) :=
    ⟨(a : ZMod p), cast_mem_modSelfSumF_of_mem h0 ha⟩
  have hcast : c.1 = ca.1 := by
    calc
      c.1 = ((residueRepF p A c : ℤ) : ZMod p) := (residueRepF_cast p A c).symm
      _ = (z : ZMod p) := by rw [hcz]
      _ = (a : ZMod p) := by rw [← haz]; simp
      _ = ca.1 := rfl
  have hca : c = ca := Subtype.ext hcast
  have hsum : a ∈ A + A := by simpa using Finset.add_mem_add ha h0
  have hle : residueRepF p A ca ≤ a := residueRepF_le ca hsum rfl
  rw [hca] at hcz
  dsimp [ca] at hle hcz
  omega

lemma card_modSelfSum_add_card_le_sumset {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A) :
    (modSelfSumF p A).card + A.card ≤ (A + A).card := by
  have hR : residueRepsF p A ⊆ A + A := residueRepsF_subset_sumset p A
  have hE : translateF (p : ℤ) A ⊆ A + A := translate_subset_self_sumset_of_mem htop
  have hdisj := residueRepsF_disjoint_translate hp h0
  rw [← card_residueRepsF p A, ← card_translateF (p : ℤ) A,
    ← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card (Finset.union_subset hR hE)

/-- In the normalized small-doubling setup, the modular self-sum stabilizer
cannot be the trivial subgroup `{0}`. -/
lemma normalized_small_doubling_mod_stabilizer_nontrivial
    {p : ℕ} {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    modStabF p A ≠ {0} := by
  intro htriv
  have hstab : (modStabF p A).card = 1 := by
    rw [htriv]
    simp
  have hlow := modSelfSum_card_ge_two_card_sub_three_of_stab_card_one
    hp hAint h0 htop hstab
  have hlift := card_modSelfSum_add_card_le_sumset hp h0 htop
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

end Jsp000216

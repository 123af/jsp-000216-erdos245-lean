import Jsp000216.StableMod

open scoped Pointwise

namespace Jsp000216

/-- Least actual sum representing a modular self-sum residue outside `D`. -/
noncomputable def residueRepOutsideF (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) (c : ↑(modSelfSumF p A \ D)) : ℤ :=
  residueRepF p A ⟨c.1, (Finset.mem_sdiff.mp c.2).1⟩

/-- One least actual sum for every modular self-sum residue outside `D`. -/
noncomputable def residueRepsOutsideF (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) : Finset ℤ :=
  (modSelfSumF p A \ D).attach.image (residueRepOutsideF p A D)

lemma residueRepOutsideF_mem (p : ℕ) (A : Finset ℤ) (D : Finset (ZMod p))
    (c : ↑(modSelfSumF p A \ D)) :
    residueRepOutsideF p A D c ∈ A + A := by
  exact residueRepF_mem p A ⟨c.1, (Finset.mem_sdiff.mp c.2).1⟩

lemma residueRepOutsideF_cast (p : ℕ) (A : Finset ℤ) (D : Finset (ZMod p))
    (c : ↑(modSelfSumF p A \ D)) :
    ((residueRepOutsideF p A D c : ℤ) : ZMod p) = c.1 := by
  exact residueRepF_cast p A ⟨c.1, (Finset.mem_sdiff.mp c.2).1⟩

lemma residueRepOutsideF_injective (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) : Function.Injective (residueRepOutsideF p A D) := by
  intro c e hce
  apply Subtype.ext
  rw [← residueRepOutsideF_cast p A D c,
    ← residueRepOutsideF_cast p A D e, hce]

lemma card_residueRepsOutsideF (p : ℕ) (A : Finset ℤ) (D : Finset (ZMod p)) :
    (residueRepsOutsideF p A D).card = (modSelfSumF p A \ D).card := by
  rw [residueRepsOutsideF,
    Finset.card_image_of_injective _ (residueRepOutsideF_injective p A D)]
  simp

lemma residueRepsOutsideF_subset_sumset (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) : residueRepsOutsideF p A D ⊆ A + A := by
  intro z hz
  simp only [residueRepsOutsideF, Finset.mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact residueRepOutsideF_mem p A D c

lemma residueRepsOutsideF_subset_residueRepsF (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) : residueRepsOutsideF p A D ⊆ residueRepsF p A := by
  intro z hz
  simp only [residueRepsOutsideF, residueRepsF, Finset.mem_image] at hz ⊢
  obtain ⟨c, -, rfl⟩ := hz
  let c' : ↑(modSelfSumF p A) := ⟨c.1, (Finset.mem_sdiff.mp c.2).1⟩
  exact ⟨c', Finset.mem_attach _ c', rfl⟩

lemma cast_not_mem_of_mem_residueRepsOutsideF
    {p : ℕ} {A : Finset ℤ} {D : Finset (ZMod p)} {z : ℤ}
    (hz : z ∈ residueRepsOutsideF p A D) : (z : ZMod p) ∉ D := by
  simp only [residueRepsOutsideF, Finset.mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  rw [residueRepOutsideF_cast]
  exact (Finset.mem_sdiff.mp c.2).2

/-- Actual sums whose residues lie in `D`. -/
def sumsetOverResiduesF (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) : Finset ℤ :=
  (A + A).filter fun z => (z : ZMod p) ∈ D

@[simp] lemma mem_sumsetOverResiduesF
    {p : ℕ} {A : Finset ℤ} {D : Finset (ZMod p)} {z : ℤ} :
    z ∈ sumsetOverResiduesF p A D ↔ z ∈ A + A ∧ (z : ZMod p) ∈ D := by
  simp [sumsetOverResiduesF]

/-- Self-sum specialization of Ruzsa's refined modular lift count.
Besides one least representative outside `D`, keep `p + A` and every
actual sum whose residue lies in `D`.  If `D` misses the residues of `A`,
these three collections are pairwise disjoint. -/
lemma card_modSelfSum_add_card_add_fiber_le
    {p : ℕ} {A : Finset ℤ} (D : Finset (ZMod p))
    (hp : 0 < p) (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hD : D ⊆ modSelfSumF p A)
    (hDB : Disjoint D (modImageF p A)) :
    (modSelfSumF p A).card + A.card + (sumsetOverResiduesF p A D).card ≤
      (A + A).card + D.card := by
  let R := residueRepsOutsideF p A D
  let E := translateF (p : ℤ) A
  let F := sumsetOverResiduesF p A D
  have hRS : R ⊆ A + A := residueRepsOutsideF_subset_sumset p A D
  have hES : E ⊆ A + A := translate_subset_self_sumset_of_mem htop
  have hFS : F ⊆ A + A := Finset.filter_subset _ _
  have hRE : Disjoint R E := by
    exact (residueRepsF_disjoint_translate hp h0).mono_left
      (residueRepsOutsideF_subset_residueRepsF p A D)
  have hRF : Disjoint R F := by
    rw [Finset.disjoint_left]
    intro z hzR hzF
    exact (cast_not_mem_of_mem_residueRepsOutsideF hzR)
      (mem_sumsetOverResiduesF.mp hzF).2
  have hEF : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro z hzE hzF
    rcases mem_translateF.mp hzE with ⟨a, ha, haz⟩
    have haD : (a : ZMod p) ∈ D := by
      have hzD := (mem_sumsetOverResiduesF.mp hzF).2
      rw [← haz] at hzD
      simpa using hzD
    have haB : (a : ZMod p) ∈ modImageF p A :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    exact (Finset.disjoint_left.mp hDB) haD haB
  have hREF : Disjoint (R ∪ E) F := by
    rw [Finset.disjoint_left]
    intro z hz hzF
    rcases Finset.mem_union.mp hz with hzR | hzE
    · exact (Finset.disjoint_left.mp hRF) hzR hzF
    · exact (Finset.disjoint_left.mp hEF) hzE hzF
  have hU : (R ∪ E) ∪ F ⊆ A + A :=
    Finset.union_subset (Finset.union_subset hRS hES) hFS
  have hcardU := Finset.card_le_card hU
  rw [Finset.card_union_of_disjoint hREF,
    Finset.card_union_of_disjoint hRE,
    card_residueRepsOutsideF, card_translateF] at hcardU
  have hsplit := Finset.card_sdiff_add_card_eq_card hD
  change (modSelfSumF p A \ D).card + D.card = (modSelfSumF p A).card at hsplit
  dsimp [R, E, F] at hcardU
  change (modSelfSumF p A).card + A.card + (sumsetOverResiduesF p A D).card ≤
    (A + A).card + D.card
  omega

end Jsp000216

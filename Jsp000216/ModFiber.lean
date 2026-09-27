import Jsp000216.RefinedLift

open Finset
open scoped Pointwise

namespace Jsp000216

/-- Elements of `A` whose residues lie in a prescribed modular set. -/
def residueFiberSetF (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) : Finset ℤ :=
  A.filter fun z => (z : ZMod p) ∈ D

@[simp] lemma mem_residueFiberSetF
    {p : ℕ} {A : Finset ℤ} {D : Finset (ZMod p)} {z : ℤ} :
    z ∈ residueFiberSetF p A D ↔ z ∈ A ∧ (z : ZMod p) ∈ D := by
  simp [residueFiberSetF]

lemma modImageF_residueFiberSetF (p : ℕ) (A : Finset ℤ)
    (D : Finset (ZMod p)) :
    modImageF p (residueFiberSetF p A D) = modImageF p A ∩ D := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨z, hz, hzc⟩
    have hz' := mem_residueFiberSetF.mp hz
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨z, hz'.1, hzc⟩, by simpa [hzc] using hz'.2⟩
  · intro hc
    have hc' := Finset.mem_inter.mp hc
    rcases Finset.mem_image.mp hc'.1 with ⟨z, hz, hzc⟩
    exact Finset.mem_image.mpr
      ⟨z, mem_residueFiberSetF.mpr ⟨hz, by simpa [hzc] using hc'.2⟩, hzc⟩

lemma card_modImageF_le (p : ℕ) (A : Finset ℤ) :
    (modImageF p A).card ≤ A.card := by
  unfold modImageF
  exact Finset.card_image_le

/-- Saturating the modular image by `H` fills the coset through any occupied
residue; the overlap with that coset is paid for by the corresponding
integer fiber of `A`. -/
lemma card_modImage_add_card_le_saturation_add_fiberF
    {p : ℕ} {A : Finset ℤ} {H : Finset (ZMod p)} {a : ZMod p}
    (h0 : (0 : ZMod p) ∈ H) (ha : a ∈ modImageF p A) :
    (modImageF p A).card + H.card ≤
      (modImageF p A + H).card +
        (residueFiberSetF p A (a +ᵥ H)).card := by
  let X := modImageF p A
  let D := a +ᵥ H
  have hX : X ⊆ X + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, h0, by simp⟩
  have hD : D ⊆ X + H := by
    intro z hz
    rcases Finset.mem_vadd_finset.mp hz with ⟨h, hh, hhz⟩
    exact Finset.mem_add.mpr ⟨a, ha, h, hh, hhz⟩
  have hU : X ∪ D ⊆ X + H := Finset.union_subset hX hD
  have hinter : (X ∩ D).card ≤ (residueFiberSetF p A D).card := by
    rw [← modImageF_residueFiberSetF]
    exact card_modImageF_le p (residueFiberSetF p A D)
  have hcardU := Finset.card_le_card hU
  have hcardD : D.card = H.card := Finset.card_vadd_finset a H
  have hIE := Finset.card_union_add_card_inter X D
  change X.card + H.card ≤ (X + H).card + (residueFiberSetF p A D).card
  omega

lemma modStabF_add_mem {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty)
    {x y : ZMod p} (hx : x ∈ modStabF p A) (hy : y ∈ modStabF p A) :
    x + y ∈ modStabF p A := by
  change x + y ∈ (modSelfSumF p A).addStab
  change x ∈ (modSelfSumF p A).addStab at hx
  change y ∈ (modSelfSumF p A).addStab at hy
  rw [← Finset.mem_coe, Finset.coe_addStab (modSelfSumF_nonempty hA)] at hx hy ⊢
  exact (AddAction.stabilizer (ZMod p) ((modSelfSumF p A : Finset (ZMod p)) : Set (ZMod p))).add_mem hx hy

lemma modStabF_neg_mem {p : ℕ} {A : Finset ℤ} (hA : A.Nonempty)
    {x : ZMod p} (hx : x ∈ modStabF p A) : -x ∈ modStabF p A := by
  change -x ∈ (modSelfSumF p A).addStab
  change x ∈ (modSelfSumF p A).addStab at hx
  rw [← Finset.mem_coe, Finset.coe_addStab (modSelfSumF_nonempty hA)] at hx ⊢
  exact (AddAction.stabilizer (ZMod p) ((modSelfSumF p A : Finset (ZMod p)) : Set (ZMod p))).neg_mem hx

lemma disjoint_vadd_add_of_closed_not_memF
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X H : Finset G} {c : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hc : c ∉ X + H) :
    Disjoint (c +ᵥ H) (X + H) := by
  rw [Finset.disjoint_left]
  intro z hzD hzX
  rcases Finset.mem_vadd_finset.mp hzD with ⟨h₂, hh₂, hh₂z⟩
  rcases Finset.mem_add.mp hzX with ⟨x, hx, h₁, hh₁, hh₁z⟩
  change c + h₂ = z at hh₂z
  apply hc
  apply Finset.mem_add.mpr
  refine ⟨x, hx, h₁ + -h₂, hadd h₁ hh₁ (-h₂) (hneg h₂ hh₂), ?_⟩
  calc
    x + (h₁ + -h₂) = (x + h₁) + -h₂ := by abel
    _ = z + -h₂ := by rw [hh₁z]
    _ = (c + h₂) + -h₂ := by rw [hh₂z]
    _ = c := by abel

lemma residueFiberSetF_add_subset_sumsetOverResiduesF
    {p : ℕ} {A : Finset ℤ} {H : Finset (ZMod p)} {a b c : ZMod p}
    (hc : a + b = c)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) :
    residueFiberSetF p A (a +ᵥ H) + residueFiberSetF p A (b +ᵥ H) ⊆
      sumsetOverResiduesF p A (c +ᵥ H) := by
  intro z hz
  rcases Finset.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
  have hx' := mem_residueFiberSetF.mp hx
  have hy' := mem_residueFiberSetF.mp hy
  rcases Finset.mem_vadd_finset.mp hx'.2 with ⟨h₁, hh₁, ha⟩
  rcases Finset.mem_vadd_finset.mp hy'.2 with ⟨h₂, hh₂, hb⟩
  change a + h₁ = (x : ZMod p) at ha
  change b + h₂ = (y : ZMod p) at hb
  apply mem_sumsetOverResiduesF.mpr
  constructor
  · exact Finset.add_mem_add hx'.1 hy'.1
  · apply Finset.mem_vadd_finset.mpr
    refine ⟨h₁ + h₂, hadd h₁ hh₁ h₂ hh₂, ?_⟩
    change c + (h₁ + h₂) = ((x + y : ℤ) : ZMod p)
    push_cast
    rw [← ha, ← hb, ← hc]
    abel

end Jsp000216

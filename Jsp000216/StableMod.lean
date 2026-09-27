import Jsp000216.ModSat
import Jsp000216.NoStable

open scoped Pointwise

namespace Jsp000216

/-- A stable interval hole gives a residue which is absent from the reduced self-sum. -/
lemma stableHole_not_mem_modSelfSumF
    {p : ℕ} {A : Finset ℤ} {x : ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hx : x ∈ stableHolesF A (p : ℤ)) :
    (x : ZMod p) ∉ modSelfSumF p A := by
  have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hxI : x ∈ intervalHolesF A (p : ℤ) := (Finset.mem_sdiff.mp hx).1
  have hxLU : x ∉ lowerSumHolesF A (p : ℤ) ∪ upperSumHolesF A (p : ℤ) :=
    (Finset.mem_sdiff.mp hx).2
  have hxL : x ∉ lowerSumHolesF A (p : ℤ) := by
    intro h
    exact hxLU (Finset.mem_union_left _ h)
  have hxU : x ∉ upperSumHolesF A (p : ℤ) := by
    intro h
    exact hxLU (Finset.mem_union_right _ h)
  have hxnotlow : x ∉ A + A := by
    intro h
    exact hxL (mem_lowerSumHolesF.mpr ⟨hxI, h⟩)
  have hxnotup : (p : ℤ) + x ∉ A + A := by
    intro h
    exact hxU (mem_upperSumHolesF.mpr ⟨hxI, h⟩)
  have hxIb := mem_intervalHolesF.mp hxI
  have hxnotA : x ∉ A := hxIb.2.2
  have hxne0 : x ≠ 0 := by
    intro h
    subst x
    exact hxnotA h0
  have hxnep : x ≠ (p : ℤ) := by
    intro h
    subst x
    exact hxnotA htop
  have hxpos : 0 < x := by omega
  have hxlt : x < (p : ℤ) := by omega
  intro hres
  rw [modSelfSumF_eq_modImageF_sumset] at hres
  rcases Finset.mem_image.mp hres with ⟨z, hz, hzx⟩
  rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, habz⟩
  have haI := Finset.mem_Icc.mp (hAint ha)
  have hbI := Finset.mem_Icc.mp (hAint hb)
  have hz0 : 0 ≤ z := by omega
  have hz2 : z ≤ 2 * (p : ℤ) := by omega
  have hzlt2 : z < 2 * (p : ℤ) := by
    by_contra h
    have hzeq : z = 2 * (p : ℤ) := by omega
    have hcast0 : ((0 : ℤ) : ZMod p) = (x : ZMod p) := by
      rw [hzeq] at hzx
      simpa using hzx
    have h0x : (0 : ℤ) = x :=
      intCast_zmod_injOn_Ico hp ⟨le_rfl, hpz⟩ ⟨le_of_lt hxpos, hxlt⟩ hcast0
    omega
  by_cases hzlt : z < (p : ℤ)
  · have hzx' : z = x :=
      intCast_zmod_injOn_Ico hp ⟨hz0, hzlt⟩ ⟨le_of_lt hxpos, hxlt⟩ hzx
    rw [hzx'] at hz
    exact hxnotlow hz
  · have hzp : (p : ℤ) ≤ z := by omega
    have hy0 : 0 ≤ z - (p : ℤ) := by omega
    have hylt : z - (p : ℤ) < (p : ℤ) := by omega
    have hycast : ((z - (p : ℤ) : ℤ) : ZMod p) = (x : ZMod p) := by
      calc
        ((z - (p : ℤ) : ℤ) : ZMod p) = (z : ZMod p) := by
          push_cast
          simp
        _ = (x : ZMod p) := hzx
    have hyx : z - (p : ℤ) = x :=
      intCast_zmod_injOn_Ico hp ⟨hy0, hylt⟩ ⟨le_of_lt hxpos, hxlt⟩ hycast
    have hzeq : z = (p : ℤ) + x := by omega
    rw [hzeq] at hz
    exact hxnotup hz

lemma modSelfSumF_ne_univ_of_stableHolesF_nonempty
    {p : ℕ} [NeZero p] {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hstable : (stableHolesF A (p : ℤ)).Nonempty) :
    modSelfSumF p A ≠ Finset.univ := by
  rcases hstable with ⟨x, hx⟩
  have hxnot := stableHole_not_mem_modSelfSumF hp hAint h0 htop hx
  intro h
  apply hxnot
  rw [h]
  simp

lemma modStabF_ne_univ_of_stableHolesF_nonempty
    {p : ℕ} [NeZero p] {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hstable : (stableHolesF A (p : ℤ)).Nonempty) :
    modStabF p A ≠ Finset.univ := by
  have hCne := modSelfSumF_ne_univ_of_stableHolesF_nonempty hp hAint h0 htop hstable
  intro hHuniv
  have hSatuniv : modSatF p A = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro z
    exact Finset.mem_add.mpr
      ⟨0, zero_mem_modImageF h0, z, by simpa [hHuniv], by simp⟩
  have hk := modSat_kneser (p := p) A
  rw [hSatuniv, hHuniv] at hk
  have hle : (Finset.univ : Finset (ZMod p)).card ≤ (modSelfSumF p A).card := by
    omega
  have hge : (modSelfSumF p A).card ≤ (Finset.univ : Finset (ZMod p)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have hcard : (modSelfSumF p A).card = Fintype.card (ZMod p) := by
    rw [← Finset.card_univ]
    exact Nat.le_antisymm hge hle
  exact hCne (Finset.eq_univ_of_card (modSelfSumF p A) hcard)

/-- The exact modular structure forced by the remaining stable-hole branch. -/
lemma stable_hard_branch_modular_structure
    {p : ℕ} [NeZero p] {A : Finset ℤ}
    (hp : 0 < p) (hAint : A ⊆ Finset.Icc 0 (p : ℤ))
    (h0 : 0 ∈ A) (htop : (p : ℤ) ∈ A)
    (hgcd : A.gcd id = 1)
    (hsmall : (A + A).card ≤ 3 * A.card - 4)
    (hstable : (stableHolesF A (p : ℤ)).Nonempty) :
    modStabF p A ≠ {0} ∧
      modStabF p A ≠ Finset.univ ∧
      ¬ modImageF p A ⊆ modStabF p A := by
  have hnontriv := normalized_small_doubling_mod_stabilizer_nontrivial
    hp hAint h0 htop hsmall
  have hproper := modStabF_ne_univ_of_stableHolesF_nonempty
    hp hAint h0 htop hstable
  have hAne : A.Nonempty := ⟨0, h0⟩
  have hnot := not_modImageF_subset_modStabF_of_gcd_one_of_stab_ne_univ
    hAne hgcd hproper
  exact ⟨hnontriv, hproper, hnot⟩

end Jsp000216

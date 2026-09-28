import Jsp000216.ChainDeterminant

open scoped BigOperators

namespace Jsp000216

/-- Nonzero support of a rational coefficient family. -/
def supportNZF {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) : Finset ι :=
  Finset.univ.filter fun i => a i ≠ 0

@[simp] lemma mem_supportNZF {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (i : ι) : i ∈ supportNZF a ↔ a i ≠ 0 := by
  simp [supportNZF]

/-- Any finite nonnegative rational combination admits an equivalent
nonnegative representation whose nonzero vectors are linearly independent.
The proof chooses a representation of minimal support and eliminates a
positive direction from any hypothetical dependence. -/
theorem exists_nonnegative_independent_support
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (w : ι → V) (a : ι → ℚ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℚ,
      (∀ i, 0 ≤ b i) ∧
      (∑ i, b i • w i) = ∑ i, a i • w i ∧
      LinearIndependent ℚ (fun i : ↥(supportNZF b) => w i.1) := by
  classical
  let target : V := ∑ i, a i • w i
  let Good : ℕ → Prop := fun n =>
    ∃ b : ι → ℚ, (∀ i, 0 ≤ b i) ∧
      (∑ i, b i • w i) = target ∧ (supportNZF b).card = n
  have hGood : ∃ n, Good n := by
    refine ⟨(supportNZF a).card, a, ha, rfl, rfl⟩
  let n := Nat.find hGood
  obtain ⟨b, hb, hbsum, hbcard⟩ := Nat.find_spec hGood
  refine ⟨b, hb, by simpa [target] using hbsum, ?_⟩
  by_contra hdep
  obtain ⟨g, hg, i₀, hi₀⟩ :=
    Fintype.not_linearIndependent_iff.mp hdep
  let g' : ↥(supportNZF b) → ℚ :=
    if 0 < g i₀ then g else -g
  have hg'sum : ∑ i, g' i • w i.1 = 0 := by
    by_cases hpos : 0 < g i₀
    · simpa [g', hpos] using hg
    · have hneg : g i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
      simpa [g', hpos] using congrArg Neg.neg hg
  have hi₀pos : 0 < g' i₀ := by
    by_cases hpos : 0 < g i₀
    · simp [g', hpos]
    · have hneg : g i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
      simp [g', hpos, hneg]
  let P : Finset ↥(supportNZF b) := Finset.univ.filter fun i => 0 < g' i
  have hP : P.Nonempty := by
    refine ⟨i₀, ?_⟩
    simp [P, hi₀pos]
  let R : Finset ℚ := P.image fun i => b i.1 / g' i
  have hR : R.Nonempty := hP.image _
  let t : ℚ := R.min' hR
  obtain ⟨iMin, hiMinP, htEq⟩ := Finset.mem_image.mp (R.min'_mem hR)
  have hiMinG : 0 < g' iMin := (Finset.mem_filter.mp hiMinP).2
  have hiMinB : 0 < b iMin.1 := by
    have hne : b iMin.1 ≠ 0 := (mem_supportNZF b iMin.1).mp iMin.2
    exact lt_of_le_of_ne (hb iMin.1) (Ne.symm hne)
  have htpos : 0 < t := by
    change 0 < R.min' hR
    rw [← htEq]
    exact div_pos hiMinB hiMinG
  let gFull : ι → ℚ := fun i =>
    if hi : i ∈ supportNZF b then g' ⟨i, hi⟩ else 0
  have hgFull : ∑ i, gFull i • w i = 0 := by
    calc
      ∑ i, gFull i • w i = ∑ i ∈ supportNZF b, gFull i • w i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hi
        have hbi : b i = 0 := not_ne_iff.mp (mt (mem_supportNZF b i).mpr hi)
        simp [gFull, hbi]
      _ = ∑ i : ↥(supportNZF b), g' i • w i.1 := by
        rw [← (supportNZF b).sum_attach]
        apply Finset.sum_congr rfl
        intro i hi
        have hbi : b i.1 ≠ 0 := (mem_supportNZF b i.1).mp i.2
        simp [gFull, hbi]
      _ = 0 := hg'sum
  let b' : ι → ℚ := fun i => b i - t * gFull i
  have hb' : ∀ i, 0 ≤ b' i := by
    intro i
    by_cases hi : i ∈ supportNZF b
    · let ii : ↥(supportNZF b) := ⟨i, hi⟩
      have hbi0 : b i ≠ 0 := (mem_supportNZF b i).mp hi
      by_cases hgpos : 0 < g' ii
      · have hiP : ii ∈ P := by simp [P, hgpos]
        have hratio : t ≤ b i / g' ii := by
          apply Finset.min'_le R
          exact Finset.mem_image.mpr ⟨ii, hiP, rfl⟩
        have hmul : t * g' ii ≤ b i :=
          (le_div_iff₀ hgpos).mp hratio
        simpa [b', gFull, hi, hbi0, ii] using sub_nonneg.mpr hmul
      · have hgle : g' ii ≤ 0 := le_of_not_gt hgpos
        have htg : t * g' ii ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hgle
        have hnonneg : 0 ≤ b i - t * g' ii := sub_nonneg.mpr (htg.trans (hb i))
        simpa [b', gFull, hi, hbi0, ii] using hnonneg
    · have hbi : b i = 0 := not_ne_iff.mp (mt (mem_supportNZF b i).mpr hi)
      simp [b', gFull, hbi]
  have hb'sum : (∑ i, b' i • w i) = ∑ i, b i • w i := by
    simp only [b', sub_smul, mul_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hgFull, smul_zero, sub_zero]
  have hsupport : supportNZF b' ⊆ supportNZF b := by
    intro i hi'
    by_contra hi
    have hbi : b i = 0 := not_ne_iff.mp (mt (mem_supportNZF b i).mpr hi)
    have hzero : b' i = 0 := by simp [b', gFull, hbi]
    exact (mem_supportNZF b' i).mp hi' hzero
  have hiMinZero : b' iMin.1 = 0 := by
    have ht : t = b iMin.1 / g' iMin := htEq.symm
    simp only [b', gFull, iMin.2, dite_true, ht]
    rw [div_mul_cancel₀ _ hiMinG.ne']
    exact sub_self _
  have hproper : supportNZF b' ⊂ supportNZF b := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupport, ?_⟩
    intro heq
    have hi' : iMin.1 ∈ supportNZF b' := by
      rw [heq]
      exact iMin.2
    exact (mem_supportNZF b' iMin.1).mp hi' hiMinZero
  have hcardlt : (supportNZF b').card < (supportNZF b).card :=
    Finset.card_lt_card hproper
  have hminimal : n ≤ (supportNZF b').card := by
    apply Nat.find_min' hGood
    refine ⟨b', hb', ?_, rfl⟩
    exact hb'sum.trans hbsum
  rw [hbcard] at hcardlt
  omega

end Jsp000216

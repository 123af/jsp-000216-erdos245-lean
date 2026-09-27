import Jsp000216.ResidueLift

open scoped Pointwise

namespace Jsp000216

/-- If the integer gcd of `A` is one and every residue of `A` lies in an
additive subgroup of `ZMod p`, then that subgroup is the whole group. -/
lemma zmod_subgroup_eq_top_of_gcd_one {p : ℕ} {A : Finset ℤ}
    (hgcd : A.gcd id = 1) (K : AddSubgroup (ZMod p))
    (hA : ∀ a ∈ A, (a : ZMod p) ∈ K) : K = ⊤ := by
  classical
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul A id
  have hterms : ∀ a ∈ A, (a : ZMod p) * (g a : ZMod p) ∈ K := by
    intro a ha
    have haK := hA a ha
    have hz := K.zsmul_mem haK (g a)
    simpa [smul_eq_mul, mul_comm] using hz
  have hsum : ((∑ a ∈ A, a * g a : ℤ) : ZMod p) ∈ K := by
    simpa only [Int.cast_sum, Int.cast_mul] using
      (K.sum_mem fun a ha => hterms a ha)
  have hone : (1 : ZMod p) ∈ K := by
    rw [hgcd] at hg
    have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hg
    norm_num at hcast
    rw [← hcast] at hsum
    exact hsum
  apply (AddSubgroup.eq_top_iff' K).mpr
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
  rw [← hz]
  simpa [smul_eq_mul] using K.zsmul_mem hone z

/-- If all residues of `A` lie in the stabilizer of its reduced self-sum and
`gcd(A)=1`, that stabilizer is all of `ZMod p`. -/
lemma modStabF_eq_univ_of_gcd_one_of_image_subset
    {p : ℕ} [NeZero p] {A : Finset ℤ} (hAne : A.Nonempty)
    (hgcd : A.gcd id = 1)
    (hsub : modImageF p A ⊆ modStabF p A) :
    modStabF p A = Finset.univ := by
  classical
  let K : AddSubgroup (ZMod p) :=
    AddAction.stabilizer (ZMod p) ((modSelfSumF p A : Finset (ZMod p)) : Set (ZMod p))
  have hHK : (↑(modStabF p A) : Set (ZMod p)) = (K : Set (ZMod p)) := by
    change (↑((modSelfSumF p A).addStab) : Set (ZMod p)) = _
    simpa [K] using Finset.coe_addStab (modSelfSumF_nonempty hAne)
  have hAK : ∀ a ∈ A, (a : ZMod p) ∈ K := by
    intro a ha
    have haB : (a : ZMod p) ∈ modImageF p A := by
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have haH : (a : ZMod p) ∈ modStabF p A := hsub haB
    have haHs : (a : ZMod p) ∈ (↑(modStabF p A) : Set (ZMod p)) := haH
    rw [hHK] at haHs
    exact haHs
  have hKtop := zmod_subgroup_eq_top_of_gcd_one hgcd K hAK
  ext x
  simp only [Finset.mem_univ, iff_true]
  have hxK : x ∈ K := by
    rw [hKtop]
    trivial
  have hxKs : x ∈ (K : Set (ZMod p)) := hxK
  rw [← hHK] at hxKs
  exact hxKs

lemma not_modImageF_subset_modStabF_of_gcd_one_of_stab_ne_univ
    {p : ℕ} [NeZero p] {A : Finset ℤ} (hAne : A.Nonempty)
    (hgcd : A.gcd id = 1) (hproper : modStabF p A ≠ Finset.univ) :
    ¬ modImageF p A ⊆ modStabF p A := by
  intro hsub
  exact hproper (modStabF_eq_univ_of_gcd_one_of_image_subset hAne hgcd hsub)

end Jsp000216

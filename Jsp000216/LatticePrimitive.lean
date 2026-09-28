import Mathlib
import Mathlib.LinearAlgebra.FreeModule.PID

open scoped BigOperators
open Module

namespace Jsp000216

noncomputable section

/-- A finite integral vector is primitive when its coordinates admit a Bezout
combination equal to one. -/
def PrimitiveIntVectorF {n : ℕ} (z : Fin n → ℤ) : Prop :=
  ∃ u : Fin n → ℤ, ∑ i, u i * z i = 1

lemma PrimitiveIntVectorF.ne_zero {n : ℕ} {z : Fin n → ℤ}
    (hz : PrimitiveIntVectorF z) : z ≠ 0 := by
  rintro rfl
  simp [PrimitiveIntVectorF] at hz

/-- Nonnegative gcd of the coordinates. -/
def vectorContentF {n : ℕ} (z : Fin n → ℤ) : ℤ := Finset.univ.gcd z

lemma vectorContentF_dvd {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    vectorContentF z ∣ z i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

lemma vectorContentF_ne_zero {n : ℕ} {z : Fin n → ℤ} (hz : z ≠ 0) :
    vectorContentF z ≠ 0 := by
  rw [vectorContentF, Finset.gcd_ne_zero_iff]
  simpa [funext_iff] using hz

/-- Divide all coordinates by their content. -/
def divideVectorContentF {n : ℕ} (z : Fin n → ℤ) : Fin n → ℤ :=
  fun i => z i / vectorContentF z

lemma vectorContentF_mul_divide {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    vectorContentF z * divideVectorContentF z i = z i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (vectorContentF_dvd z i)

private theorem exists_bezout_finsetF {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℤ) :
    ∃ u : ι → ℤ, ∑ i ∈ s, u i * z i = s.gcd z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨u, hu⟩ := ih
      let A : ℤ := Int.gcdA (z a) (s.gcd z)
      let B : ℤ := Int.gcdB (z a) (s.gcd z)
      refine ⟨fun i => if i = a then A else B * u i, ?_⟩
      rw [Finset.sum_insert ha, Finset.gcd_insert]
      simp only [if_pos]
      have hsum :
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
            B * s.gcd z := by
        calc
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
              ∑ i ∈ s, B * (u i * z i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_neg (by intro hia; subst i; exact ha hi)]
                ring
          _ = B * ∑ i ∈ s, u i * z i := by rw [Finset.mul_sum]
          _ = B * s.gcd z := by rw [hu]
      rw [hsum]
      dsimp [A, B]
      rw [mul_comm B, mul_comm (Int.gcdA (z a) (s.gcd z))]
      exact (Int.gcd_eq_gcd_ab (z a) (s.gcd z)).symm

lemma primitiveIntVectorF_of_content_eq_one {n : ℕ} {z : Fin n → ℤ}
    (hz : vectorContentF z = 1) : PrimitiveIntVectorF z := by
  obtain ⟨u, hu⟩ := exists_bezout_finsetF Finset.univ z
  have hu' : ∑ i, u i * z i = vectorContentF z := by
    simpa [vectorContentF] using hu
  exact ⟨u, hu'.trans hz⟩

lemma divideVectorContentF_primitive {n : ℕ} {z : Fin n → ℤ}
    (hz : z ≠ 0) : PrimitiveIntVectorF (divideVectorContentF z) := by
  apply primitiveIntVectorF_of_content_eq_one
  rw [vectorContentF]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

lemma divideVectorContentF_ne_zero {n : ℕ} {z : Fin n → ℤ}
    (hz : z ≠ 0) : divideVectorContentF z ≠ 0 :=
  (divideVectorContentF_primitive hz).ne_zero

/-- A least nonzero vector for any positive integer-homogeneous gauge is
primitive. -/
theorem primitiveIntVectorF_of_minimal_gauge {n : ℕ} (z : Fin n → ℤ)
    (hz : z ≠ 0) (mu : (Fin n → ℤ) → ℝ)
    (hpos : ∀ x ≠ 0, 0 < mu x)
    (hhom : ∀ (c : ℤ), 0 < c → ∀ x, mu (c • x) = (c : ℝ) * mu x)
    (hmin : ∀ x ≠ 0, mu z ≤ mu x) : PrimitiveIntVectorF z := by
  let c : ℤ := vectorContentF z
  have hc0 : 0 ≤ c := by
    have hn := Finset.normalize_gcd (s := Finset.univ) (f := z)
    have habs : |c| = c := by
      rw [Int.abs_eq_normalize]
      exact hn
    rw [← habs]
    exact abs_nonneg c
  have hcne : c ≠ 0 := vectorContentF_ne_zero hz
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  suffices hc : c = 1 by
    exact primitiveIntVectorF_of_content_eq_one hc
  by_contra hc
  have hc2 : (2 : ℤ) ≤ c := by omega
  let z' : Fin n → ℤ := divideVectorContentF z
  have hz' : z' ≠ 0 := divideVectorContentF_ne_zero hz
  have hz_eq : z = c • z' := by
    funext i
    exact (vectorContentF_mul_divide z i).symm
  have hscale : mu z = (c : ℝ) * mu z' := by
    rw [hz_eq]
    exact hhom c hcpos z'
  have hle : mu z ≤ mu z' := hmin z' hz'
  have hz'pos : 0 < mu z' := hpos z' hz'
  have hc2r : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
  rw [hscale] at hle
  nlinarith

/-- Integral dot-product functional. -/
def intDotLinearF {n : ℕ} (u : Fin n → ℤ) : (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ∑ i, u i * z i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_left_comm]

/-- A primitive vector extends to an integral basis. -/
theorem exists_int_basis_zero_eq_of_primitive {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ) (hz : PrimitiveIntVectorF z) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b ⟨0, hn⟩ = z := by
  obtain ⟨u, hu⟩ := hz
  let f : (Fin n → ℤ) →ₗ[ℤ] ℤ := intDotLinearF u
  have hfz : f z = 1 := by simpa [f, intDotLinearF] using hu
  let K : Submodule ℤ (Fin n → ℤ) := LinearMap.ker f
  let kb := K.basisOfPid (Pi.basisFun ℤ (Fin n))
  let k : ℕ := kb.1
  let bK : Basis (Fin k) ℤ K := kb.2
  have hli : ∀ (c : ℤ), ∀ x ∈ K, c • z + x = 0 → c = 0 := by
    intro c x hx hzero
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
    have h := congrArg f hzero
    rw [map_add, map_smul, hfz, hx0, map_zero] at h
    simpa using h
  have hsp : ∀ x : Fin n → ℤ, ∃ c : ℤ, x + c • z ∈ K := by
    intro x
    refine ⟨-f x, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [map_add, map_smul, hfz]
    simp
  let b' : Basis (Fin (k + 1)) ℤ (Fin n → ℤ) := Basis.mkFinCons z bK hli hsp
  have hb'0 : b' 0 = z := by simp [b', Basis.coe_mkFinCons]
  have hkn : k + 1 = n := by
    have hc := Fintype.card_congr (b'.indexEquiv (Pi.basisFun ℤ (Fin n)))
    simpa using hc
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := b'.reindex (finCongr hkn)
  refine ⟨b, ?_⟩
  simp only [b, Basis.reindex_apply]
  have hzero : (finCongr hkn).symm ⟨0, hn⟩ = (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hzero, hb'0]

/-- Integral coordinates identify the integer span of a real basis with
`ℤ^n`. -/
def zspanCoordEquivF {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Submodule.span ℤ (Set.range b) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (b.restrictScalars ℤ).repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

/-- A shortest nonzero vector in the integer span is primitive in lattice
coordinates and extends to an integral lattice basis. -/
theorem shortest_zspan_vector_extendsF
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ E)
    (v : Submodule.span ℤ (Set.range b)) (hv : v ≠ 0)
    (mu : Submodule.span ℤ (Set.range b) → ℝ)
    (hpos : ∀ x ≠ 0, 0 < mu x)
    (hhom : ∀ (c : ℤ), 0 < c → ∀ x, mu (c • x) = (c : ℝ) * mu x)
    (hmin : ∀ x ≠ 0, mu v ≤ mu x) :
    ∃ B : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)),
      B ⟨0, hn⟩ = v := by
  let e := zspanCoordEquivF b
  let z : Fin n → ℤ := e v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply e.injective
    simpa [z] using hz0
  let nu : (Fin n → ℤ) → ℝ := fun x => mu (e.symm x)
  have hnupos : ∀ x ≠ 0, 0 < nu x := by
    intro x hx
    apply hpos
    simpa using e.symm.injective.ne hx
  have hnuhom : ∀ (c : ℤ), 0 < c → ∀ x, nu (c • x) = (c : ℝ) * nu x := by
    intro c hc x
    dsimp [nu]
    rw [map_smul]
    exact hhom c hc (e.symm x)
  have hnumin : ∀ x ≠ 0, nu z ≤ nu x := by
    intro x hx
    dsimp [nu, z]
    rw [e.symm_apply_apply]
    apply hmin
    simpa using e.symm.injective.ne hx
  have hzprim : PrimitiveIntVectorF z :=
    primitiveIntVectorF_of_minimal_gauge z hz nu hnupos hnuhom hnumin
  obtain ⟨B, hB⟩ := exists_int_basis_zero_eq_of_primitive hn z hzprim
  refine ⟨B.map e.symm, ?_⟩
  rw [Basis.map_apply, hB]
  exact e.symm_apply_apply v

end

end Jsp000216

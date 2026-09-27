import Jsp000216.NormalizedThreeK

open scoped Pointwise

namespace Jsp000216

noncomputable section

/-- Gcd of the absolute offsets of `A` from the anchor `a`. -/
def differenceContentF (A : Finset ℤ) (a : ℤ) : ℕ :=
  A.gcd fun x => (x - a).natAbs

/-- Translate by `a` and divide by the common content of all offsets. -/
def normalizationCoordF (A : Finset ℤ) (a x : ℤ) : ℤ :=
  (x - a) / (differenceContentF A a : ℤ)

/-- Affine normalized image of `A` based at `a`. -/
def normalizeAtF (A : Finset ℤ) (a : ℤ) : Finset ℤ :=
  A.image (normalizationCoordF A a)

lemma differenceContentF_dvd_sub (A : Finset ℤ) (a : ℤ) {x : ℤ}
    (hx : x ∈ A) :
    (differenceContentF A a : ℤ) ∣ x - a := by
  rw [Int.natCast_dvd]
  exact Finset.gcd_dvd hx

lemma differenceContentF_ne_zero {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    differenceContentF A a ≠ 0 := by
  intro hzero
  have hall : ∀ z ∈ A, (z - a).natAbs = 0 := by
    exact Finset.gcd_eq_zero_iff.mp
      (show A.gcd (fun z => (z - a).natAbs) = 0 by
        simpa [differenceContentF] using hzero)
  have hsub : A ⊆ {a} := by
    intro z hz
    simp only [Finset.mem_singleton]
    exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (hall z hz))
  have hc := Finset.card_le_card hsub
  simpa using hc at hcard

lemma differenceContentF_pos {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    0 < differenceContentF A a :=
  Nat.pos_of_ne_zero (differenceContentF_ne_zero ha hcard)

lemma add_content_mul_normalizationCoordF {A : Finset ℤ} {a x : ℤ}
    (hx : x ∈ A) :
    a + (differenceContentF A a : ℤ) * normalizationCoordF A a x = x := by
  have hdvd := differenceContentF_dvd_sub A a hx
  have hcancel :
      (differenceContentF A a : ℤ) *
        ((x - a) / (differenceContentF A a : ℤ)) = x - a :=
    Int.mul_ediv_cancel' hdvd
  rw [normalizationCoordF]
  omega

lemma normalizationCoordF_injOn {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    Set.InjOn (normalizationCoordF A a) A := by
  intro x hx y hy hxy
  have hxrec := add_content_mul_normalizationCoordF (A := A) (a := a) hx
  have hyrec := add_content_mul_normalizationCoordF (A := A) (a := a) hy
  rw [hxy] at hxrec
  exact hxrec.symm.trans hyrec

lemma card_normalizeAtF {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    (normalizeAtF A a).card = A.card := by
  rw [normalizeAtF, Finset.card_image_iff]
  exact normalizationCoordF_injOn ha hcard

lemma zero_mem_normalizeAtF {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    0 ∈ normalizeAtF A a := by
  apply Finset.mem_image.mpr
  refine ⟨a, ha, ?_⟩
  simp [normalizationCoordF]

lemma normalizeAtF_nonneg {A : Finset ℤ} {a : ℤ}
    (hlower : ∀ x ∈ A, a ≤ x) {z : ℤ}
    (hz : z ∈ normalizeAtF A a) : 0 ≤ z := by
  rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
  exact Int.ediv_nonneg (sub_nonneg.mpr (hlower x hx)) (by positivity)

/-- Integer-valued finset gcd agrees with the cast of the gcd of natAbs. -/
lemma finset_int_gcd_eq_natAbs_gcd (S : Finset ℤ) :
    S.gcd id = (S.gcd Int.natAbs : ℤ) := by
  induction S using Finset.cons_induction_on with
  | empty => simp
  | cons a S ha ih =>
      rw [Finset.gcd_cons ha, Finset.gcd_cons ha, ih]
      rw [← Int.coe_gcd]
      rfl

/-- Normalizing by the full offset content produces a primitive set. -/
lemma differenceContentF_normalizeAtF_eq_one {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    differenceContentF (normalizeAtF A a) 0 = 1 := by
  let d := differenceContentF A a
  let e := differenceContentF (normalizeAtF A a) 0
  have hdpos : 0 < d := by
    simpa [d] using differenceContentF_pos ha hcard
  have hde_dvd : d * e ∣ d := by
    apply Finset.dvd_gcd
    intro x hx
    have hdvd : (d : ℤ) ∣ x - a := by
      simpa [d] using differenceContentF_dvd_sub A a hx
    have hxnorm : normalizationCoordF A a x ∈ normalizeAtF A a :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hecoord : e ∣ (normalizationCoordF A a x).natAbs := by
      have h := Finset.gcd_dvd
        (s := normalizeAtF A a)
        (f := fun z : ℤ => (z - 0).natAbs) hxnorm
      simpa only [e, differenceContentF, sub_zero] using h
    have hquotabs :
        (normalizationCoordF A a x).natAbs = (x - a).natAbs / d := by
      simpa [normalizationCoordF, d] using Int.natAbs_ediv_of_dvd hdvd
    have hdmul : d ∣ (x - a).natAbs := by
      simpa only [d, differenceContentF] using
        (Finset.gcd_dvd hx : differenceContentF A a ∣ (x - a).natAbs)
    have hoffset :
        (x - a).natAbs = d * (normalizationCoordF A a x).natAbs := by
      rw [hquotabs]
      exact (Nat.mul_div_cancel' hdmul).symm
    rw [hoffset]
    exact Nat.mul_dvd_mul_left d hecoord
  have he_dvd_one : e ∣ 1 := by
    apply (Nat.mul_dvd_mul_iff_left hdpos).mp
    simpa using hde_dvd
  exact Nat.eq_one_of_dvd_one he_dvd_one

lemma gcd_normalizeAtF_eq_one {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    (normalizeAtF A a).gcd id = 1 := by
  have hcontent := differenceContentF_normalizeAtF_eq_one ha hcard
  have hnat : (normalizeAtF A a).gcd Int.natAbs = 1 := by
    simpa only [differenceContentF, sub_zero] using hcontent
  rw [finset_int_gcd_eq_natAbs_gcd, hnat]
  norm_num

private def denormalizePairSumF (A : Finset ℤ) (a z : ℤ) : ℤ :=
  2 * a + (differenceContentF A a : ℤ) * z

lemma image_denormalizePairSumF_add_normalizeAtF {A : Finset ℤ} {a : ℤ} :
    (normalizeAtF A a + normalizeAtF A a).image (denormalizePairSumF A a) =
      A + A := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, hwz⟩
    rcases Finset.mem_add.mp hw with ⟨u, hu, v, hv, huv⟩
    rcases Finset.mem_image.mp hu with ⟨x, hx, hxu⟩
    rcases Finset.mem_image.mp hv with ⟨y, hy, hyv⟩
    apply Finset.mem_add.mpr
    refine ⟨x, hx, y, hy, ?_⟩
    have hxrec := add_content_mul_normalizationCoordF (A := A) (a := a) hx
    have hyrec := add_content_mul_normalizationCoordF (A := A) (a := a) hy
    rw [← hwz, ← huv]
    calc
      x + y =
          (a + (differenceContentF A a : ℤ) * normalizationCoordF A a x) +
          (a + (differenceContentF A a : ℤ) * normalizationCoordF A a y) :=
        congrArg₂ (· + ·) hxrec.symm hyrec.symm
      _ = denormalizePairSumF A a (u + v) := by
        rw [hxu, hyv]
        simp only [denormalizePairSumF]
        ring
  · intro hz
    rcases Finset.mem_add.mp hz with ⟨x, hx, y, hy, hxyz⟩
    apply Finset.mem_image.mpr
    refine ⟨normalizationCoordF A a x + normalizationCoordF A a y, ?_, ?_⟩
    · exact Finset.mem_add.mpr
        ⟨normalizationCoordF A a x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
          normalizationCoordF A a y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
    · have hxrec := add_content_mul_normalizationCoordF (A := A) (a := a) hx
      have hyrec := add_content_mul_normalizationCoordF (A := A) (a := a) hy
      calc
        denormalizePairSumF A a
            (normalizationCoordF A a x + normalizationCoordF A a y) =
            (a + (differenceContentF A a : ℤ) * normalizationCoordF A a x) +
            (a + (differenceContentF A a : ℤ) * normalizationCoordF A a y) := by
          simp only [denormalizePairSumF]
          ring
        _ = x + y := congrArg₂ (· + ·) hxrec hyrec
        _ = z := hxyz

lemma card_add_normalizeAtF {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    (normalizeAtF A a + normalizeAtF A a).card = (A + A).card := by
  let d := differenceContentF A a
  have hdne : (d : ℤ) ≠ 0 := by
    exact_mod_cast differenceContentF_ne_zero ha hcard
  have hinj : Function.Injective (denormalizePairSumF A a) := by
    intro x y hxy
    have hmul : (d : ℤ) * x = (d : ℤ) * y := by
      simpa [denormalizePairSumF, d] using add_left_cancel hxy
    exact mul_left_cancel₀ hdne hmul
  calc
    (normalizeAtF A a + normalizeAtF A a).card =
        ((normalizeAtF A a + normalizeAtF A a).image
          (denormalizePairSumF A a)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (A + A).card := by rw [image_denormalizePairSumF_add_normalizeAtF]

end

end Jsp000216

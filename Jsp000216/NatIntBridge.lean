import Jsp000216.FiniteThreeK

open scoped Pointwise

namespace Jsp000216

/-- Cast a finite set of naturals into the integers. -/
def natToIntFinsetF (A : Finset ℕ) : Finset ℤ :=
  A.image fun n : ℕ => (n : ℤ)

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

/-- If three ordered natural numbers, viewed in `ℤ`, lie in one positive-step
arithmetic progression of displayed length `length`, then the last one is
bounded using only the first two and `length`. -/
lemma ContainedInAPF.nat_upper_bound
    {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAPF A start step length)
    {x0 x1 x : ℕ}
    (hx0 : (x0 : ℤ) ∈ A) (hx1 : (x1 : ℤ) ∈ A) (hxx : (x : ℤ) ∈ A)
    (h01 : x0 < x1) (h1x : x1 ≤ x) :
    x ≤ x0 + length * x1 := by
  rcases hA.2 _ hx0 with ⟨i0, hi0, hr0⟩
  rcases hA.2 _ hx1 with ⟨i1, hi1, hr1⟩
  rcases hA.2 _ hxx with ⟨ix, hix, hrx⟩
  have hstepZ : (0 : ℤ) < (step : ℤ) := by
    exact_mod_cast hA.1
  have h01Z : (x0 : ℤ) < (x1 : ℤ) := by
    exact_mod_cast h01
  have h1xZ : (x1 : ℤ) ≤ (x : ℤ) := by
    exact_mod_cast h1x
  have hi01 : (i0 : ℤ) < (i1 : ℤ) := by
    by_contra hnot
    have hle : (i1 : ℤ) ≤ (i0 : ℤ) := le_of_not_gt hnot
    have hmul : (i1 : ℤ) * (step : ℤ) ≤ (i0 : ℤ) * (step : ℤ) :=
      mul_le_mul_of_nonneg_right hle hstepZ.le
    nlinarith [hr0, hr1]
  have hi1x : (i1 : ℤ) ≤ (ix : ℤ) := by
    by_contra hnot
    have hlt : (ix : ℤ) < (i1 : ℤ) := lt_of_not_ge hnot
    have hmul : (ix : ℤ) * (step : ℤ) < (i1 : ℤ) * (step : ℤ) :=
      mul_lt_mul_of_pos_right hlt hstepZ
    nlinarith [hr1, hrx]
  have hcoef_nonneg : (0 : ℤ) ≤ (ix : ℤ) - (i0 : ℤ) := by
    omega
  have hcoef_le : (ix : ℤ) - (i0 : ℤ) ≤ (length : ℤ) := by
    have hixZ : (ix : ℤ) < (length : ℤ) := by
      exact_mod_cast hix
    have hi0Z : (0 : ℤ) ≤ (i0 : ℤ) := by positivity
    omega
  have hdiff1 :
      (x1 : ℤ) - (x0 : ℤ) =
        ((i1 : ℤ) - (i0 : ℤ)) * (step : ℤ) := by
    rw [hr1, hr0]
    ring
  have hdiff1_ge : (1 : ℤ) ≤ (i1 : ℤ) - (i0 : ℤ) := by
    omega
  have hstep_le_diff :
      (step : ℤ) ≤ ((i1 : ℤ) - (i0 : ℤ)) * (step : ℤ) := by
    have := mul_le_mul_of_nonneg_right hdiff1_ge hstepZ.le
    simpa using this
  have hstep_le_x1 : (step : ℤ) ≤ (x1 : ℤ) := by
    have hx0Z : (0 : ℤ) ≤ (x0 : ℤ) := by positivity
    calc
      (step : ℤ) ≤ ((i1 : ℤ) - (i0 : ℤ)) * (step : ℤ) := hstep_le_diff
      _ = (x1 : ℤ) - (x0 : ℤ) := hdiff1.symm
      _ ≤ (x1 : ℤ) := by omega
  have hdiffx :
      (x : ℤ) - (x0 : ℤ) =
        ((ix : ℤ) - (i0 : ℤ)) * (step : ℤ) := by
    rw [hrx, hr0]
    ring
  have hprod_le :
      ((ix : ℤ) - (i0 : ℤ)) * (step : ℤ) ≤
        (length : ℤ) * (x1 : ℤ) := by
    calc
      ((ix : ℤ) - (i0 : ℤ)) * (step : ℤ) ≤
          (length : ℤ) * (step : ℤ) :=
        mul_le_mul_of_nonneg_right hcoef_le hstepZ.le
      _ ≤ (length : ℤ) * (x1 : ℤ) :=
        mul_le_mul_of_nonneg_left hstep_le_x1 (by positivity)
  have hboundZ :
      (x : ℤ) ≤ (x0 : ℤ) + (length : ℤ) * (x1 : ℤ) := by
    nlinarith [hdiffx, hprod_le]
  exact_mod_cast hboundZ

end Jsp000216

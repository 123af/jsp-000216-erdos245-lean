import Jsp000216.CramerBound

open scoped BigOperators

namespace Jsp000216

/-- Reduce the nonnegative doubling-chain representation to linearly
independent nonzero support.  If one homogeneous coordinate is constantly
one, the coefficient of the initial generator is strictly positive; Cramer's
rule then bounds it by a dimension/box constant. -/
lemma exists_bounded_reduced_doublingChain_coefficients
    {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ) (q : Fin d)
    (hq : ∀ i, u i q = 1)
    (B : Fin d → ℕ) (hB : ∀ j, 1 ≤ B j)
    (hgen : ∀ i j, (doublingChainGenInt u n i j).natAbs ≤ B j)
    (hv : ∀ j, (u n j).natAbs ≤ B j) :
    ∃ b : Fin (n + 1) → ℚ,
      (∀ i, 0 ≤ b i) ∧
      castIntVec (u n) =
        ∑ i, b i • castIntVec (doublingChainGenInt u n i) ∧
      0 < b 0 ∧
      b 0 ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by
  classical
  obtain ⟨a, ha, harepr⟩ :=
    exists_nonnegative_doublingChain_coefficients
      (fun k => castIntVec (u k)) n
  have harepr' :
      castIntVec (u n) =
        ∑ i, a i • castIntVec (doublingChainGenInt u n i) := by
    rw [harepr]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [castIntVec_doublingChainGenInt]
  obtain ⟨b, hb, hbsum, hbli⟩ :=
    exists_nonnegative_independent_support
      (fun i => castIntVec (doublingChainGenInt u n i)) a ha
  have hrel :
      castIntVec (u n) =
        ∑ i, b i • castIntVec (doublingChainGenInt u n i) := by
    rw [harepr', ← hbsum]
  have hgenq (i : Fin (n + 1)) :
      doublingChainGenInt u n i q = if i = 0 then 1 else -1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [doublingChainGenInt, hq]
    · have hsucc : (Fin.succ j : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
      simp [doublingChainGenInt, hq, hsucc]
  have hcoord :
      (1 : ℚ) =
        ∑ i, b i * (doublingChainGenInt u n i q : ℚ) := by
    have h := congrFun hrel q
    simpa only [castIntVec_apply, hq, Int.cast_one, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have hbzero : 0 < b 0 := by
    by_contra hnpos
    have hb0 : b 0 = 0 := le_antisymm (le_of_not_gt hnpos) (hb 0)
    have hterm (i : Fin (n + 1)) :
        b i * (doublingChainGenInt u n i q : ℚ) ≤ 0 := by
      by_cases hi : i = 0
      · subst i
        simp [hb0]
      · rw [hgenq, if_neg hi]
        simp [hb i]
    have hsum :
        (∑ i, b i * (doublingChainGenInt u n i q : ℚ)) ≤ 0 :=
      Finset.sum_nonpos fun i _hi => hterm i
    linarith
  let i0 : ↥(supportNZF b) :=
    ⟨0, (mem_supportNZF b 0).2 hbzero.ne'⟩
  have hrel_support :
      castIntVec (u n) =
        ∑ i : ↥(supportNZF b),
          b i.1 • castIntVec (doublingChainGenInt u n i.1) := by
    calc
      castIntVec (u n) =
          ∑ i, b i • castIntVec (doublingChainGenInt u n i) := hrel
      _ = ∑ i ∈ supportNZF b,
          b i • castIntVec (doublingChainGenInt u n i) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hnot
        have hbi : b i = 0 :=
          not_ne_iff.mp (mt (mem_supportNZF b i).mpr hnot)
        simp [hbi]
      _ = ∑ i : ↥(supportNZF b),
          b i.1 • castIntVec (doublingChainGenInt u n i.1) := by
        rw [← (supportNZF b).sum_attach]
        rfl
  have hcoeff := coefficient_le_of_integral_independent
    (fun i : ↥(supportNZF b) => doublingChainGenInt u n i.1)
    (u n) (fun i : ↥(supportNZF b) => b i.1) i0
    hbli hrel_support B hB
    (fun i j => hgen i.1 j) hv
  refine ⟨b, hb, hrel, hbzero, ?_⟩
  simpa [i0] using hcoeff

end Jsp000216

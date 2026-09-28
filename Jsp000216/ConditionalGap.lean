import Jsp000216.DensityScale
import Jsp000216.NatIntBridge
import Jsp000216.GAPChain
import Jsp000216.GAPCoverInterface

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Jsp000216

noncomputable section

/-- A uniform quantitative GAP cover for doubling constant `12` converts an
eventual sumset ratio below three into arbitrarily late factor-two gaps in
the increasing enumeration.  This isolates the sole remaining structural
input of the infinite argument. -/
lemma exists_doubling_gap_of_eventually_three_of_cover
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    (hden : Tendsto (fun N => (countInF S N : ℝ) / N) atTop (𝓝 0))
    {R C : ℕ} (hcover : UniformGAPCoverF 12 R C)
    (hsum : ∀ᶠ N in atTop,
      countInF (S + S) N < 3 * countInF S N) :
    ∀ s : ℕ, ∃ i ≥ s,
      2 * enumerateF S i < enumerateF S (i + 1) := by
  intro s
  by_contra hgap
  push_neg at hgap
  have hnogap : ∀ i ≥ s,
      enumerateF S (i + 1) ≤ 2 * enumerateF S i := by
    intro i hi
    exact hgap i hi
  let D := (R + 1).factorial * (3 ^ R * C) * enumerateF S s
  have hdenseD : ∀ᶠ M in atTop,
      (D + 1) * countInF S M < M :=
    density_eventually_mul_ltF (countInF S) hden (by omega)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hdenseD
  have hlarge : ∀ᶠ N in atTop,
      countInF S L + s + 2 < countInF S N :=
    (countInF_tendsto_atTop hS hpos).eventually
      (eventually_gt_atTop (countInF S L + s + 2))
  obtain ⟨Lsum, hLsum⟩ := eventually_atTop.1 hsum
  have hsum2 : ∀ᶠ N in atTop,
      countInF (S + S) (2 * N) < 3 * countInF S (2 * N) :=
    eventually_atTop.2 ⟨Lsum, fun N hN => hLsum (2 * N) (by omega)⟩
  obtain ⟨N, hstop, hsumN, hklarge⟩ :=
    ((frequently_countInF_two_mul_le_four hS hpos hden).and_eventually
      (hsum2.and hlarge)).exists
  let X := windowF S N
  let k := countInF S N
  have hsk : s < k := by
    dsimp [k] at hklarge ⊢
    omega
  have hkpos : 0 < k := by omega
  have hXcard : X.card = k := rfl
  have hXne : X.Nonempty := Finset.card_pos.mp (by simpa [hXcard] using hkpos)
  have hXsmall : (X + X).card ≤ 12 * X.card := by
    have hsub := Finset.card_le_card (windowF_add_subset S N)
    change (X + X).card ≤ countInF (S + S) (2 * N) at hsub
    change countInF S (2 * N) ≤ 4 * k at hstop
    change countInF (S + S) (2 * N) < 3 * countInF S (2 * N) at hsumN
    change X.card = k at hXcard
    omega
  let Xint := natToIntFinsetF X
  have hXintne : Xint.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [Xint]
    rw [card_natToIntFinsetF, hXcard]
    exact hkpos
  have hXintsmall : (Xint + Xint).card ≤ 12 * Xint.card := by
    dsimp [Xint]
    rw [card_add_natToIntFinsetF, card_natToIntFinsetF]
    exact hXsmall
  obtain ⟨Q, hQrank, hQsub, hQcard⟩ :=
    hcover Xint hXintne hXintsmall
  have hprefix (j : ℕ) (hj : j < k) : enumerateF S j ∈ X := by
    apply mem_windowF.mpr
    exact ⟨hpos (enumerateF_mem hS j),
      (enumerateF_le_iff_lt_countInF hS hpos j N).mpr (by simpa [k] using hj),
      enumerateF_mem hS j⟩
  have hparam (j : ℕ) (hj : j < k) :
      ∃ q : Q.Param, Q.eval q = (enumerateF S j : ℤ) := by
    apply Q.mem_carrier_iff.mp
    apply hQsub
    exact natCast_mem_natToIntFinsetF (hprefix j hj)
  let x : ℕ → Q.Param := fun j =>
    if hj : j < k then Classical.choose (hparam j hj) else default
  have hx (j : ℕ) (hj : j < k) :
      Q.eval (x j) = (enumerateF S j : ℤ) := by
    simp only [x, dif_pos hj]
    exact Classical.choose_spec (hparam j hj)
  let n := k - 1 - s
  let y : ℕ → Q.Param := fun j => x (s + j)
  have hsn : s + n = k - 1 := by
    dsimp [n]
    omega
  have hy (j : ℕ) (hj : j ≤ n) :
      Q.eval (y j) = (enumerateF S (s + j) : ℤ) := by
    apply hx
    omega
  have hypos : ∀ j ≤ n, 0 ≤ Q.eval (y j) := by
    intro j hj
    rw [hy j hj]
    exact Int.natCast_nonneg _
  have hynogap : ∀ j < n,
      Q.eval (y (j + 1)) ≤ 2 * Q.eval (y j) := by
    intro j hj
    rw [hy (j + 1) (by omega), hy j hj.le]
    exact_mod_cast hnogap (s + j) (by omega)
  have hdiam := Q.no_gap_chain_diameter_bound y n hypos hynogap
  have hdiamNat :
      enumerateF S (k - 1) ≤
        ((Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard)) *
          enumerateF S s := by
    have hy0 : Q.eval (y 0) = (enumerateF S s : ℤ) := by
      simpa using hy 0 (Nat.zero_le n)
    have hyn : Q.eval (y n) = (enumerateF S (k - 1) : ℤ) := by
      simpa [hsn] using hy n le_rfl
    rw [hyn, hy0] at hdiam
    exact_mod_cast hdiam
  have hcoef :
      (Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard) ≤
        (R + 1).factorial * (3 ^ R * (C * k)) := by
    have hfac : (Q.rank + 1).factorial ≤ (R + 1).factorial := by
      apply Nat.factorial_le
      omega
    have hpow : 3 ^ Q.rank ≤ 3 ^ R := by
      apply Nat.pow_le_pow_right (by omega)
      exact hQrank
    have hcard : Q.boxCard ≤ C * k := by
      dsimp [Xint] at hQcard
      rw [card_natToIntFinsetF, hXcard] at hQcard
      exact hQcard
    exact Nat.mul_le_mul hfac (Nat.mul_le_mul hpow hcard)
  have hlinear : enumerateF S (k - 1) ≤ D * k := by
    calc
      enumerateF S (k - 1) ≤
          ((Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard)) *
            enumerateF S s := hdiamNat
      _ ≤ ((R + 1).factorial * (3 ^ R * (C * k))) *
            enumerateF S s := Nat.mul_le_mul_right _ hcoef
      _ = D * k := by simp only [D]; ring
  have hlastL : L < enumerateF S (k - 1) := by
    have hcountL : countInF S L < k := by
      dsimp [k] at hklarge ⊢
      omega
    have hnot : ¬(k - 1 < countInF S L) := by omega
    exact Nat.lt_of_not_ge fun hle =>
      hnot ((enumerateF_le_iff_lt_countInF hS hpos (k - 1) L).mp hle)
  have hdenseLast := hL (enumerateF S (k - 1)) hlastL.le
  rw [countInF_enumerate_eq hS hpos (k - 1)] at hdenseLast
  have hkpred : k - 1 + 1 = k := by omega
  rw [hkpred] at hdenseLast
  rw [add_mul, one_mul] at hdenseLast
  omega

end

end Jsp000216

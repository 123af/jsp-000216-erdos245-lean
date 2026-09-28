import Mathlib

open scoped BigOperators

namespace Jsp000216

/-- Generators attached to a doubling chain.  The zeroth generator is the
initial vector, and every later generator records the deviation from exact
doubling. -/
def doublingChainGen {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) : Fin (n + 1) → V :=
  Fin.cases (u 0) fun j : Fin n => u (j + 1) - (2 : ℚ) • u j

private lemma doublingChainGen_castSucc
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) (i : Fin (n + 1)) :
    doublingChainGen u (n + 1) i.castSucc = doublingChainGen u n i := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · rfl
  · rfl

private lemma doublingChainGen_last
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) :
    doublingChainGen u (n + 1) (Fin.last (n + 1)) =
      u (n + 1) - (2 : ℚ) • u n := by
  rfl

/-- Every endpoint of a finite doubling chain is a nonnegative rational
combination of the initial vector and the successive doubling deviations. -/
lemma exists_nonnegative_doublingChain_coefficients
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) :
    ∃ a : Fin (n + 1) → ℚ, (∀ i, 0 ≤ a i) ∧
      u n = ∑ i, a i • doublingChainGen u n i := by
  induction n with
  | zero =>
      refine ⟨fun _ => 1, fun _ => by positivity, ?_⟩
      simp [doublingChainGen]
  | succ n ih =>
      obtain ⟨a, ha, hrepr⟩ := ih
      let a' : Fin (n + 2) → ℚ := Fin.lastCases 1 (fun i => 2 * a i)
      refine ⟨a', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [a']
        · simp [a', ha]
      · rw [Fin.sum_univ_castSucc]
        simp only [a', Fin.lastCases_castSucc, Fin.lastCases_last,
          doublingChainGen_castSucc, doublingChainGen_last]
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, ← hrepr]
        module

/-- Integer-coordinate version of the doubling-chain generators. -/
def doublingChainGenInt {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ) :
    Fin (n + 1) → Fin d → ℤ :=
  Fin.cases (u 0) fun j : Fin n => u (j + 1) - 2 • u j

/-- Cast an integer coordinate vector to rational coordinates. -/
def castIntVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℚ :=
  fun i => z i

@[simp] lemma castIntVec_apply {d : ℕ} (z : Fin d → ℤ) (i : Fin d) :
    castIntVec z i = (z i : ℚ) := rfl

lemma castIntVec_injective {d : ℕ} :
    Function.Injective (@castIntVec d) := by
  intro x y h
  ext j
  have hj := congrFun h j
  change (x j : ℚ) = (y j : ℚ) at hj
  exact_mod_cast hj

lemma castIntVec_doublingChainGenInt {d : ℕ}
    (u : ℕ → Fin d → ℤ) (n : ℕ) (i : Fin (n + 1)) :
    castIntVec (doublingChainGenInt u n i) =
      doublingChainGen (fun k => castIntVec (u k)) n i := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · rfl
  · ext q
    simp [doublingChainGenInt, doublingChainGen, castIntVec, sub_eq_add_neg]

end Jsp000216

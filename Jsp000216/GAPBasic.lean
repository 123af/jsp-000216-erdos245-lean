import Mathlib

open scoped BigOperators

namespace Jsp000216

/-- A finite affine generalized arithmetic progression in `ℤ`.
The coefficient box uses coordinates `0, ..., length i`. -/
structure GAPF where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace GAPF

/-- Coefficient vectors in the defining box. -/
abbrev Param (Q : GAPF) := (i : Fin Q.rank) → Fin (Q.length i + 1)

/-- Evaluation of one coefficient vector. -/
def eval (Q : GAPF) (x : Q.Param) : ℤ :=
  Q.base + ∑ i : Fin Q.rank, (x i : ℤ) * Q.step i

/-- Finite set represented by the progression. -/
def carrier (Q : GAPF) : Finset ℤ :=
  (Finset.univ : Finset Q.Param).image Q.eval

/-- The presentation is proper when distinct coefficient vectors have
distinct integer values. -/
def Proper (Q : GAPF) : Prop := Function.Injective Q.eval

/-- Cardinality of the coefficient box. -/
def boxCard (Q : GAPF) : ℕ :=
  ∏ i : Fin Q.rank, (Q.length i + 1)

lemma mem_carrier_iff (Q : GAPF) {z : ℤ} :
    z ∈ Q.carrier ↔ ∃ x : Q.Param, Q.eval x = z := by
  simp [carrier]

lemma boxCard_pos (Q : GAPF) : 0 < Q.boxCard := by
  unfold boxCard
  exact Finset.prod_pos fun _ _ => Nat.succ_pos _

/-- Properness identifies the represented set with the full coefficient box. -/
lemma card_carrier_of_proper (Q : GAPF) (hQ : Q.Proper) :
    Q.carrier.card = Q.boxCard := by
  rw [carrier, Finset.card_image_of_injective (Finset.univ : Finset Q.Param) hQ,
    Finset.card_univ]
  simp [Param, boxCard]

/-- Every coefficient lies in its displayed side length. -/
lemma param_le_length (Q : GAPF) (x : Q.Param) (i : Fin Q.rank) :
    (x i : ℕ) ≤ Q.length i := by
  exact Nat.le_of_lt_succ (x i).isLt

end GAPF

end Jsp000216

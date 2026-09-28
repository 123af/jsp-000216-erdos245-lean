import Jsp000216.GapWindow
import Jsp000216.NatIntBridge

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- At a genuine doubling gap, a sharp `3k-4` bound on the global sumset
window forces the `i`-th element of `S` to be linearly bounded in `i`.
This is the finite inverse-theorem half of the infinite argument. -/
lemma enumerateF_linear_bound_at_gap
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1)
    {i : ℕ} (hi : 2 ≤ i)
    (hgap : 2 * enumerateF S i < enumerateF S (i + 1))
    (hsmall :
      countInF (S + S) (2 * enumerateF S i) ≤ 3 * (i + 1) - 4) :
    enumerateF S i ≤
      (enumerateF S 0 + 2 * enumerateF S 1) * (i + 1) := by
  let X := windowF S (enumerateF S i)
  have hXcard : X.card = i + 1 := by
    change countInF S (enumerateF S i) = i + 1
    exact countInF_enumerate_eq hS hpos i
  have hprefix (j : ℕ) (hj : j ≤ i) : enumerateF S j ∈ X := by
    apply mem_windowF.mpr
    exact ⟨hpos (enumerateF_mem hS j),
      (enumerateF_strictMono hS).monotone hj,
      enumerateF_mem hS j⟩
  have hX0 : enumerateF S 0 ∈ X := hprefix 0 (by omega)
  have hX1 : enumerateF S 1 ∈ X := hprefix 1 (by omega)
  have hXi : enumerateF S i ∈ X := hprefix i le_rfl
  have hXsum :
      (X + X).card = countInF (S + S) (2 * enumerateF S i) := by
    change
      (windowF S (enumerateF S i) + windowF S (enumerateF S i)).card =
        (windowF (S + S) (2 * enumerateF S i)).card
    rw [windowF_add_eq_at_doubling_gap hS hpos i hgap]
  let A := natToIntFinsetF X
  have hAcard : A.card = i + 1 := by
    dsimp [A]
    rw [card_natToIntFinsetF, hXcard]
  have hAsum :
      (A + A).card = countInF (S + S) (2 * enumerateF S i) := by
    dsimp [A]
    rw [card_add_natToIntFinsetF, hXsum]
  have hAcard3 : 3 ≤ A.card := by
    rw [hAcard]
    omega
  have hAsmall : (A + A).card ≤ 3 * A.card - 4 := by
    rw [hAsum, hAcard]
    exact hsmall
  obtain ⟨start, step, hAP⟩ :=
    freiman_three_k_minus_fourF hAcard3 hAsmall
  have h01 : enumerateF S 0 < enumerateF S 1 :=
    enumerateF_strictMono hS (by omega)
  have h1i : enumerateF S 1 ≤ enumerateF S i :=
    (enumerateF_strictMono hS).monotone (by omega)
  have hraw := hAP.nat_upper_bound
    (natCast_mem_natToIntFinsetF hX0)
    (natCast_mem_natToIntFinsetF hX1)
    (natCast_mem_natToIntFinsetF hXi)
    h01 h1i
  have hLle :
      (A + A).card - A.card + 1 ≤ 2 * (i + 1) := by
    rw [hAcard]
    omega
  have hmul :
      ((A + A).card - A.card + 1) * enumerateF S 1 ≤
        (2 * (i + 1)) * enumerateF S 1 := by
    exact Nat.mul_le_mul_right (enumerateF S 1) hLle
  have he0 : enumerateF S 0 ≤ enumerateF S 0 * (i + 1) := by
    calc
      enumerateF S 0 = enumerateF S 0 * 1 := by simp
      _ ≤ enumerateF S 0 * (i + 1) :=
        Nat.mul_le_mul_left (enumerateF S 0) (by omega)
  calc
    enumerateF S i ≤
        enumerateF S 0 +
          ((A + A).card - A.card + 1) * enumerateF S 1 := hraw
    _ ≤ enumerateF S 0 + (2 * (i + 1)) * enumerateF S 1 :=
      Nat.add_le_add_left hmul _
    _ = enumerateF S 0 + (2 * enumerateF S 1) * (i + 1) := by ring
    _ ≤ enumerateF S 0 * (i + 1) +
        (2 * enumerateF S 1) * (i + 1) :=
      Nat.add_le_add_right he0 _
    _ = (enumerateF S 0 + 2 * enumerateF S 1) * (i + 1) := by ring

end

end Jsp000216

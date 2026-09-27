import Jsp000216.SetCount

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

/-- At an enumeration gap larger than a factor of two, the finite prefix
self-sum is exactly the global sumset window at the doubled cutoff. -/
lemma windowF_add_eq_at_doubling_gap
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Set.Ici 1) (i : ℕ)
    (hgap : 2 * enumerateF S i < enumerateF S (i + 1)) :
    windowF S (enumerateF S i) + windowF S (enumerateF S i) =
      windowF (S + S) (2 * enumerateF S i) := by
  apply Finset.Subset.antisymm
  · exact windowF_add_subset S (enumerateF S i)
  · intro z hz
    have hz' := mem_windowF.mp hz
    have hzle := hz'.2.1
    rcases hz'.2.2 with ⟨x, hxS, y, hyS, rfl⟩
    have hxle : x ≤ enumerateF S i := by
      by_contra hx
      have hxgt : enumerateF S i < x := Nat.lt_of_not_ge hx
      rw [← range_enumerateF hS] at hxS
      rcases hxS with ⟨j, rfl⟩
      have hij : i < j := (enumerateF_strictMono hS).lt_iff_lt.mp hxgt
      have hnext : enumerateF S (i + 1) ≤ enumerateF S j :=
        (enumerateF_strictMono hS).monotone (by omega)
      have htooLarge : 2 * enumerateF S i < enumerateF S j + y :=
        hgap.trans_le (hnext.trans (Nat.le_add_right _ _))
      exact (Nat.not_lt_of_ge hzle) htooLarge
    have hyle : y ≤ enumerateF S i := by
      by_contra hy
      have hygt : enumerateF S i < y := Nat.lt_of_not_ge hy
      rw [← range_enumerateF hS] at hyS
      rcases hyS with ⟨j, rfl⟩
      have hij : i < j := (enumerateF_strictMono hS).lt_iff_lt.mp hygt
      have hnext : enumerateF S (i + 1) ≤ enumerateF S j :=
        (enumerateF_strictMono hS).monotone (by omega)
      have htooLarge : 2 * enumerateF S i < x + enumerateF S j :=
        hgap.trans_le (hnext.trans (Nat.le_add_left _ _))
      exact (Nat.not_lt_of_ge hzle) htooLarge
    exact Finset.mem_add.mpr ⟨x,
      mem_windowF.mpr ⟨hpos hxS, hxle, hxS⟩, y,
      mem_windowF.mpr ⟨hpos hyS, hyle, hyS⟩, rfl⟩

end Jsp000216

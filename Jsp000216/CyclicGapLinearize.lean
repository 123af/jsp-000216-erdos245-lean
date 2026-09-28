import Jsp000216.CyclicGAP
import Jsp000216.FreimanFourfold

open scoped BigOperators Pointwise

namespace Jsp000216

noncomputable section

/-- Linearize a centred cyclic GAP through a Freiman-linear map into our
integer `GAPF`.  The parameter boxes are definitionally the same. -/
noncomputable def cyclicGapFreimanImageF {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (L : ZMod N → ℤ) : GAPF where
  rank := Q.rank
  base := L (Q.eval Q.minParam)
  step i := if hi : 0 < Q.radius i then
      L (Q.eval (Q.unitParam i hi)) - L (Q.eval Q.minParam)
    else 0
  length i := 2 * Q.radius i

@[simp] lemma cyclicGapFreimanImageF_rank {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (L : ZMod N → ℤ) :
    (cyclicGapFreimanImageF Q L).rank = Q.rank := rfl

@[simp] lemma cyclicGapFreimanImageF_length {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (L : ZMod N → ℤ) (i : Fin Q.rank) :
    (cyclicGapFreimanImageF Q L).length i = 2 * Q.radius i := rfl

lemma eval_cyclicGapFreimanImageF_pred_add_step {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (L : ZMod N → ℤ) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    (cyclicGapFreimanImageF Q L).eval x =
      (cyclicGapFreimanImageF Q L).eval (Q.predParam x i hi) +
        (cyclicGapFreimanImageF Q L).step i := by
  simp only [GAPF.eval, cyclicGapFreimanImageF, dif_pos hradius]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
          (if hj : 0 < Q.radius j then
            L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
        (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) =
      ∑ j, ((x j : ℕ) : ℤ) *
          (if hj : 0 < Q.radius j then
            L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => ((x j : ℕ) : ℤ) *
        (if hj : 0 < Q.radius j then
          L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0))
      (Finset.mem_univ i)]
    have hrest :
        ∑ j ∈ Finset.univ.erase i, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) =
          ∑ j ∈ Finset.univ.erase i, ((x j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)]
    rw [hrest, Q.predParam_apply_self]
    simp only [dif_pos hradius]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    have hxiZ : (((x i : ℕ) - 1 : ℕ) : ℤ) + 1 = (x i : ℤ) := by
      exact_mod_cast hxi
    linear_combination
      (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) * hxiZ
  calc
    L (Q.eval Q.minParam) +
          ∑ j, ((x j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) =
        L (Q.eval Q.minParam) +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
            (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam))) := by
              rw [hsum]
    _ = (L (Q.eval Q.minParam) +
          ∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
          (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) := by
            ring

/-- A Freiman-additive map on the carrier of a cyclic GAP agrees with the
coordinatewise affine linearization. -/
theorem eval_cyclicGapFreimanImageF {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (D : Finset (ZMod N))
    (hQD : Q.carrier ⊆ D) (L : ZMod N → ℤ)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d)
    (x : Q.Param) :
    (cyclicGapFreimanImageF Q L).eval x = L (Q.eval x) := by
  classical
  have hmem (y : Q.Param) : Q.eval y ∈ D := by
    apply hQD
    exact Q.mem_carrier_iff.mpr ⟨y, rfl⟩
  induction hweight : (∑ i, (x i : ℕ)) using Nat.strong_induction_on generalizing x with
  | h k ih =>
      by_cases hk : k = 0
      · have hsumzero : ∑ i, (x i : ℕ) = 0 := hweight.trans hk
        have hxzero (i : Fin Q.rank) : (x i : ℕ) = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun _ _ => Nat.zero_le _)).mp hsumzero i (Finset.mem_univ i)
        have hx : x = Q.minParam := by
          funext i
          apply Fin.ext
          exact hxzero i
        subst x
        simp [GAPF.eval, cyclicGapFreimanImageF, CyclicGAPF.minParam]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hsumpos : 0 < ∑ i, (x i : ℕ) := by omega
        rw [Finset.sum_pos_iff_of_nonneg (by simp)] at hsumpos
        obtain ⟨i, _hiuniv, hi⟩ := hsumpos
        have hradius : 0 < Q.radius i := by
          have hix := (x i).isLt
          change (x i : ℕ) < 2 * Q.radius i + 1 at hix
          omega
        let y := Q.predParam x i hi
        have hyweight : (∑ j, (y j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
          exact Q.sum_predParam_add_one x i hi
        have hylt : (∑ j, (y j : ℕ)) < k := by omega
        have ihy : (cyclicGapFreimanImageF Q L).eval y = L (Q.eval y) :=
          ih _ hylt y rfl
        have hrel : L (Q.eval y) + L (Q.eval (Q.unitParam i hradius)) =
            L (Q.eval x) + L (Q.eval Q.minParam) := by
          apply hadd (hmem y) (hmem (Q.unitParam i hradius))
            (hmem x) (hmem Q.minParam)
          exact Q.eval_predParam_add_eval_unitParam x i hi hradius
        rw [eval_cyclicGapFreimanImageF_pred_add_step Q L x i hi hradius, ihy]
        simp only [cyclicGapFreimanImageF, dif_pos hradius]
        omega

lemma proper_cyclicGapFreimanImageF {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (hQ : Q.Proper)
    (D : Finset (ZMod N)) (hQD : Q.carrier ⊆ D)
    (L : ZMod N → ℤ) (hLinj : Set.InjOn L D)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d) :
    (cyclicGapFreimanImageF Q L).Proper := by
  intro x y hxy
  have hx := eval_cyclicGapFreimanImageF Q D hQD L hadd x
  have hy := eval_cyclicGapFreimanImageF Q D hQD L hadd y
  rw [hx, hy] at hxy
  apply hQ
  exact hLinj (hQD (Q.mem_carrier_iff.mpr ⟨x, rfl⟩))
    (hQD (Q.mem_carrier_iff.mpr ⟨y, rfl⟩)) hxy

lemma carrier_cyclicGapFreimanImageF {N : ℕ} [NeZero N]
    (Q : CyclicGAPF N) (D : Finset (ZMod N))
    (hQD : Q.carrier ⊆ D) (L : ZMod N → ℤ)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d) :
    (cyclicGapFreimanImageF Q L).carrier = Q.carrier.image L := by
  ext z
  simp only [GAPF.mem_carrier_iff, Finset.mem_image]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Q.eval x, ?_, ?_⟩
    · exact Q.mem_carrier_iff.mpr ⟨x, rfl⟩
    · exact (eval_cyclicGapFreimanImageF Q D hQD L hadd x).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx⟩ := Q.mem_carrier_iff.mp hw
    refine ⟨x, ?_⟩
    simpa only [hx] using (eval_cyclicGapFreimanImageF Q D hQD L hadd x)

/-- Directly lift a proper cyclic GAP through an order-eight Freiman model to
our integer `GAPF`, with no rank or cardinality loss. -/
theorem exists_proper_GAPF_lift_of_cyclic
    {N : ℕ} [NeZero N]
    (A : Finset ℤ) (B : Finset (ZMod N)) (hB : B.Nonempty)
    (f : ℤ → ZMod N)
    (hf : IsAddFreimanIso 8 (A : Set ℤ) (B : Set (ZMod N)) f)
    (Q : CyclicGAPF N) (hQproper : Q.Proper)
    (hQsub : Q.carrier ⊆ 2 • B - 2 • B) :
    ∃ P : GAPF,
      P.rank = Q.rank ∧
      P.Proper ∧
      P.carrier ⊆ 2 • A - 2 • A ∧
      P.carrier.card = Q.carrier.card := by
  let g : ZMod N → ℤ := Function.invFunOn f (A : Set ℤ)
  have hg : IsAddFreimanIso 8 (B : Set (ZMod N)) (A : Set ℤ) g := by
    simpa only [g] using hf.invFunOn
  let D : Finset (ZMod N) := 2 • B - 2 • B
  let L : ZMod N → ℤ := freimanFourfoldLiftF B hB g
  have hLinj : Set.InjOn L D := by
    simpa only [L, D] using
      (freimanFourfoldLiftF_injOn hB (hg.mono (hmn := by omega)))
  have hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d := by
    intro a b c d ha hb hc hd hab
    exact (freimanFourfoldLiftF_add_eq_add hB hg ha hb hc hd).mpr hab
  let P : GAPF := cyclicGapFreimanImageF Q L
  have hPproper : P.Proper := by
    exact proper_cyclicGapFreimanImageF Q hQproper D hQsub L hLinj hadd
  have hPcarrier : P.carrier = Q.carrier.image L := by
    exact carrier_cyclicGapFreimanImageF Q D hQsub L hadd
  refine ⟨P, rfl, hPproper, ?_, ?_⟩
  · rw [hPcarrier]
    intro z hz
    obtain ⟨x, hxQ, rfl⟩ := Finset.mem_image.mp hz
    exact freimanFourfoldLiftF_mem_two_nsmul_sub_two_nsmul hB
      hg.bijOn.mapsTo (hQsub hxQ)
  · rw [hPcarrier]
    exact Finset.card_image_of_injOn (hLinj.mono hQsub)

end

end Jsp000216

import Jsp000216.GAPCoverInterface

open scoped BigOperators Pointwise

namespace Jsp000216

namespace GAPF

/-- A GAP containing every difference of two points of `P`. -/
def differenceAP (P : GAPF) : GAPF where
  rank := P.rank
  base := -∑ i, (P.length i : ℤ) * P.step i
  step := P.step
  length i := 2 * P.length i

def differenceParam (P : GAPF) (x y : P.Param) :
    P.differenceAP.Param := fun i =>
  ⟨P.length i + (x i : ℕ) - (y i : ℕ), by
    have hx := (x i).isLt
    have hy := (y i).isLt
    dsimp [differenceAP]
    omega⟩

lemma eval_differenceParam (P : GAPF) (x y : P.Param) :
    P.differenceAP.eval (P.differenceParam x y) = P.eval x - P.eval y := by
  simp only [eval, differenceAP, differenceParam]
  have hcast (i : Fin P.rank) :
      ((P.length i + (x i : ℕ) - (y i : ℕ) : ℕ) : ℤ) =
        (P.length i : ℤ) + (x i : ℤ) - (y i : ℤ) := by
    have hy := (y i).isLt
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp_rw [hcast]
  change (-∑ i : Fin P.rank, (P.length i : ℤ) * P.step i) +
      ∑ i : Fin P.rank,
        ((P.length i : ℤ) + (x i : ℤ) - (y i : ℤ)) * P.step i =
    P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i -
      (P.base + ∑ i : Fin P.rank, (y i : ℤ) * P.step i)
  have hsum :
      (∑ i : Fin P.rank,
          ((P.length i : ℤ) + (x i : ℤ) - (y i : ℤ)) * P.step i) =
        (∑ i : Fin P.rank, (P.length i : ℤ) * P.step i) +
          (∑ i : Fin P.rank, (x i : ℤ) * P.step i) -
            (∑ i : Fin P.rank, (y i : ℤ) * P.step i) := by
    calc
      (∑ i : Fin P.rank,
          ((P.length i : ℤ) + (x i : ℤ) - (y i : ℤ)) * P.step i) =
          ∑ i : Fin P.rank,
            ((P.length i : ℤ) * P.step i +
              (x i : ℤ) * P.step i - (y i : ℤ) * P.step i) := by
                congr 1
                funext i
                ring
      _ = (∑ i : Fin P.rank, (P.length i : ℤ) * P.step i) +
          (∑ i : Fin P.rank, (x i : ℤ) * P.step i) -
            (∑ i : Fin P.rank, (y i : ℤ) * P.step i) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsum]
  ring

lemma sub_carrier_subset_differenceAP (P : GAPF) :
    P.carrier - P.carrier ⊆ P.differenceAP.carrier := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨x, hx⟩ := P.mem_carrier_iff.mp hu
  obtain ⟨y, hy⟩ := P.mem_carrier_iff.mp hv
  rw [← hx, ← hy]
  exact P.differenceAP.mem_carrier_iff.mpr
    ⟨P.differenceParam x y, P.eval_differenceParam x y⟩

@[simp] lemma rank_differenceAP (P : GAPF) :
    P.differenceAP.rank = P.rank := rfl

lemma boxCard_differenceAP_le (P : GAPF) :
    P.differenceAP.boxCard ≤ 2 ^ P.rank * P.boxCard := by
  change (∏ i : Fin P.rank, (2 * P.length i + 1)) ≤
    2 ^ P.rank * ∏ i : Fin P.rank, (P.length i + 1)
  calc
    (∏ i : Fin P.rank, (2 * P.length i + 1)) ≤
        ∏ i : Fin P.rank, (2 * (P.length i + 1)) := by
      gcongr with i
      omega
    _ = (∏ _i : Fin P.rank, 2) *
        (∏ i : Fin P.rank, (P.length i + 1)) := by
      rw [← Finset.prod_mul_distrib]
    _ = 2 ^ P.rank * ∏ i : Fin P.rank, (P.length i + 1) := by simp

/-- Add one binary generator for every element of a finite translating set. -/
noncomputable def translateCoverAP (P : GAPF) (F : Finset ℤ) : GAPF where
  rank := P.rank + F.card
  base := P.base
  step := Fin.addCases P.step (fun j => (F.equivFin.symm j : ℤ))
  length := Fin.addCases P.length (fun _ => 1)

noncomputable def translateCoverParam (P : GAPF) (F : Finset ℤ)
    (x : P.Param) (j : Fin F.card) : (P.translateCoverAP F).Param :=
  Fin.addCases
    (fun i => ⟨x i, by
      simpa only [translateCoverAP, Fin.addCases_left] using (x i).isLt⟩)
    (fun k => if hkj : k = j then
      ⟨1, by simp [translateCoverAP]⟩ else 0)

lemma eval_translateCoverParam (P : GAPF) (F : Finset ℤ)
    (x : P.Param) (j : Fin F.card) :
    (P.translateCoverAP F).eval (P.translateCoverParam F x j) =
      P.eval x + (F.equivFin.symm j : ℤ) := by
  change P.base +
      ∑ i : Fin (P.rank + F.card),
        ((P.translateCoverParam F x j i : ℕ) : ℤ) *
          (P.translateCoverAP F).step i =
    P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i +
      (F.equivFin.symm j : ℤ)
  rw [Fin.sum_univ_add]
  simp only [translateCoverParam, translateCoverAP,
    Fin.addCases_left, Fin.addCases_right]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro k hk hkj
    simp [hkj]
  · simp

lemma add_subset_translateCoverAP (P : GAPF) (F : Finset ℤ) :
    F + P.carrier ⊆ (P.translateCoverAP F).carrier := by
  intro z hz
  obtain ⟨f, hf, p, hp, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨x, hx⟩ := P.mem_carrier_iff.mp hp
  let j : Fin F.card := F.equivFin ⟨f, hf⟩
  apply (P.translateCoverAP F).mem_carrier_iff.mpr
  refine ⟨P.translateCoverParam F x j, ?_⟩
  rw [P.eval_translateCoverParam F x j, hx]
  have hj : (F.equivFin.symm j : F) = ⟨f, hf⟩ := by
    exact F.equivFin.symm_apply_apply ⟨f, hf⟩
  have hjval : (F.equivFin.symm j : ℤ) = f := congrArg Subtype.val hj
  rw [hjval]
  exact add_comm p f

@[simp] lemma rank_translateCoverAP (P : GAPF) (F : Finset ℤ) :
    (P.translateCoverAP F).rank = P.rank + F.card := rfl

lemma boxCard_translateCoverAP (P : GAPF) (F : Finset ℤ) :
    (P.translateCoverAP F).boxCard = P.boxCard * 2 ^ F.card := by
  change (∏ i : Fin (P.rank + F.card),
      (Fin.addCases P.length (fun _ => 1) i + 1)) =
    (∏ i : Fin P.rank, (P.length i + 1)) * 2 ^ F.card
  rw [Fin.prod_univ_add]
  simp

lemma boxCard_translateCoverAP_differenceAP_le (P : GAPF)
    (hP : P.Proper) (F : Finset ℤ) :
    (P.differenceAP.translateCoverAP F).boxCard ≤
      2 ^ (P.rank + F.card) * P.carrier.card := by
  rw [boxCard_translateCoverAP, P.card_carrier_of_proper hP]
  calc
    P.differenceAP.boxCard * 2 ^ F.card ≤
        (2 ^ P.rank * P.boxCard) * 2 ^ F.card :=
      Nat.mul_le_mul_right _ P.boxCard_differenceAP_le
    _ = 2 ^ (P.rank + F.card) * P.boxCard := by
      rw [pow_add]
      ring

end GAPF

/-- Natural-number form of Ruzsa covering for integer finsets. -/
lemma ruzsa_covering_intF {A B : Finset ℤ} {K : ℕ} (hB : B.Nonempty)
    (hsmall : (A + B).card ≤ K * B.card) :
    ∃ F ⊆ A, F.card ≤ K ∧ A ⊆ F + (B - B) := by
  have hsmall' : ((A + B).card : ℝ) ≤ (K : ℝ) * (B.card : ℝ) := by
    exact_mod_cast hsmall
  obtain ⟨F, hFA, hFK, hcover⟩ := Finset.ruzsa_covering_add hB hsmall'
  refine ⟨F, hFA, ?_, hcover⟩
  exact_mod_cast hFK

/-- Natural-number consequence of Plünnecke--Ruzsa. -/
lemma pluennecke_ruzsa_intF {A B : Finset ℤ} {K m n : ℕ} (hA : A.Nonempty)
    (hsmall : (A + B).card ≤ K * A.card) :
    (m • B - n • B).card ≤ K ^ (m + n) * A.card := by
  have hratio :
      ((A + B).card : ℚ≥0) / (A.card : ℚ≥0) ≤ (K : ℚ≥0) := by
    rw [div_le_iff₀]
    · exact_mod_cast hsmall
    · exact_mod_cast hA.card_pos
  have hbound := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
  have hbound' :
      ((m • B - n • B).card : ℚ≥0) ≤
        (K : ℚ≥0) ^ (m + n) * (A.card : ℚ≥0) := by
    refine hbound.trans ?_
    gcongr
  exact_mod_cast hbound'

/-- The only genuinely structural input still needed for the weak GAP cover:
a large proper bounded-rank GAP core inside the fourfold difference set. -/
def DenseGAPCoreF (K R D : ℕ) : Prop :=
  ∀ A : Finset ℤ, A.Nonempty →
    (A + A).card ≤ K * A.card →
      ∃ P : GAPF,
        P.rank ≤ R ∧
        P.Proper ∧
        P.carrier ⊆ 2 • A - 2 • A ∧
        A.card ≤ D * P.carrier.card

/-- A dense bounded-rank core implies exactly the uniform GAP-cover interface
used by the infinite gap argument.  No properization of the final cover is
needed. -/
theorem uniformGAPCoverF_of_denseCore {K R D : ℕ}
    (hK : 1 ≤ K) (hcore : DenseGAPCoreF K R D) :
    UniformGAPCoverF K (R + K ^ 5 * D)
      (2 ^ (R + K ^ 5 * D) * K ^ 4) := by
  intro A hA hsmall
  obtain ⟨P, hPrank, hPproper, hPsub, hPlarge⟩ := hcore A hA hsmall
  have hPne : P.carrier.Nonempty := by
    apply Finset.card_pos.mp
    have hApos := Finset.card_pos.mpr hA
    by_contra hzero
    have hz : P.carrier.card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hz, mul_zero] at hPlarge
    omega
  have hAPsub : A + P.carrier ⊆ 3 • A - 2 • A := by
    intro z hz
    obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, hpval⟩ := Finset.mem_sub.mp (hPsub hp)
    apply Finset.mem_sub.mpr
    refine ⟨a + u, ?_, v, hv, ?_⟩
    · rw [show 3 • A = A + 2 • A by simp [succ_nsmul, add_comm]]
      exact Finset.mem_add.mpr ⟨a, ha, u, hu, rfl⟩
    · rw [← hpval]
      abel
  have hAPcard : (A + P.carrier).card ≤ (K ^ 5 * D) * P.carrier.card := by
    have hfive := pluennecke_ruzsa_intF hA hsmall (m := 3) (n := 2)
    calc
      (A + P.carrier).card ≤ (3 • A - 2 • A).card :=
        Finset.card_le_card hAPsub
      _ ≤ K ^ 5 * A.card := by simpa using hfive
      _ ≤ K ^ 5 * (D * P.carrier.card) := Nat.mul_le_mul_left _ hPlarge
      _ = (K ^ 5 * D) * P.carrier.card := by ring
  obtain ⟨F, hFA, hFcard, hcover⟩ := ruzsa_covering_intF hPne hAPcard
  let C : GAPF := P.differenceAP.translateCoverAP F
  have hAC : A ⊆ C.carrier := by
    intro a ha
    have haCover := hcover ha
    obtain ⟨f, hf, d, hd, rfl⟩ := Finset.mem_add.mp haCover
    apply P.differenceAP.add_subset_translateCoverAP F
    exact Finset.mem_add.mpr
      ⟨f, hf, d, P.sub_carrier_subset_differenceAP hd, rfl⟩
  have hCrank : C.rank ≤ R + K ^ 5 * D := by
    change P.rank + F.card ≤ R + K ^ 5 * D
    exact Nat.add_le_add hPrank hFcard
  have hPupper : P.carrier.card ≤ K ^ 4 * A.card := by
    have hfour := pluennecke_ruzsa_intF hA hsmall (m := 2) (n := 2)
    exact (Finset.card_le_card hPsub).trans (by simpa using hfour)
  have hCbox : C.boxCard ≤
      (2 ^ (R + K ^ 5 * D) * K ^ 4) * A.card := by
    calc
      C.boxCard ≤ 2 ^ (P.rank + F.card) * P.carrier.card :=
        P.boxCard_translateCoverAP_differenceAP_le hPproper F
      _ ≤ 2 ^ (R + K ^ 5 * D) * P.carrier.card := by
        exact Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by omega) hCrank)
      _ ≤ 2 ^ (R + K ^ 5 * D) * (K ^ 4 * A.card) :=
        Nat.mul_le_mul_left _ hPupper
      _ = (2 ^ (R + K ^ 5 * D) * K ^ 4) * A.card := by ring
  exact ⟨C, hCrank, hAC, hCbox⟩

end Jsp000216

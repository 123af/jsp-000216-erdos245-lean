import Jsp000216.GAPCoverReduction
import Jsp000216.CyclicGapLinearize

open scoped BigOperators Pointwise

namespace Jsp000216

noncomputable section

/-- Uniform cyclic-group form of the one remaining structural input.
At fixed density loss `q`, it asks for a large proper bounded-rank cyclic GAP
inside the fourfold difference set. -/
def UniformCyclicDenseCoreF (q R D : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N], 1 < N →
    ∀ B : Finset (ZMod N), B.Nonempty →
      N ≤ q * B.card →
        ∃ Q : CyclicGAPF N,
          Q.rank ≤ R ∧
          Q.Proper ∧
          Q.carrier ⊆ 2 • B - 2 • B ∧
          B.card ≤ D * Q.carrier.card

/-- Ruzsa's order-eight cyclic model plus the direct Freiman lift reduce the
integer dense-core theorem to a purely cyclic dense-core theorem. -/
theorem denseGAPCoreF_of_cyclicDenseCore {K R D : ℕ}
    (hK : 1 ≤ K)
    (hcyc : UniformCyclicDenseCoreF (32 * K ^ 16) R D) :
    DenseGAPCoreF K R (16 * D) := by
  intro A hA hsmall
  have hEne : (8 • A - 8 • A).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate 8 a).sum ∈ 8 • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate 8 a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hEcard : (8 • A - 8 • A).card ≤ K ^ 16 * A.card := by
    have h := pluennecke_ruzsa_intF hA hsmall (m := 8) (n := 8)
    simpa using h
  have hmodel := exists_large_cyclic_freiman_modelF A 8 hA (by omega)
  dsimp only at hmodel
  obtain ⟨A', B, f, hA'ne, hA'sub, hA'card, hB, hf⟩ := hmodel
  subst B
  have hBne : (A'.image f).Nonempty := by
    obtain ⟨a, ha⟩ := hA'ne
    exact ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  have hBcard : (A'.image f).card = A'.card := by
    exact Finset.card_image_of_injOn hf.bijOn.injOn
  have hNpos : 0 < 2 * (8 • A - 8 • A).card := by
    have := Finset.card_pos.mpr hEne
    omega
  letI : NeZero (2 * (8 • A - 8 • A).card) := ⟨hNpos.ne'⟩
  have hNtwo : 1 < 2 * (8 • A - 8 • A).card := by omega
  have hdense :
      2 * (8 • A - 8 • A).card ≤
        (32 * K ^ 16) * (A'.image f).card := by
    calc
      2 * (8 • A - 8 • A).card ≤ 2 * (K ^ 16 * A.card) :=
        Nat.mul_le_mul_left 2 hEcard
      _ ≤ 2 * (K ^ 16 * (16 * A'.card)) := by
        gcongr
      _ = (32 * K ^ 16) * (A'.image f).card := by
        rw [hBcard]
        ring
  obtain ⟨Q, hQrank, hQproper, hQsub, hQlarge⟩ :=
    hcyc (2 * (8 • A - 8 • A).card) hNtwo (A'.image f) hBne hdense
  obtain ⟨P, hPrank, hPproper, hPsub, hPcard⟩ :=
    exists_proper_GAPF_lift_of_cyclic A' (A'.image f) hBne f hf
      Q hQproper hQsub
  have hPsubA : P.carrier ⊆ 2 • A - 2 • A := by
    have h2sub : 2 • A' ⊆ 2 • A := nsmul_le_nsmul_right hA'sub 2
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp (hPsub hz)
    exact Finset.mem_sub.mpr ⟨u, h2sub hu, v, h2sub hv, rfl⟩
  have hPlarge : A.card ≤ (16 * D) * P.carrier.card := by
    calc
      A.card ≤ 16 * A'.card := by simpa using hA'card
      _ = 16 * (A'.image f).card := by rw [hBcard]
      _ ≤ 16 * (D * Q.carrier.card) := Nat.mul_le_mul_left 16 hQlarge
      _ = (16 * D) * P.carrier.card := by
        rw [hPcard]
        ring
  refine ⟨P, ?_, hPproper, hPsubA, hPlarge⟩
  rw [hPrank]
  exact hQrank

end

end Jsp000216

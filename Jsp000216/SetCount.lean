import Jsp000216.FiniteThreeK

open Filter Set
open scoped Pointwise Topology

namespace Jsp000216

noncomputable section

/-- Elements of `S` in the positive finite window `[1,N]`. -/
noncomputable def windowF (S : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n => n ∈ S

/-- Counting function for positive elements of `S` up to `N`. -/
noncomputable def countInF (S : Set ℕ) (N : ℕ) : ℕ :=
  (windowF S N).card

@[simp] lemma mem_windowF {S : Set ℕ} {N x : ℕ} :
    x ∈ windowF S N ↔ 1 ≤ x ∧ x ≤ N ∧ x ∈ S := by
  classical
  simp [windowF, and_assoc]

lemma countInF_eq_ncard (S : Set ℕ) (N : ℕ) :
    countInF S N = (S ∩ Set.Icc 1 N).ncard := by
  classical
  rw [countInF, windowF, ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_left_comm, and_comm]

lemma countInF_mono_set {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    countInF S N ≤ countInF T N := by
  classical
  unfold countInF windowF
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

lemma countInF_mono_nat (S : Set ℕ) : Monotone (countInF S) := by
  intro M N hMN
  classical
  unfold countInF windowF
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hMN⟩, hn.2⟩

/-- Increasing enumeration of an infinite subset of the naturals. -/
noncomputable def enumerateF (S : Set ℕ) : ℕ → ℕ :=
  Nat.nth fun n => n ∈ S

lemma enumerateF_strictMono {S : Set ℕ} (hS : S.Infinite) :
    StrictMono (enumerateF S) :=
  Nat.nth_strictMono hS

lemma enumerateF_mem {S : Set ℕ} (hS : S.Infinite) (i : ℕ) :
    enumerateF S i ∈ S :=
  Nat.nth_mem_of_infinite hS i

lemma range_enumerateF {S : Set ℕ} (hS : S.Infinite) :
    Set.range (enumerateF S) = S :=
  Nat.range_nth_of_infinite hS

lemma countInF_enumerate_ge {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Set.Ici 1) (k : ℕ) :
    k + 1 ≤ countInF S (enumerateF S k) := by
  classical
  let F : Fin (k + 1) → ℕ := fun i => enumerateF S i
  have hF_inj : Function.Injective F := by
    intro i j hij
    apply Fin.ext
    exact (enumerateF_strictMono hS).injective hij
  have hF_mem (i : Fin (k + 1)) :
      F i ∈ S ∩ Set.Icc 1 (enumerateF S k) := by
    have hi : i.1 ≤ k := by omega
    exact ⟨enumerateF_mem hS i,
      hpos (enumerateF_mem hS i),
      (enumerateF_strictMono hS).monotone hi⟩
  rw [countInF_eq_ncard]
  calc
    k + 1 = (Set.range F).ncard := by
      rw [Set.ncard_range_of_injective hF_inj]
      simp
    _ ≤ (S ∩ Set.Icc 1 (enumerateF S k)).ncard := by
      apply Set.ncard_le_ncard
        (ht := (Set.finite_Icc 1 (enumerateF S k)).subset Set.inter_subset_right)
      rintro x ⟨i, rfl⟩
      exact hF_mem i

lemma countInF_tendsto_atTop {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Set.Ici 1) :
    Tendsto (countInF S) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨enumerateF S k, ?_⟩
  intro N hN
  exact (Nat.le_succ k).trans
    ((countInF_enumerate_ge hS hpos k).trans (countInF_mono_nat S hN))

lemma eventually_countInF_pos {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Set.Ici 1) :
    ∀ᶠ N in atTop, 0 < countInF S N := by
  exact (countInF_tendsto_atTop hS hpos).eventually (eventually_gt_atTop 0)

lemma countInF_enumerate_eq {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Set.Ici 1) (i : ℕ) :
    countInF S (enumerateF S i) = i + 1 := by
  classical
  let F : Finset ℕ :=
    (Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) => enumerateF S j.1)
  have hFinj : Function.Injective
      (fun j : Fin (i + 1) => enumerateF S j.1) :=
    (enumerateF_strictMono hS).injective.comp Fin.val_injective
  have hFcard : F.card = i + 1 := by
    change ((Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) => enumerateF S j.1)).card = i + 1
    calc
      _ = (Finset.univ : Finset (Fin (i + 1))).card :=
        Finset.card_image_of_injective _ hFinj
      _ = i + 1 := by simp
  have hFeq : F = windowF S (enumerateF S i) := by
    ext x
    change x ∈ (Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) => enumerateF S j.1) ↔
        x ∈ windowF S (enumerateF S i)
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
      have hji : j.1 ≤ i := by omega
      exact mem_windowF.mpr
        ⟨hpos (enumerateF_mem hS j),
          (enumerateF_strictMono hS).monotone hji,
          enumerateF_mem hS j⟩
    · intro hx
      have hxS := (mem_windowF.mp hx).2.2
      rw [← range_enumerateF hS] at hxS
      rcases hxS with ⟨j, rfl⟩
      have hji : j ≤ i :=
        (enumerateF_strictMono hS).le_iff_le.mp (mem_windowF.mp hx).2.1
      apply Finset.mem_image.mpr
      exact ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩
  rw [countInF, ← hFeq, hFcard]

lemma enumerateF_le_iff_lt_countInF {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Set.Ici 1) (i N : ℕ) :
    enumerateF S i ≤ N ↔ i < countInF S N := by
  constructor
  · intro hiN
    have hmono := countInF_mono_nat S hiN
    rw [countInF_enumerate_eq hS hpos i] at hmono
    omega
  · intro hicount
    by_contra hnot
    have hNlt : N < enumerateF S i := Nat.lt_of_not_ge hnot
    have hsub : windowF S N ⊂ windowF S (enumerateF S i) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        apply mem_windowF.mpr
        have hx' := mem_windowF.mp hx
        exact ⟨hx'.1, hx'.2.1.trans hNlt.le, hx'.2.2⟩
      · intro heq
        have hemem : enumerateF S i ∈ windowF S (enumerateF S i) :=
          mem_windowF.mpr
            ⟨hpos (enumerateF_mem hS i), le_rfl, enumerateF_mem hS i⟩
        rw [← heq] at hemem
        exact (Nat.not_le_of_gt hNlt) (mem_windowF.mp hemem).2.1
    have hcardlt := Finset.card_lt_card hsub
    change countInF S N < countInF S (enumerateF S i) at hcardlt
    rw [countInF_enumerate_eq hS hpos i] at hcardlt
    omega

lemma windowF_add_subset (S : Set ℕ) (N : ℕ) :
    windowF S N + windowF S N ⊆ windowF (S + S) (2 * N) := by
  intro z hz
  rcases Finset.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
  have hx' := mem_windowF.mp hx
  have hy' := mem_windowF.mp hy
  apply mem_windowF.mpr
  exact ⟨by omega, by omega, Set.add_mem_add hx'.2.2 hy'.2.2⟩

end

end Jsp000216

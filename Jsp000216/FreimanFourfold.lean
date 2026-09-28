import Jsp000216.CyclicModel

open scoped BigOperators Pointwise

namespace Jsp000216

noncomputable section

/-- A presentation of one point of `2B - 2B` by four elements of `B`. -/
structure FourfoldPresentationF (β : Type*) where
  pos₁ : β
  pos₂ : β
  neg₁ : β
  neg₂ : β

namespace FourfoldPresentationF

variable {β : Type*} [AddCommGroup β]

def eval (p : FourfoldPresentationF β) : β :=
  p.pos₁ + p.pos₂ - p.neg₁ - p.neg₂

def Mem (B : Finset β) (p : FourfoldPresentationF β) : Prop :=
  p.pos₁ ∈ B ∧ p.pos₂ ∈ B ∧ p.neg₁ ∈ B ∧ p.neg₂ ∈ B

end FourfoldPresentationF

variable {α β : Type*} [AddCommGroup α] [AddCommGroup β]
  [DecidableEq β]

lemma mem_two_nsmul_sub_two_nsmul_iffF {B : Finset β} {x : β} :
    x ∈ 2 • B - 2 • B ↔
      ∃ p : FourfoldPresentationF β, p.Mem B ∧ p.eval = x := by
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    rw [show 2 • B = B + B by simp [two_nsmul]] at hu hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hv
    refine ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd⟩, ?_⟩
    dsimp only [FourfoldPresentationF.eval]
    rw [← huv, ← hab, ← hcd]
    abel
  · rintro ⟨p, hp, rfl⟩
    apply Finset.mem_sub.mpr
    refine ⟨p.pos₁ + p.pos₂, ?_, p.neg₁ + p.neg₂, ?_, ?_⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.pos₁, hp.1, p.pos₂, hp.2.1, rfl⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.neg₁, hp.2.2.1, p.neg₂, hp.2.2.2, rfl⟩
    · dsimp only [FourfoldPresentationF.eval]
      abel

noncomputable def defaultFourfoldPresentationF (B : Finset β)
    (hB : B.Nonempty) : FourfoldPresentationF β :=
  let b := Classical.choose hB
  ⟨b, b, b, b⟩

noncomputable def selectedFourfoldPresentationF (B : Finset β)
    (hB : B.Nonempty) (x : β) : FourfoldPresentationF β := by
  classical
  exact if hx : ∃ p : FourfoldPresentationF β, p.Mem B ∧ p.eval = x then
      Classical.choose hx
    else defaultFourfoldPresentationF B hB

lemma selectedFourfoldPresentationF_spec (B : Finset β)
    (hB : B.Nonempty) {x : β} (hx : x ∈ 2 • B - 2 • B) :
    (selectedFourfoldPresentationF B hB x).Mem B ∧
      (selectedFourfoldPresentationF B hB x).eval = x := by
  have hex := mem_two_nsmul_sub_two_nsmul_iffF.mp hx
  simp only [selectedFourfoldPresentationF, dif_pos hex]
  exact Classical.choose_spec hex

def fourfoldMapValueF (g : β → α) (p : FourfoldPresentationF β) : α :=
  g p.pos₁ + g p.pos₂ - g p.neg₁ - g p.neg₂

lemma fourfold_sub_eq_iff_cross_addF {G : Type*} [AddCommGroup G]
    (a b c d e f g h : G) :
    a + b - c - d = e + f - g - h ↔
      a + b + g + h = e + f + c + d := by
  constructor
  · intro heq
    calc
      a + b + g + h = (a + b - c - d) + (c + d + g + h) := by abel
      _ = (e + f - g - h) + (c + d + g + h) := by rw [heq]
      _ = e + f + c + d := by abel
  · intro heq
    calc
      a + b - c - d = (a + b + g + h) - (c + d + g + h) := by abel
      _ = (e + f + c + d) - (c + d + g + h) := by rw [heq]
      _ = e + f - g - h := by abel

lemma add_fourfold_sub_eq_iff_cross_addF {G : Type*} [AddCommGroup G]
    (a₁ a₂ c₁ c₂ b₁ b₂ d₁ d₂
      e₁ e₂ g₁ g₂ f₁ f₂ h₁ h₂ : G) :
    (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
        (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) ↔
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
        e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by
  constructor
  · intro heq
    calc
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
          ((a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = ((e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by abel
  · intro heq
    calc
      (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
          (a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = (e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) := by abel

omit [DecidableEq β] in
lemma fourfoldMapValueF_eq_iff_eval_eq
    {A : Set α} {B : Finset β} {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {p r : FourfoldPresentationF β} (hp : p.Mem B) (hr : r.Mem B) :
    fourfoldMapValueF g p = fourfoldMapValueF g r ↔ p.eval = r.eval := by
  let s : Multiset β := p.pos₁ ::ₘ p.pos₂ ::ₘ r.neg₁ ::ₘ r.neg₂ ::ₘ 0
  let t : Multiset β := r.pos₁ ::ₘ r.pos₂ ::ₘ p.neg₁ ::ₘ p.neg₂ ::ₘ 0
  have hsB : ∀ ⦃x⦄, x ∈ s → x ∈ (B : Set β) := by
    intro x hx
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hr.2.2.1, hr.2.2.2]
  have htB : ∀ ⦃x⦄, x ∈ t → x ∈ (B : Set β) := by
    intro x hx
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hr.1, hr.2.1, hp.2.2.1, hp.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = p.pos₁ + p.pos₂ + r.neg₁ + r.neg₂ := by simp [s]; abel
  have ht : t.sum = r.pos₁ + r.pos₂ + p.neg₁ + p.neg₂ := by simp [t]; abel
  have hgs : (s.map g).sum = g p.pos₁ + g p.pos₂ + g r.neg₁ + g r.neg₂ := by
    simp [s]; abel
  have hgt : (t.map g).sum = g r.pos₁ + g r.pos₂ + g p.neg₁ + g p.neg₂ := by
    simp [t]; abel
  rw [hs, ht, hgs, hgt] at hrel
  exact (fourfold_sub_eq_iff_cross_addF
    (g p.pos₁) (g p.pos₂) (g p.neg₁) (g p.neg₂)
    (g r.pos₁) (g r.pos₂) (g r.neg₁) (g r.neg₂)).trans
      (hrel.trans (fourfold_sub_eq_iff_cross_addF
        p.pos₁ p.pos₂ p.neg₁ p.neg₂ r.pos₁ r.pos₂ r.neg₁ r.neg₂).symm)

noncomputable def freimanFourfoldLiftF (B : Finset β) (hB : B.Nonempty)
    (g : β → α) (x : β) : α :=
  fourfoldMapValueF g (selectedFourfoldPresentationF B hB x)

lemma freimanFourfoldLiftF_eq_of_presentation
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {x : β} (hx : x ∈ 2 • B - 2 • B)
    {p : FourfoldPresentationF β} (hp : p.Mem B) (hpx : p.eval = x) :
    freimanFourfoldLiftF B hB g x = fourfoldMapValueF g p := by
  have hs := selectedFourfoldPresentationF_spec B hB hx
  apply (fourfoldMapValueF_eq_iff_eval_eq hg hs.1 hp).mpr
  exact hs.2.trans hpx.symm

lemma freimanFourfoldLiftF_mem_two_nsmul_sub_two_nsmul [DecidableEq α]
    {A : Finset α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : Set.MapsTo g (B : Set β) (A : Set α))
    {x : β} (hx : x ∈ 2 • B - 2 • B) :
    freimanFourfoldLiftF B hB g x ∈ 2 • A - 2 • A := by
  let p := selectedFourfoldPresentationF B hB x
  have hp := selectedFourfoldPresentationF_spec B hB hx
  rw [mem_two_nsmul_sub_two_nsmul_iffF]
  refine ⟨⟨g p.pos₁, g p.pos₂, g p.neg₁, g p.neg₂⟩, ?_, rfl⟩
  exact ⟨hg hp.1.1, hg hp.1.2.1, hg hp.1.2.2.1, hg hp.1.2.2.2⟩

theorem freimanFourfoldLiftF_injOn
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g) :
    Set.InjOn (freimanFourfoldLiftF B hB g) (2 • B - 2 • B : Finset β) := by
  intro x hx y hy hxy
  have hsx := selectedFourfoldPresentationF_spec B hB hx
  have hsy := selectedFourfoldPresentationF_spec B hB hy
  have heval := (fourfoldMapValueF_eq_iff_eval_eq hg hsx.1 hsy.1).mp hxy
  rw [hsx.2, hsy.2] at heval
  exact heval

lemma freimanFourfoldLiftF_add_eq_add
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 8 (B : Set β) A g)
    {x y z w : β}
    (hx : x ∈ 2 • B - 2 • B) (hy : y ∈ 2 • B - 2 • B)
    (hz : z ∈ 2 • B - 2 • B) (hw : w ∈ 2 • B - 2 • B) :
    freimanFourfoldLiftF B hB g x + freimanFourfoldLiftF B hB g y =
        freimanFourfoldLiftF B hB g z + freimanFourfoldLiftF B hB g w ↔
      x + y = z + w := by
  let px := selectedFourfoldPresentationF B hB x
  let py := selectedFourfoldPresentationF B hB y
  let pz := selectedFourfoldPresentationF B hB z
  let pw := selectedFourfoldPresentationF B hB w
  have hpx := selectedFourfoldPresentationF_spec B hB hx
  have hpy := selectedFourfoldPresentationF_spec B hB hy
  have hpz := selectedFourfoldPresentationF_spec B hB hz
  have hpw := selectedFourfoldPresentationF_spec B hB hw
  let s : Multiset β := px.pos₁ ::ₘ px.pos₂ ::ₘ py.pos₁ ::ₘ py.pos₂ ::ₘ
    pz.neg₁ ::ₘ pz.neg₂ ::ₘ pw.neg₁ ::ₘ pw.neg₂ ::ₘ 0
  let t : Multiset β := pz.pos₁ ::ₘ pz.pos₂ ::ₘ pw.pos₁ ::ₘ pw.pos₂ ::ₘ
    px.neg₁ ::ₘ px.neg₂ ::ₘ py.neg₁ ::ₘ py.neg₂ ::ₘ 0
  have hsB : ∀ ⦃a⦄, a ∈ s → a ∈ (B : Set β) := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpx.1.1, hpx.1.2.1, hpy.1.1, hpy.1.2.1,
      hpz.1.2.2.1, hpz.1.2.2.2, hpw.1.2.2.1, hpw.1.2.2.2]
  have htB : ∀ ⦃a⦄, a ∈ t → a ∈ (B : Set β) := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpz.1.1, hpz.1.2.1, hpw.1.1, hpw.1.2.1,
      hpx.1.2.2.1, hpx.1.2.2.2, hpy.1.2.2.1, hpy.1.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = px.pos₁ + px.pos₂ + py.pos₁ + py.pos₂ +
      pz.neg₁ + pz.neg₂ + pw.neg₁ + pw.neg₂ := by simp [s]; abel
  have ht : t.sum = pz.pos₁ + pz.pos₂ + pw.pos₁ + pw.pos₂ +
      px.neg₁ + px.neg₂ + py.neg₁ + py.neg₂ := by simp [t]; abel
  have hgs : (s.map g).sum = g px.pos₁ + g px.pos₂ + g py.pos₁ + g py.pos₂ +
        g pz.neg₁ + g pz.neg₂ + g pw.neg₁ + g pw.neg₂ := by simp [s]; abel
  have hgt : (t.map g).sum = g pz.pos₁ + g pz.pos₂ + g pw.pos₁ + g pw.pos₂ +
        g px.neg₁ + g px.neg₂ + g py.neg₁ + g py.neg₂ := by simp [t]; abel
  rw [hs, ht, hgs, hgt] at hrel
  have hmapCross := add_fourfold_sub_eq_iff_cross_addF
    (g px.pos₁) (g px.pos₂) (g px.neg₁) (g px.neg₂)
    (g py.pos₁) (g py.pos₂) (g py.neg₁) (g py.neg₂)
    (g pz.pos₁) (g pz.pos₂) (g pz.neg₁) (g pz.neg₂)
    (g pw.pos₁) (g pw.pos₂) (g pw.neg₁) (g pw.neg₂)
  have horiginalCross := add_fourfold_sub_eq_iff_cross_addF
    px.pos₁ px.pos₂ px.neg₁ px.neg₂ py.pos₁ py.pos₂ py.neg₁ py.neg₂
    pz.pos₁ pz.pos₂ pz.neg₁ pz.neg₂ pw.pos₁ pw.pos₂ pw.neg₁ pw.neg₂
  have hvalues : px.eval + py.eval = pz.eval + pw.eval ↔ x + y = z + w := by
    rw [hpx.2, hpy.2, hpz.2, hpw.2]
  exact hmapCross.trans (hrel.trans (horiginalCross.symm.trans hvalues))

theorem freimanFourfoldLiftF_isAddFreimanIso
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 8 (B : Set β) A g) :
    IsAddFreimanIso 2 ((2 • B - 2 • B : Finset β) : Set β)
      ((freimanFourfoldLiftF B hB g) '' ((2 • B - 2 • B : Finset β) : Set β))
      (freimanFourfoldLiftF B hB g) := by
  rw [isAddFreimanIso_two]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · exact freimanFourfoldLiftF_injOn hB (hg.mono (hmn := by omega))
    · intro y hy
      exact hy
  · intro x hx y hy z hz w hw
    exact freimanFourfoldLiftF_add_eq_add hB hg hx hy hz hw

end

end Jsp000216

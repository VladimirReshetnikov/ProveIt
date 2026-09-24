import CoarseDegrees.Generic

/-!
# Budget forcing and the bridge lemma in forcing form

This file contains the combinatorial core of research report 10
(`docs/coarse-degrees/research-reports/10/coarse_hyperdegrees.tex`, Section 4), with nothing admitted.

* A `Budget` is a family of finite sets of positions, closed under subsets, with a *one-bit
  reserve*: every member can absorb any one sufficiently large new position.
* `Cond 𝔅` is the forcing of pairs of equal-length binary strings whose disagreement set lies in
  the budget.
* A `DecSys` is an abstract "decision system" on strings: a relation `dec σ ψ n b`
  ("the condition `σ` decides the `n`-th instance of the name `ψ` as `b`") that persists under
  extension, is consistent, and has dense domain.  Cohen forcing for ranked sentences is one; so
  is convergence of a total Turing functional.
* `bridge` is the bridge lemma (report 10, Lemma 4.2): below a padded condition with no
  cross-disagreement extension, all deciding extensions of the first coordinate agree.
* `exists_generic_pair` builds sets `A`, `B` by meeting countably many dense sets: both meet a
  prescribed family of dense sets of strings, `A △ B` obeys the budget, both decide every
  instance, and for every pair of names on which they agree, the common value is determined by
  the decision relation above a single initial segment of `A`.
-/

noncomputable section

open scoped Classical

namespace CoarseDegrees

/-! ## Disagreement sets of strings -/

/-- The set of positions at which two strings disagree. -/
def diff (σ τ : List Bool) : Finset ℕ :=
  (Finset.range σ.length).filter (fun i => σ[i]? ≠ τ[i]?)

theorem mem_diff {σ τ : List Bool} {k : ℕ} :
    k ∈ diff σ τ ↔ k < σ.length ∧ σ[k]? ≠ τ[k]? := by
  simp [diff]

@[simp] theorem diff_self (σ : List Bool) : diff σ σ = ∅ := by
  ext k
  simp [mem_diff]

theorem mem_diff_append {σ τ u v : List Bool} (h : σ.length = τ.length) {k : ℕ} :
    k ∈ diff (σ ++ u) (τ ++ v) ↔
      k ∈ diff σ τ ∨ (σ.length ≤ k ∧ k - σ.length ∈ diff u v) := by
  simp only [mem_diff, List.length_append]
  by_cases hk : k < σ.length
  · have hk' : k < τ.length := h ▸ hk
    rw [List.getElem?_append_left hk, List.getElem?_append_left hk']
    constructor
    · intro hne
      exact Or.inl ⟨hk, hne.2⟩
    · rintro (hne | ⟨hle, -⟩)
      · exact ⟨by omega, hne.2⟩
      · omega
  · have hk1 : σ.length ≤ k := not_lt.mp hk
    have hk2 : τ.length ≤ k := h ▸ hk1
    rw [List.getElem?_append_right hk1, List.getElem?_append_right hk2, ← h]
    constructor
    · rintro ⟨hlt, hne⟩
      exact Or.inr ⟨hk1, by omega, hne⟩
    · rintro (⟨hlt, -⟩ | ⟨-, hlt, hne⟩)
      · omega
      · exact ⟨by omega, hne⟩

theorem diff_append_same {σ τ : List Bool} (h : σ.length = τ.length) (u : List Bool) :
    diff (σ ++ u) (τ ++ u) = diff σ τ := by
  ext k
  rw [mem_diff_append h]
  simp

/-- The hybrid of `u₁` (before position `i`) and `u₀` (from position `i` on). -/
def hybrid (u₀ u₁ : List Bool) (i : ℕ) : List Bool := u₁.take i ++ u₀.drop i

theorem length_hybrid {u₀ u₁ : List Bool} (h : u₀.length = u₁.length) {i : ℕ}
    (hi : i ≤ u₀.length) : (hybrid u₀ u₁ i).length = u₀.length := by
  simp [hybrid]
  omega

theorem getElem?_hybrid {u₀ u₁ : List Bool} (h : u₀.length = u₁.length) {i : ℕ}
    (hi : i ≤ u₀.length) (j : ℕ) :
    (hybrid u₀ u₁ i)[j]? = if j < i then u₁[j]? else u₀[j]? := by
  unfold hybrid
  have hlen : (u₁.take i).length = i := by simp; omega
  by_cases hj : j < i
  · rw [List.getElem?_append_left (by omega), if_pos hj, List.getElem?_take_of_lt hj]
  · rw [List.getElem?_append_right (by omega), if_neg hj, hlen, List.getElem?_drop]
    congr 1
    omega

theorem hybrid_zero (u₀ u₁ : List Bool) : hybrid u₀ u₁ 0 = u₀ := by
  simp [hybrid]

theorem hybrid_length {u₀ u₁ : List Bool} (h : u₀.length = u₁.length) :
    hybrid u₀ u₁ u₀.length = u₁ := by
  simp [hybrid, h]

theorem diff_hybrid_succ {u₀ u₁ : List Bool} (h : u₀.length = u₁.length) {i : ℕ}
    (hi : i < u₀.length) : diff (hybrid u₀ u₁ i) (hybrid u₀ u₁ (i + 1)) ⊆ {i} := by
  intro j hj
  rw [mem_diff, getElem?_hybrid h (by omega), getElem?_hybrid h (by omega)] at hj
  rw [Finset.mem_singleton]
  by_contra hne
  apply hj.2
  by_cases hji : j < i
  · rw [if_pos hji, if_pos (by omega)]
  · rw [if_neg hji, if_neg (by omega)]

/-! ## Budgets and the forcing -/

/-- A disagreement budget (report 10, Section 4.1; synthesis, Definition 8.1).  The computability
requirements of the paper definition are not needed for the existence theorems proved here. -/
structure Budget where
  /-- The affordable finite sets of positions. -/
  mem : Finset ℕ → Prop
  empty_mem : mem ∅
  mono : ∀ {E F : Finset ℕ}, F ⊆ E → mem E → mem F
  /-- The one-bit reserve. -/
  reserve : ∀ E, mem E → ∀ L : ℕ, ∃ M, L ≤ M ∧ ∀ k, M ≤ k → mem (insert k E)

/-- A set obeys the budget if all its initial segments are affordable. -/
def Budget.Obeys (𝔅 : Budget) (V : Set ℕ) : Prop :=
  ∀ n, 𝔅.mem ((Finset.range n).filter (· ∈ V))

/-- The counting budget `|E ∩ [0,k)| ≤ b k` for a nondecreasing unbounded `b`. -/
def countingBudget (b : ℕ → ℕ) (hmono : Monotone b) (hunb : ∀ c, ∃ n, c ≤ b n) : Budget where
  mem E := ∀ k, (E.filter (· < k)).card ≤ b k
  empty_mem := by simp
  mono := by
    intro E F hFE hE k
    exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hFE)) (hE k)
  reserve := by
    intro E hE L
    obtain ⟨n, hn⟩ := hunb (E.card + 1)
    refine ⟨max L n, le_max_left _ _, fun k hk j => ?_⟩
    by_cases hjk : j ≤ k
    · have : (insert k E).filter (· < j) = E.filter (· < j) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hlt⟩
          · omega
          · exact ⟨hx, hlt⟩
        · rintro ⟨hx, hlt⟩
          exact ⟨Or.inr hx, hlt⟩
      rw [this]
      exact hE j
    · have h1 : ((insert k E).filter (· < j)).card ≤ E.card + 1 :=
        le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Finset.card_insert_le _ _)
      have h2 : b n ≤ b j := hmono (by omega)
      omega

/-- Budgets are closed under intersection: one may impose two constraints at once. -/
def Budget.inter (𝔅 𝔏 : Budget) : Budget where
  mem E := 𝔅.mem E ∧ 𝔏.mem E
  empty_mem := ⟨𝔅.empty_mem, 𝔏.empty_mem⟩
  mono h hE := ⟨𝔅.mono h hE.1, 𝔏.mono h hE.2⟩
  reserve E hE L := by
    obtain ⟨M₁, h₁, hM₁⟩ := 𝔅.reserve E hE.1 L
    obtain ⟨M₂, h₂, hM₂⟩ := 𝔏.reserve E hE.2 L
    exact ⟨max M₁ M₂, le_trans h₁ (le_max_left _ _), fun k hk =>
      ⟨hM₁ k (le_trans (le_max_left _ _) hk), hM₂ k (le_trans (le_max_right _ _) hk)⟩⟩

theorem Budget.Obeys.left {𝔅 𝔏 : Budget} {V : Set ℕ} (h : (𝔅.inter 𝔏).Obeys V) :
    𝔅.Obeys V := fun n => (h n).1

theorem Budget.Obeys.right {𝔅 𝔏 : Budget} {V : Set ℕ} (h : (𝔅.inter 𝔏).Obeys V) :
    𝔏.Obeys V := fun n => (h n).2

/-- The *density budget* `|E ∩ [0,n)| ≤ r·n`.  Obeying it means exactly lying within distance
`r` of the empty set in the prefix-density metric `d(U,V) = supₙ ρₙ(U △ V)` of the synthesis,
so a condition of this forcing is a ball of that metric: the forcing of report 10 and the
Baire-category method of the synthesis act on the same space. -/
def densityBudget (r : ℚ) (hr : 0 < r) : Budget where
  mem E := ∀ n : ℕ, ((E.filter (· < n)).card : ℚ) ≤ r * n
  empty_mem := by
    intro n
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  mono := by
    intro E F hFE hE n
    refine le_trans ?_ (hE n)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hFE)
  reserve := by
    intro E hE L
    refine ⟨max L ⌈((E.card : ℚ) + 1) / r⌉₊, le_max_left _ _, fun k hk n => ?_⟩
    by_cases hnk : n ≤ k
    · have hfil : (insert k E).filter (· < n) = E.filter (· < n) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hlt⟩
          · omega
          · exact ⟨hx, hlt⟩
        · rintro ⟨hx, hlt⟩
          exact ⟨Or.inr hx, hlt⟩
      rw [hfil]
      exact hE n
    · have hcard : ((insert k E).filter (· < n)).card ≤ E.card + 1 :=
        le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Finset.card_insert_le _ _)
      have hMn : ⌈((E.card : ℚ) + 1) / r⌉₊ ≤ n := by
        have : ⌈((E.card : ℚ) + 1) / r⌉₊ ≤ k := le_trans (le_max_right _ _) hk
        omega
      have h1 : ((E.card : ℚ) + 1) / r ≤ (n : ℚ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hMn)
      have h2 : (E.card : ℚ) + 1 ≤ r * n := by
        rw [div_le_iff₀ hr] at h1
        linarith
      calc (((insert k E).filter (· < n)).card : ℚ) ≤ ((E.card : ℚ) + 1) := by exact_mod_cast hcard
        _ ≤ r * n := h2

/-- A set obeying the density budget has all prefix ratios at most `r`. -/
theorem densityBudget_le {r : ℚ} (hr : 0 < r) {V : Set ℕ} (h : (densityBudget r hr).Obeys V)
    (n : ℕ) : ((count V n : ℚ)) ≤ r * n := by
  have hn := h n n
  refine le_trans (le_of_eq ?_) hn
  unfold count
  congr 2
  apply (Finset.filter_true_of_mem _).symm
  intro x hx
  exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1

/-- Conditions: pairs of equal-length strings whose disagreement set is affordable. -/
structure Cond (𝔅 : Budget) where
  fst : List Bool
  snd : List Bool
  len : fst.length = snd.length
  ok : 𝔅.mem (diff fst snd)

variable {𝔅 : Budget}

/-- `q` extends `p`. -/
def Cond.Ext (q p : Cond 𝔅) : Prop := p.fst <+: q.fst ∧ p.snd <+: q.snd

theorem Cond.Ext.refl (p : Cond 𝔅) : p.Ext p := ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem Cond.Ext.trans {r q p : Cond 𝔅} (h1 : r.Ext q) (h2 : q.Ext p) : r.Ext p :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- The empty condition. -/
def Cond.nil (𝔅 : Budget) : Cond 𝔅 := ⟨[], [], rfl, by simpa [diff] using 𝔅.empty_mem⟩

/-- Copy extension: append the same word to both coordinates. -/
def Cond.copy (p : Cond 𝔅) (u : List Bool) : Cond 𝔅 :=
  ⟨p.fst ++ u, p.snd ++ u, by simp [p.len], by rw [diff_append_same p.len]; exact p.ok⟩

theorem Cond.copy_ext (p : Cond 𝔅) (u : List Bool) : (p.copy u).Ext p :=
  ⟨List.prefix_append _ _, List.prefix_append _ _⟩

/-- A condition is padded if one more disagreement at any new position is affordable. -/
def Cond.Padded (p : Cond 𝔅) : Prop :=
  ∀ k, p.fst.length ≤ k → 𝔅.mem (insert k (diff p.fst p.snd))

theorem Cond.exists_padded (p : Cond 𝔅) : ∃ q : Cond 𝔅, q.Ext p ∧ q.Padded := by
  obtain ⟨M, hLM, hM⟩ := 𝔅.reserve _ p.ok p.fst.length
  refine ⟨p.copy (List.replicate (M - p.fst.length) false), p.copy_ext _, fun k hk => ?_⟩
  have hlen : (p.copy (List.replicate (M - p.fst.length) false)).fst.length = M := by
    simp [Cond.copy]
    omega
  have hd : diff (p.copy (List.replicate (M - p.fst.length) false)).fst
      (p.copy (List.replicate (M - p.fst.length) false)).snd = diff p.fst p.snd :=
    diff_append_same p.len _
  rw [hd]
  exact hM k (by omega)

/-- Below a padded condition, two suffixes of the same length that differ in at most one
position give a condition. -/
def Cond.oneBit (p : Cond 𝔅) (hp : p.Padded) (x y : List Bool) (hxy : x.length = y.length)
    (i : ℕ) (hd : diff x y ⊆ {i}) : Cond 𝔅 :=
  ⟨p.fst ++ x, p.snd ++ y, by simp [p.len, hxy], by
    refine 𝔅.mono ?_ (hp (p.fst.length + i) (by omega))
    intro k hk
    rw [mem_diff_append p.len] at hk
    rw [Finset.mem_insert]
    rcases hk with hk | ⟨hle, hk⟩
    · exact Or.inr hk
    · have := Finset.mem_singleton.mp (hd hk)
      left
      omega⟩

theorem Cond.oneBit_ext (p : Cond 𝔅) (hp : p.Padded) (x y : List Bool)
    (hxy : x.length = y.length) (i : ℕ) (hd : diff x y ⊆ {i}) :
    (p.oneBit hp x y hxy i hd).Ext p :=
  ⟨List.prefix_append _ _, List.prefix_append _ _⟩

/-! ## Decision systems and the bridge lemma -/

/-- An abstract decision relation on strings. -/
structure DecSys (Name : Type) where
  dec : List Bool → Name → ℕ → Bool → Prop
  persist : ∀ {σ σ' ψ n b}, dec σ ψ n b → σ <+: σ' → dec σ' ψ n b
  consistent : ∀ {σ ψ n b c}, dec σ ψ n b → dec σ ψ n c → b = c
  dense : ∀ σ ψ n, ∃ σ' b, σ <+: σ' ∧ dec σ' ψ n b

variable {Name : Type} (D : DecSys Name)

/-- `q` is a cross-disagreement for the names `ψ⁰`, `ψ¹`. -/
def IsCross (ψ₀ ψ₁ : Name) (q : Cond 𝔅) : Prop :=
  ∃ n b c, b ≠ c ∧ D.dec q.fst ψ₀ n b ∧ D.dec q.snd ψ₁ n c

/-- One step of the bridge: the decided value is carried from one hybrid to the next. -/
theorem bridge_step {ψ₀ ψ₁ : Name} {p : Cond 𝔅} (hp : p.Padded)
    (hno : ∀ q : Cond 𝔅, q.Ext p → ¬ IsCross D ψ₀ ψ₁ q) {n : ℕ} {b : Bool}
    (x y : List Bool) (hxy : x.length = y.length) (i : ℕ) (hd : diff x y ⊆ {i})
    (hx : ∃ ρ, D.dec (p.fst ++ x ++ ρ) ψ₀ n b) :
    ∃ ρ, D.dec (p.fst ++ y ++ ρ) ψ₀ n b := by
  obtain ⟨ρ, hρ⟩ := hx
  -- decide `ψ₁` above `p.snd ++ y ++ ρ`
  obtain ⟨β, c, hβ, hc⟩ := D.dense (p.snd ++ y ++ ρ) ψ₁ n
  obtain ⟨ν, rfl⟩ := hβ
  have hdx : diff (x ++ ρ ++ ν) (y ++ ρ ++ ν) ⊆ {i} := by
    intro k hk
    rw [List.append_assoc, List.append_assoc, mem_diff_append hxy] at hk
    rcases hk with hk | ⟨-, hk⟩
    · exact hd hk
    · simp at hk
  have hcb : c = b := by
    by_contra hne
    apply hno (p.oneBit hp (x ++ ρ ++ ν) (y ++ ρ ++ ν) (by simp [hxy]) i hdx)
      (p.oneBit_ext hp _ _ _ _ _)
    refine ⟨n, b, c, fun h => hne h.symm, ?_, ?_⟩
    · have : p.fst ++ (x ++ ρ ++ ν) = p.fst ++ x ++ ρ ++ ν := by simp
      show D.dec (p.fst ++ (x ++ ρ ++ ν)) ψ₀ n b
      rw [this]
      exact D.persist hρ (List.prefix_append _ _)
    · have : p.snd ++ (y ++ ρ ++ ν) = p.snd ++ y ++ ρ ++ ν := by simp
      show D.dec (p.snd ++ (y ++ ρ ++ ν)) ψ₁ n c
      rw [this]
      exact hc
  subst hcb
  -- decide `ψ₀` above `p.fst ++ y ++ ρ ++ ν`
  obtain ⟨α, d, hα, hdd⟩ := D.dense (p.fst ++ y ++ ρ ++ ν) ψ₀ n
  obtain ⟨ν', rfl⟩ := hα
  have hdc : d = c := by
    by_contra hne
    apply hno (p.copy (y ++ ρ ++ ν ++ ν')) (p.copy_ext _)
    refine ⟨n, d, c, hne, ?_, ?_⟩
    · have : p.fst ++ (y ++ ρ ++ ν ++ ν') = p.fst ++ y ++ ρ ++ ν ++ ν' := by simp
      show D.dec (p.fst ++ (y ++ ρ ++ ν ++ ν')) ψ₀ n d
      rw [this]
      exact hdd
    · have : p.snd ++ (y ++ ρ ++ ν ++ ν') = p.snd ++ y ++ ρ ++ ν ++ ν' := by simp
      show D.dec (p.snd ++ (y ++ ρ ++ ν ++ ν')) ψ₁ n c
      rw [this]
      exact D.persist hc (List.prefix_append _ _)
  subst hdc
  refine ⟨ρ ++ ν ++ ν', ?_⟩
  have : p.fst ++ y ++ (ρ ++ ν ++ ν') = p.fst ++ y ++ ρ ++ ν ++ ν' := by simp
  rw [this]
  exact hdd

/-- **The bridge lemma** (report 10, Lemma 4.2).  Below a padded condition no extension of which
is a cross-disagreement, all extensions of the first coordinate that decide an instance of `ψ₀`
decide it the same way. -/
theorem bridge {ψ₀ ψ₁ : Name} {p : Cond 𝔅} (hp : p.Padded)
    (hno : ∀ q : Cond 𝔅, q.Ext p → ¬ IsCross D ψ₀ ψ₁ q) {n : ℕ} {b c : Bool}
    {α α' : List Bool} (hα : p.fst <+: α) (hα' : p.fst <+: α')
    (hb : D.dec α ψ₀ n b) (hc : D.dec α' ψ₀ n c) : b = c := by
  obtain ⟨u, rfl⟩ := hα
  obtain ⟨v, rfl⟩ := hα'
  -- equalize the lengths of the two suffixes
  let u₀ := u ++ List.replicate v.length false
  let u₁ := v ++ List.replicate u.length false
  have hlen : u₀.length = u₁.length := by
    simp only [u₀, u₁, List.length_append, List.length_replicate]
    omega
  have hb' : D.dec (p.fst ++ u₀) ψ₀ n b :=
    D.persist hb ⟨List.replicate v.length false, by simp [u₀]⟩
  have key : ∀ i, i ≤ u₀.length → ∃ ρ, D.dec (p.fst ++ hybrid u₀ u₁ i ++ ρ) ψ₀ n b := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨[], by simpa [hybrid_zero] using hb'⟩
    | succ i ih =>
      intro hi
      refine bridge_step D hp hno _ _ ?_ i (diff_hybrid_succ hlen (by omega)) (ih (by omega))
      rw [length_hybrid hlen (by omega), length_hybrid hlen hi]
  obtain ⟨ρ, hρ⟩ := key u₀.length le_rfl
  rw [hybrid_length hlen] at hρ
  have hc' : D.dec (p.fst ++ u₁ ++ ρ) ψ₀ n c :=
    D.persist hc ⟨List.replicate u.length false ++ ρ, by simp [u₁]⟩
  exact D.consistent hρ hc'

/-! ## Generic pairs -/

/-- A descending sequence meeting countably many dense sets (Rasiowa--Sikorski). -/
theorem exists_chain {P : Type} (le : P → P → Prop) (p₀ : P) (Dn : ℕ → Set P)
    (hD : ∀ n p, ∃ q, le q p ∧ q ∈ Dn n) :
    ∃ c : ℕ → P, c 0 = p₀ ∧ (∀ s, le (c (s + 1)) (c s)) ∧ ∀ s, c (s + 1) ∈ Dn s := by
  choose f hf using hD
  exact ⟨fun s => Nat.rec p₀ (fun n q => f n q) s, rfl, fun s => (hf s _).1, fun s => (hf s _).2⟩

/-- The set determined by an increasing sequence of strings. -/
def limitSet (c : ℕ → List Bool) : Set ℕ := {i | ∃ s, (c s)[i]? = some true}

theorem isPrefixOf_limitSet {c : ℕ → List Bool} (hmono : ∀ s t, s ≤ t → c s <+: c t) (s : ℕ) :
    IsPrefixOf (c s) (limitSet c) := by
  intro i hi
  constructor
  · intro h
    exact ⟨s, by rw [List.getElem?_eq_getElem hi, h]⟩
  · rintro ⟨t, ht⟩
    have hit : i < (c t).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (not_lt.mp hcon)] at ht
      exact absurd ht (by simp)
    rw [List.getElem?_eq_getElem hit] at ht
    have htrue : (c t)[i] = true := Option.some.inj ht
    rcases le_total s t with hst | hts
    · exact ((hmono s t hst).getElem hi).trans htrue
    · exact ((hmono t s hts).getElem hit).symm.trans htrue

/-- Two initial segments of the same set are comparable. -/
theorem IsPrefixOf.prefix_of_length_le {σ τ : List Bool} {X : Set ℕ} (hσ : IsPrefixOf σ X)
    (hτ : IsPrefixOf τ X) (h : σ.length ≤ τ.length) : σ <+: τ := by
  have : σ = τ.take σ.length := by
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2
      rw [List.getElem_take]
      have hi : i < τ.length := by omega
      have e1 := hσ i h1
      have e2 := hτ i hi
      cases hb : σ[i] <;> cases hc : τ[i] <;> simp_all
  rw [this]
  exact List.take_prefix _ _

/-- "The set `A` decides the `n`-th instance of `ψ` as `b`." -/
def Truth (A : Set ℕ) (ψ : Name) (n : ℕ) (b : Bool) : Prop :=
  ∃ σ, IsPrefixOf σ A ∧ D.dec σ ψ n b

/-- **Generic pairs** (report 10, Section 4.3, abstract form).  Given a budget, a decision system
with countably many names, and countably many dense sets of strings, there are sets `A`, `B`
such that: both meet all the given dense sets; `A △ B` obeys the budget; both decide every
instance; and whenever `A` and `B` agree on the names `ψ₀`, `ψ₁`, some initial segment `σ` of
`A` has the property that all extensions of `σ` decide the instances of `ψ₀` the same way, and
that way is the truth about `A`. -/
theorem exists_generic_pair [Countable Name] (𝔅 : Budget) (𝒟 : ℕ → Set (List Bool))
    (h𝒟 : ∀ k σ, ∃ σ', σ <+: σ' ∧ σ' ∈ 𝒟 k) :
    ∃ A B : Set ℕ,
      (∀ k, ∃ σ, IsPrefixOf σ A ∧ σ ∈ 𝒟 k) ∧ (∀ k, ∃ σ, IsPrefixOf σ B ∧ σ ∈ 𝒟 k) ∧
      𝔅.Obeys (symmDiff A B) ∧
      (∀ ψ n, ∃ b, Truth D A ψ n b) ∧ (∀ ψ n, ∃ b, Truth D B ψ n b) ∧
      ∀ ψ₀ ψ₁ : Name, (∀ n b c, Truth D A ψ₀ n b → Truth D B ψ₁ n c → b = c) →
        ∃ σ, IsPrefixOf σ A ∧
          (∀ n b c α α', σ <+: α → σ <+: α' → D.dec α ψ₀ n b → D.dec α' ψ₀ n c → b = c) ∧
          ∀ n b, Truth D A ψ₀ n b ↔ ∃ α, σ <+: α ∧ D.dec α ψ₀ n b := by
  -- the countably many requirements
  let I := ℕ ⊕ ℕ ⊕ (Name × ℕ) ⊕ (Name × ℕ) ⊕ (Name × Name) ⊕ ℕ
  let Dset : I → Set (Cond 𝔅) := fun r =>
    match r with
    | .inl k => {q | q.fst ∈ 𝒟 k}
    | .inr (.inl k) => {q | q.snd ∈ 𝒟 k}
    | .inr (.inr (.inl (ψ, n))) => {q | ∃ b, D.dec q.fst ψ n b}
    | .inr (.inr (.inr (.inl (ψ, n)))) => {q | ∃ b, D.dec q.snd ψ n b}
    | .inr (.inr (.inr (.inr (.inl (ψ₀, ψ₁))))) =>
        {q | IsCross D ψ₀ ψ₁ q ∨ (q.Padded ∧ ∀ q' : Cond 𝔅, q'.Ext q → ¬ IsCross D ψ₀ ψ₁ q')}
    | .inr (.inr (.inr (.inr (.inr k)))) => {q | k ≤ q.fst.length}
  have hdense : ∀ (r : I) (p : Cond 𝔅), ∃ q : Cond 𝔅, q.Ext p ∧ q ∈ Dset r := by
    intro r p
    match r with
    | .inl k =>
      obtain ⟨σ', ⟨u, rfl⟩, hσ'⟩ := h𝒟 k p.fst
      exact ⟨p.copy u, p.copy_ext u, hσ'⟩
    | .inr (.inl k) =>
      obtain ⟨σ', ⟨u, rfl⟩, hσ'⟩ := h𝒟 k p.snd
      exact ⟨p.copy u, p.copy_ext u, hσ'⟩
    | .inr (.inr (.inl (ψ, n))) =>
      obtain ⟨σ', b, ⟨u, rfl⟩, hb⟩ := D.dense p.fst ψ n
      exact ⟨p.copy u, p.copy_ext u, b, hb⟩
    | .inr (.inr (.inr (.inl (ψ, n)))) =>
      obtain ⟨σ', b, ⟨u, rfl⟩, hb⟩ := D.dense p.snd ψ n
      exact ⟨p.copy u, p.copy_ext u, b, hb⟩
    | .inr (.inr (.inr (.inr (.inl (ψ₀, ψ₁))))) =>
      by_cases hex : ∃ q : Cond 𝔅, q.Ext p ∧ IsCross D ψ₀ ψ₁ q
      · obtain ⟨q, hq, hcross⟩ := hex
        exact ⟨q, hq, Or.inl hcross⟩
      · obtain ⟨q, hq, hpad⟩ := p.exists_padded
        exact ⟨q, hq, Or.inr ⟨hpad, fun q' hq' hcross => hex ⟨q', hq'.trans hq, hcross⟩⟩⟩
    | .inr (.inr (.inr (.inr (.inr k)))) =>
      refine ⟨p.copy (List.replicate k false), p.copy_ext _, ?_⟩
      show k ≤ (p.fst ++ List.replicate k false).length
      simp
  obtain ⟨f, hf⟩ := exists_surjective_nat I
  obtain ⟨c, -, hstep, hmeet⟩ :=
    exists_chain (fun q p : Cond 𝔅 => q.Ext p) (Cond.nil 𝔅) (fun s => Dset (f s))
      (fun s p => hdense (f s) p)
  have hmono : ∀ s t, s ≤ t → (c t).Ext (c s) := by
    intro s t hst
    induction t, hst using Nat.le_induction with
    | base => exact Cond.Ext.refl _
    | succ t _ ih => exact (hstep t).trans ih
  have hreq : ∀ r : I, ∃ s, c s ∈ Dset r := by
    intro r
    obtain ⟨s, hs⟩ := hf r
    exact ⟨s + 1, hs ▸ hmeet s⟩
  let A := limitSet (fun s => (c s).fst)
  let B := limitSet (fun s => (c s).snd)
  have hA : ∀ s, IsPrefixOf (c s).fst A :=
    isPrefixOf_limitSet (c := fun s => (c s).fst) (fun s t h => (hmono s t h).1)
  have hB : ∀ s, IsPrefixOf (c s).snd B :=
    isPrefixOf_limitSet (c := fun s => (c s).snd) (fun s t h => (hmono s t h).2)
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨s, hs⟩ := hreq (.inl k)
    exact ⟨_, hA s, hs⟩
  · intro k
    obtain ⟨s, hs⟩ := hreq (.inr (.inl k))
    exact ⟨_, hB s, hs⟩
  · intro n
    obtain ⟨s, hs⟩ := hreq (.inr (.inr (.inr (.inr (.inr n)))))
    have hs' : n ≤ (c s).fst.length := hs
    refine 𝔅.mono ?_ (c s).ok
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    have hi1 : i < (c s).fst.length := by omega
    have hi2 : i < (c s).snd.length := (c s).len ▸ hi1
    rw [mem_diff]
    refine ⟨hi1, fun heq => ?_⟩
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at heq
    have heq' : (c s).fst[i] = (c s).snd[i] := Option.some.inj heq
    have eA := hA s i hi1
    have eB := hB s i hi2
    have hiff : i ∈ A ↔ i ∈ B := by rw [← eA, ← eB, heq']
    rcases hi.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.mp h1)
    · exact h2 (hiff.mpr h1)
  · intro ψ n
    obtain ⟨s, b, hb⟩ := hreq (.inr (.inr (.inl (ψ, n))))
    exact ⟨b, _, hA s, hb⟩
  · intro ψ n
    obtain ⟨s, b, hb⟩ := hreq (.inr (.inr (.inr (.inl (ψ, n)))))
    exact ⟨b, _, hB s, hb⟩
  · intro ψ₀ ψ₁ hagree
    obtain ⟨s, hs⟩ := hreq (.inr (.inr (.inr (.inr (.inl (ψ₀, ψ₁))))))
    rcases hs with ⟨n, b, c', hne, hb, hc⟩ | ⟨hpad, hno⟩
    · exact absurd (hagree n b c' ⟨_, hA s, hb⟩ ⟨_, hB s, hc⟩) hne
    · have huniq : ∀ n b c' α α', (c s).fst <+: α → (c s).fst <+: α' →
          D.dec α ψ₀ n b → D.dec α' ψ₀ n c' → b = c' :=
        fun n b c' α α' h1 h2 h3 h4 => bridge D hpad hno h1 h2 h3 h4
      refine ⟨(c s).fst, hA s, huniq, fun n b => ⟨?_, ?_⟩⟩
      · rintro ⟨σ, hσ, hdec⟩
        rcases le_total (c s).fst.length σ.length with hle | hle
        · exact ⟨σ, (hA s).prefix_of_length_le hσ hle, hdec⟩
        · exact ⟨(c s).fst, List.prefix_refl _,
            D.persist hdec (hσ.prefix_of_length_le (hA s) hle)⟩
      · rintro ⟨α, hα, hdec⟩
        obtain ⟨t, b', hb'⟩ := hreq (.inr (.inr (.inl (ψ₀, n))))
        have hb'' : D.dec (c t).fst ψ₀ n b' := hb'
        rcases le_total s t with hst | hts
        · have hpre : (c s).fst <+: (c t).fst := (hmono s t hst).1
          have : b = b' := huniq n b b' α _ hα hpre hdec hb''
          exact ⟨_, hA t, this ▸ hb''⟩
        · have hpre : (c t).fst <+: (c s).fst := (hmono t s hts).1
          have hd : D.dec (c s).fst ψ₀ n b' := D.persist hb'' hpre
          have : b = b' := huniq n b b' α _ hα (List.prefix_refl _) hdec hd
          exact ⟨_, hA s, this ▸ hd⟩

end CoarseDegrees

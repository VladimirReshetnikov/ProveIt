/-
  A STRONGLY COMPACT CARDINAL ABOVE THE COVER BOUND: GROUNDS (synthesis §7).

  * set forcing over an inner model, inside `ZFSet`: posets, generic filters, name
    evaluation `val`, grounds, the Ground Axiom, and the `lam`-chain condition
    computed in the ground;
  * two admitted published inputs: Goldberg's ground theorem, and the textbook
    preservation of regular cardinals by chain-condition forcing;
  * `proper_ground` (Theorem 7.2), `groundAxiom_obstruction` (Corollary 7.3),
    `general_ground_obstruction` (Corollary 7.4), `two_strongly_compacts`
    (Corollary 7.5), `strongLimit_in_ground` (R8), and the failure of small covering
    (Corollary 5.5).
-/
import Cardinals.Below

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal

/-! ### Forcing over an inner model -/

/-- The forcing order coded by the set of pairs `le`: `p ≤ q`. -/
def leP (le p q : ZFSet.{u}) : Prop := pair p q ∈ le

/-- `(P, le)` is a preorder. -/
structure IsForcingPoset (P le : ZFSet.{u}) : Prop where
  refl : ∀ p ∈ P, leP le p p
  trans : ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, leP le p q → leP le q r → leP le p r

/-- `p` and `q` have a common extension. -/
def Compat (P le p q : ZFSet.{u}) : Prop := ∃ r ∈ P, leP le r p ∧ leP le r q

/-- `D` is dense in `P`. -/
def IsDenseIn (P le D : ZFSet.{u}) : Prop := D ⊆ P ∧ ∀ p ∈ P, ∃ d ∈ D, leP le d p

/-- `A` is an antichain of `P`. -/
def IsAntichainIn (P le A : ZFSet.{u}) : Prop :=
  A ⊆ P ∧ ∀ p ∈ A, ∀ q ∈ A, p ≠ q → ¬ Compat P le p q

/-- `G` is a filter on `P` that meets every dense subset of `P` lying in `W`. -/
structure IsGenericOver (W : ZFSet.{u} → Prop) (P le G : ZFSet.{u}) : Prop where
  sub : G ⊆ P
  nonempty : G.Nonempty
  upward : ∀ p ∈ G, ∀ q ∈ P, leP le p q → q ∈ G
  directed : ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, leP le r p ∧ leP le r q
  generic : ∀ D, W D → IsDenseIn P le D → ∃ d ∈ D, d ∈ G

/-- The candidates `σ` with `⟨σ, p⟩ ∈ τ` for some `p ∈ G`. -/
def nameDom (G τ : ZFSet.{u}) : ZFSet.{u} :=
  (⋃₀ (⋃₀ τ : ZFSet.{u}) : ZFSet.{u}).sep (fun σ => ∃ p ∈ G, pair σ p ∈ τ)

/-- Evaluation of a `P`-name by the filter `G`:
`val G τ = { val G σ : ∃ p ∈ G, ⟨σ, p⟩ ∈ τ }`, by recursion on rank. -/
noncomputable def val (G : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  (InvImage.wf (fun x : ZFSet.{u} => rank x) Ordinal.lt_wf).fix
    (fun τ rec => ZFSet.range (fun σ : {σ // σ ∈ nameDom G τ} =>
      if h : rank σ.1 < rank τ then rec σ.1 h else ∅))

/-- `V = W[G]` for a `W`-generic filter `G` on a poset `(P, le) ∈ W`. -/
structure IsForcingPresentation (W : ZFSet.{u} → Prop) (P le G : ZFSet.{u}) : Prop where
  memP : W P
  memLe : W le
  poset : IsForcingPoset P le
  gen : IsGenericOver W P le G
  all : ∀ x : ZFSet.{u}, ∃ τ, W τ ∧ val G τ = x

/-- `W` is a (set-forcing) ground of `V`. -/
def IsGround (W : ZFSet.{u} → Prop) : Prop :=
  IsInnerModelZFC W ∧ ∃ P le G, IsForcingPresentation W P le G

/-- The Ground Axiom: `V` has no proper ground. -/
def GroundAxiom : Prop := ∀ W : ZFSet.{u} → Prop, IsGround W → ∀ x, W x

/-- `f` is an injection from `x` into `y` (as a set of ordered pairs). -/
def IsInjFunc (x y f : ZFSet.{u}) : Prop :=
  IsFunc x y f ∧ ∀ a b z, pair a z ∈ f → pair b z ∈ f → a = b

/-- `P` has the `lam`-chain condition *in `W`*: no antichain of `P` lying in `W`
receives, in `W`, an injection from `lam`. -/
def CCIn (W : ZFSet.{u} → Prop) (P le : ZFSet.{u}) (lam : Ordinal.{u}) : Prop :=
  ∀ A, W A → IsAntichainIn P le A → ¬ ∃ f, W f ∧ IsInjFunc (ordZ lam) A f

/-! ### Admitted published inputs -/

namespace Published

/-- Goldberg's ground theorem: if `κ` is strongly compact, `HCD(κ)` is a ground of `V`.
([G24, Theorem 4.10].) -/
theorem HCD_isGround (κ : Cardinal.{u}) (hκ : SC κ) : IsGround (HCD κ) := by
  admit

/-- Forcing with the `lam`-chain condition preserves the regularity of `lam`:
if `lam = c.ord` is regular uncountable in the ground `W` and `V = W[G]` for a forcing
that is `lam`-cc in `W`, then `V` has no short cofinal subset of `lam`.
([Jech, Theorem 15.3 and Lemma 15.4]; synthesis Lemma 7.1.) -/
theorem cc_preserves_regular (W : ZFSet.{u} → Prop) (P le G : ZFSet.{u})
    (hpres : IsForcingPresentation W P le G) (hW : IsInnerModelZFC W)
    (c : Cardinal.{u}) (hc : ℵ₀ < c) (hreg : RegularIn W c.ord) (hcc : CCIn W P le c.ord) :
    ∀ a : ZFSet.{u}, ¬ ShortCofinal a c.ord := by
  admit

end Published

/-! ### Cardinalities of set-coded injections -/

theorem card_le_of_isInjFunc {x y f : ZFSet.{u}} (h : IsInjFunc x y f) :
    ZFSet.card x ≤ ZFSet.card y := by
  obtain ⟨⟨hsub, hfun⟩, hinj⟩ := h
  have hval : ∀ a : {a // a ∈ x}, ∃ w, pair a.1 w ∈ f := fun a => (hfun a.1 a.2).exists
  choose g hg using hval
  have hgy : ∀ a, g a ∈ y := fun a => (pair_mem_prod.mp (hsub (hg a))).2
  have hinj' : Function.Injective (fun a : {a // a ∈ x} => (⟨g a, hgy a⟩ : {b // b ∈ y})) := by
    intro a b hab
    have : g a = g b := congrArg Subtype.val hab
    exact Subtype.ext (hinj a.1 b.1 (g a) (hg a) (this ▸ hg b))
  have := Cardinal.mk_le_of_injective hinj'
  have hx : #{a // a ∈ x} = Cardinal.lift.{u + 1, u} (ZFSet.card x) := ZFSet.cardinalMk_coe_sort
  have hy : #{b // b ∈ y} = Cardinal.lift.{u + 1, u} (ZFSet.card y) := ZFSet.cardinalMk_coe_sort
  rw [hx, hy] at this
  exact Cardinal.lift_le.mp this

/-! ### The proper-ground theorem -/

/-- A class in which `lam` is regular omits every countable cofinal subset of `lam`,
provided `lam` is uncountable. -/
theorem countable_cofinal_notMem (W : ZFSet.{u} → Prop) (c : Cardinal.{u}) (hc : ℵ₀ < c)
    (hreg : RegularIn W c.ord) (a : ZFSet.{u}) (hcof : CofinalIn a c.ord)
    (hcard : ZFSet.card a ≤ ℵ₀) : ¬ W a :=
  fun hW => hreg a hW ⟨hcof, by rw [card_ord]; exact lt_of_le_of_lt hcard hc⟩

/-- A cover-exacting cardinal is uncountable. -/
theorem aleph0_lt_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) : ℵ₀ < c :=
  Cardinals.Published.aleph0_lt_of_witness c hc (fun _ hα => h.nonempty_witness hα)

/-- **Proper canonical ground (synthesis Theorem 7.2).**  If `c ≤ γ < κ`, `c.ord` is
`γ`-cover exacting and `κ` is strongly compact, then `HCD(κ)` is a *proper* ground in
which `c.ord` is regular, while `c.ord` has cofinality `ω` in `V`. -/
theorem proper_ground (c γ κ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (hκ : SC κ) (hγκ : γ < κ) :
    IsGround (HCD κ) ∧ RegularIn (HCD κ) c.ord ∧ ∃ a, ¬ HCD κ a := by
  have hreg := regular_in_HCD c γ κ hc h hγκ
  obtain ⟨a, hcof, hcard⟩ := exists_countable_cofinal c γ hc h
  exact ⟨Published.HCD_isGround κ hκ, hreg,
    a, countable_cofinal_notMem _ c (aleph0_lt_of_CEx c γ hc h) hreg a hcof hcard⟩

/-- **Ground Axiom obstruction (synthesis Corollary 7.3).** -/
theorem groundAxiom_obstruction (c γ κ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (hκ : SC κ) (hγκ : γ < κ) : ¬ GroundAxiom.{u} := by
  intro hGA
  obtain ⟨hground, -, a, ha⟩ := proper_ground c γ κ hc h hκ hγκ
  exact ha (hGA _ hground a)

/-- Under the Ground Axiom, every strongly compact cardinal is at most every cover
bound of every cover-exacting cardinal. -/
theorem SC_le_cover_bound_of_GA (hGA : GroundAxiom.{u}) (c γ κ : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (h : CEx γ c.ord) (hκ : SC κ) : κ ≤ γ := by
  by_contra hlt
  exact groundAxiom_obstruction c γ κ hc h hκ (not_le.mp hlt) hGA

/-- The Ground Axiom together with a proper class of strongly compact cardinals
excludes every cover-exacting cardinal, for every set-sized cover bound. -/
theorem no_CEx_of_GA_of_class_SC (hGA : GroundAxiom.{u})
    (hSC : ∀ μ : Cardinal.{u}, ∃ κ, μ < κ ∧ SC κ) (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) :
    ¬ CEx γ c.ord := by
  intro h
  obtain ⟨κ, hγκ, hκ⟩ := hSC γ
  exact groundAxiom_obstruction c γ κ hc h hκ hγκ hGA

/-- **General ground obstruction (synthesis Corollary 7.4, Lemma 7.1).**  If
`W ⊆ HCD(η)` with `η > γ` is a ground, no forcing presenting `V = W[G]` has the
`c.ord`-chain condition in `W`. -/
theorem general_ground_obstruction (c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (hη : γ < η) (W : ZFSet.{u} → Prop) (hWsub : ∀ x, W x → HCD η x)
    (hW : IsInnerModelZFC W) (P le G : ZFSet.{u}) (hpres : IsForcingPresentation W P le G) :
    ¬ CCIn W P le c.ord := by
  intro hcc
  have hreg : RegularIn W c.ord := fun a ha => regular_in_HCD c γ η hc h hη a (hWsub a ha)
  obtain ⟨a, hcof, hcard⟩ := exists_countable_cofinal c γ hc h
  have hlt := aleph0_lt_of_CEx c γ hc h
  exact Published.cc_preserves_regular W P le G hpres hW c hlt hreg hcc a
    ⟨hcof, by rw [card_ord]; exact lt_of_le_of_lt hcard hlt⟩

/-- In particular this applies to every presentation of `V` over `HCD(κ)`. -/
theorem HCD_ground_not_cc (c γ κ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (hκ : SC κ) (hγκ : γ < κ) (P le G : ZFSet.{u})
    (hpres : IsForcingPresentation (HCD κ) P le G) : ¬ CCIn (HCD κ) P le c.ord :=
  general_ground_obstruction c γ κ hc h hγκ (HCD κ) (fun _ hx => hx)
    (Published.HCD_isInnerModelZFC κ hκ) P le G hpres

/-- **`c.ord` is a strong limit in any class `W`** (report R8; used with regularity
to get strong inaccessibility in the ground): `W` contains no injection of `c.ord`
into the `W`-subsets of a smaller cardinal `μ`. -/
theorem strongLimit_in_class (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (W : ZFSet.{u} → Prop) (μ : Cardinal.{u}) (hμ : μ < c) :
    ¬ ∃ f, W f ∧ IsInjFunc (ordZ c.ord) ((powerset (ordZ μ.ord)).sep W) f := by
  rintro ⟨f, -, hf⟩
  have hsl := Published.strongLimit_of_witness c hc (fun _ hα => h.nonempty_witness hα) μ hμ
  have h1 := card_le_of_isInjFunc hf
  have h2 : ZFSet.card ((powerset (ordZ μ.ord)).sep W) ≤ 2 ^ μ := by
    refine (card_mono (fun x hx => (mem_sep.mp hx).1)).trans ?_
    rw [card_powerset, card_toZFSet, card_ord]
  rw [card_toZFSet, card_ord] at h1
  exact absurd (h1.trans h2) (not_le.mpr hsl)

/-- **Two strongly compact cardinals (synthesis Corollary 7.5).** -/
theorem two_strongly_compacts (δ c γ κ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ)
    (hδc : δ < c) (h : CEx γ c.ord) (hκ : SC κ) (hγκ : γ < κ) :
    IsGround (HCD κ) ∧ IsGround (HCD δ) ∧ (∀ x, HCD κ x → HCD δ x) ∧
      ∃ a, HCD δ a ∧ ZFSet.card a < δ ∧ SubOrd a c.ord ∧ ¬ HCD κ a := by
  have hcγ := Published.le_of_CEx c γ hc h
  have hδκ : δ ≤ κ := (hδc.trans_le hcγ).le.trans hγκ.le
  obtain ⟨a, ha, hcof, hcard, hnot⟩ := separation δ c γ hc hδ hδc h
  exact ⟨Published.HCD_isGround κ hκ, Published.HCD_isGround δ hδ,
    fun x hx => hx.mono hδκ, a, ha, hcard, hcof.1, fun haκ => hnot κ hγκ haκ.cd⟩

/-! ### Failure of small covering (synthesis Corollary 5.5) -/

/-- If `lam` is regular in an inner model `W` of ZF, a cofinal `ω`-sequence `s` meets
every member of `W` of size below `|lam|` in a finite set: all but finitely many
terms of `s` are omitted.  In particular no such member of `W` covers `s`. -/
theorem finite_trace_of_regularIn (W : ZFSet.{u} → Prop) (hW : IsInnerModelZF W)
    (lam : Ordinal.{u}) (hreg : RegularIn W lam)
    (s : ℕ → Ordinal.{u}) (hs : StrictMono s) (hlt : ∀ n, s n < lam)
    (hcof : ∀ ξ < lam, ∃ n, ξ ≤ s n)
    (b : ZFSet.{u}) (hb : W b) (hcard : ZFSet.card b < lam.card) :
    ∃ N, ∀ n ≥ N, ordZ (s n) ∉ b := by
  have hbl : W (b ∩ ordZ lam) := hW.inter_ord hb lam
  have hsub : SubOrd (b ∩ ordZ lam) lam :=
    subOrd_iff_subset.mpr (fun x hx => (mem_inter.mp hx).2)
  have hnc : ¬ CofinalIn (b ∩ ordZ lam) lam := fun hcof =>
    hreg _ hbl ⟨hcof, lt_of_le_of_lt (card_mono (fun x hx => (mem_inter.mp hx).1)) hcard⟩
  have : ∃ ξ < lam, ∀ η, ξ ≤ η → η < lam → ordZ η ∉ b ∩ ordZ lam := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨hsub, fun ξ hξ => by
      obtain ⟨η, h1, h2, h3⟩ := hcon ξ hξ
      exact ⟨η, h1, h2, h3⟩⟩
  obtain ⟨ξ, hξ, hξb⟩ := this
  obtain ⟨N, hN⟩ := hcof ξ hξ
  refine ⟨N, fun n hn hmem => ?_⟩
  have hle : ξ ≤ s n := hN.trans (hs.monotone hn)
  exact hξb (s n) hle (hlt n)
    (mem_inter.mpr ⟨hmem, Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlt n)⟩)

end Cardinals

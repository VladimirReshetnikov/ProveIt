/-
  THE HOD BOUNDARY AT AN EXACTING CARDINAL
  (synthesis Proposition 8.3 and the provable clauses of Theorem 10.7).

  Theorem 10.7 of the synthesis is an *equiconsistency* with `I0`; that comparison is a
  metamathematical statement imported from Aguilera–Bagaria–Goldberg–Lücke and is not
  formalized.  What is formalized is the part the reports actually prove: every clause
  of the boundary package follows, inside ZFC, from "`lam` is exacting and
  `V_lam ⊆ HOD`" (clauses (1)–(4)); clause (5) is the content of §9.

  Admitted inputs: `Published.no_short_cofinal_OD` (ABL Theorem 2.10) and the textbook
  fact that `HOD` is an inner model of ZF.
-/
import Cardinals.Width

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal

/-- Ordinal definable (no set parameters). -/
def OD (x : ZFSet.{u}) : Prop := ODfrom (fun _ => False) x

/-- Hereditarily ordinal definable. -/
def HOD (x : ZFSet.{u}) : Prop :=
  ∃ t : ZFSet.{u}, IsTransitive t ∧ x ∈ t ∧ ∀ y ∈ t, OD y

theorem HOD.od {x : ZFSet.{u}} (h : HOD x) : OD x := by
  obtain ⟨t, -, hxt, hall⟩ := h
  exact hall x hxt

namespace Published

/-- `HOD` is an inner model of ZF (indeed of ZFC).  ([Jech, Theorem 13.26].) -/
theorem HOD_isInnerModelZF : IsInnerModelZF (HOD.{u}) := by
  admit

end Published

/-- **An exacting cardinal is regular in `HOD`** ([ABL, Theorem 2.10], set form). -/
theorem regularIn_HOD (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hEx : Ex c.ord) :
    RegularIn HOD c.ord :=
  fun a ha hshort =>
    Published.no_short_cofinal_OD c hc hEx a (ODfrom.mono (fun _ h => h.elim) ha.od) hshort

/-- The witnesses of an exacting cardinal, in the form required by `Published`. -/
theorem Ex.witnesses {lam : Ordinal.{u}} (h : Ex lam) :
    ∀ α > lam, ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness lam α Y) :=
  fun α hα => ⟨∅, fun _ hx => absurd hx (notMem_empty _), h α hα⟩

/-- **Clause (3): a cofinal `ω`-sequence is missing from `HOD`.** -/
theorem seqSet_notMem_HOD (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hEx : Ex c.ord)
    (s : ℕ → Ordinal.{u}) (hlt : ∀ n, s n < c.ord) (hcof : ∀ ξ < c.ord, ∃ n, ξ ≤ s n) :
    ¬ HOD (seqSet s) :=
  countable_cofinal_notMem HOD c (Published.aleph0_lt_of_witness c hc hEx.witnesses)
    (regularIn_HOD c hc hEx) (seqSet s) (cofinalIn_seqSet hlt hcof) (card_seqSet_le s)

/-- **Clause (4a): finite traces** (the fresh cofinal set of Proposition 8.3).
A cofinal `ω`-sequence meets every `HOD`-set of size below `c` in a finite set. -/
theorem finite_trace_HOD (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hEx : Ex c.ord)
    (s : ℕ → Ordinal.{u}) (hs : StrictMono s) (hlt : ∀ n, s n < c.ord)
    (hcof : ∀ ξ < c.ord, ∃ n, ξ ≤ s n) (b : ZFSet.{u}) (hb : HOD b)
    (hcard : ZFSet.card b < c) : ∃ N, ∀ n ≥ N, ordZ (s n) ∉ b :=
  finite_trace_of_regularIn HOD Published.HOD_isInnerModelZF c.ord (regularIn_HOD c hc hEx)
    s hs hlt hcof b hb (by rwa [card_ord])

/-- **Clause (4b): no small cover in `HOD`.**  Every `HOD`-set covering a cofinal
`ω`-sequence has cardinality at least `c`. -/
theorem cover_in_HOD_large (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hEx : Ex c.ord)
    (s : ℕ → Ordinal.{u}) (hlt : ∀ n, s n < c.ord) (hcof : ∀ ξ < c.ord, ∃ n, ξ ≤ s n)
    (b : ZFSet.{u}) (hb : HOD b) (hcover : seqSet s ⊆ b) : c ≤ ZFSet.card b := by
  by_contra hlt'
  rw [not_le] at hlt'
  have hbl : HOD (b ∩ ordZ c.ord) := Published.HOD_isInnerModelZF.inter_ord hb c.ord
  have hcofb : CofinalIn (b ∩ ordZ c.ord) c.ord := by
    refine ⟨subOrd_iff_subset.mpr (fun x hx => (mem_inter.mp hx).2), fun ξ hξ => ?_⟩
    obtain ⟨n, hn⟩ := hcof ξ hξ
    exact ⟨s n, hn, hlt n, mem_inter.mpr
      ⟨hcover (mem_seqSet.mpr ⟨n, rfl⟩), Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlt n)⟩⟩
  refine regularIn_HOD c hc hEx _ hbl ⟨hcofb, ?_⟩
  rw [card_ord]
  exact lt_of_le_of_lt (card_mono (fun x hx => (mem_inter.mp hx).1)) hlt'

/-- **Clause (2): below `lam`, `HOD` has all subsets**, as soon as `V_lam ⊆ HOD`. -/
theorem subset_mem_HOD_of_rank (lam α : Ordinal.{u}) (hα : α < lam)
    (hV : ∀ x ∈ V_ lam, HOD x) (x : ZFSet.{u}) (hx : x ⊆ ordZ α) : HOD x := by
  apply hV
  rw [mem_vonNeumann]
  calc rank x ≤ rank (ordZ α) := rank_mono hx
    _ = α := rank_toZFSet α
    _ < lam := hα

/-- **Clause (1): `lam` is the least exacting cardinal**, as soon as `V_lam ⊆ HOD`
(known: [ABGL, Corollary 3.10]).  A smaller exacting `d.ord` would have a countable
cofinal subset of rank below `lam`, hence in `HOD`, contradicting its `HOD`-regularity. -/
theorem no_smaller_exacting (c d : Cardinal.{u}) (hd : ℵ₀ ≤ d) (hdc : d < c)
    (hV : ∀ x ∈ V_ c.ord, HOD x) : ¬ Ex d.ord := by
  intro hEx
  obtain ⟨s, -, hlt, hcof⟩ := Published.cof_omega_of_witness d hd hEx.witnesses
  have hrank : seqSet s ∈ V_ c.ord := by
    rw [mem_vonNeumann]
    have hsub : seqSet s ⊆ ordZ d.ord := by
      intro x hx
      obtain ⟨n, rfl⟩ := mem_seqSet.mp hx
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlt n)
    calc rank (seqSet s) ≤ rank (ordZ d.ord) := rank_mono hsub
      _ = d.ord := rank_toZFSet _
      _ < c.ord := Cardinal.ord_lt_ord.mpr hdc
  exact seqSet_notMem_HOD d hd hEx s hlt hcof (hV _ hrank)

end Cardinals

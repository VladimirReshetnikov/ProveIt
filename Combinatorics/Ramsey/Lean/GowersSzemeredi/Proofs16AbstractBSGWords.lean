import GowersSzemeredi.Proofs16ColumnWordRepresentations
import GowersSzemeredi.Proofs16AbstractBSGPruning

/-! Compatible words for an arbitrary quadruple relation on a prime cyclic
index group. The relation can express bounded image, rather than exact
agreement of local maps. Splicing reuses the existing injective geometry. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def relationTripleRepresentations {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) (a : ZMod N) :
    Finset (ZMod N × ZMod N × ZMod N) :=
  (B ×ˢ B ×ˢ B).filter fun t => a = t.1 - t.2.1 + t.2.2 ∧ R a t.1 t.2.2 t.2.1

def mixedRelationQuadruples {N : Nat} [NeZero N] (U V : Finset (ZMod N))
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => q 0 ∈ U ∧ q 2 ∈ U ∧ q 1 ∈ V ∧ q 3 ∈ V ∧
    q 0 + q 1 = q 2 + q 3 ∧ R (q 0) (q 2) (q 3) (q 1)

def relationWordRepresentations {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) :
    (as : List (ZMod N)) → Finset (ColumnWord N as.length)
  | [] => Finset.univ
  | [a] => Finset.univ.filter fun w => w.1 ∈ relationTripleRepresentations B R a
  | a :: b :: as => Finset.univ.filter fun w =>
      let p := columnWordUnsplice a (columnAnchorEval id (b :: as)) w
      p.2.1 ∈ relationTripleRepresentations B R a ∧
      p.2.2 ∈ relationWordRepresentations B R (b :: as) ∧
      p.1 ∈ mixedRelationQuadruples B B R

/-- The arbitrary relation is retained on both the original triples and
all splice quadruples. Every output represents the alternating anchor sum. -/
theorem relationWordRepresentations_spec {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) :
    ∀ (as : List (ZMod N)) (w : ColumnWord N as.length),
      w ∈ relationWordRepresentations B R as →
      columnWordIn B w ∧ columnWordValue w = columnAnchorEval id as := by
  intro as
  induction as with
  | nil => intro w _; exact ⟨True.intro, rfl⟩
  | cons a as ih =>
    cases as with
    | nil =>
      intro w hw
      obtain ⟨hm, he, _⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hw).2
      simp only [Finset.mem_product] at hm
      obtain ⟨h1, h2, h3⟩ := hm
      exact ⟨⟨h1, h2, h3, True.intro⟩, by
        simpa [columnWordValue, columnWordEval, columnAnchorEval] using he.symm⟩
    | cons b as =>
      intro w hw
      obtain ⟨_, hy, hz, hq⟩ := Finset.mem_filter.mp hw
      obtain ⟨hm, he, _⟩ := Finset.mem_filter.mp hy
      simp only [Finset.mem_product] at hm
      obtain ⟨h1, h2, h3⟩ := hm
      have hzs := ih _ hz
      obtain ⟨_, hq0, hq2, hq1, hq3, hadd, _⟩ := Finset.mem_filter.mp hq
      refine ⟨⟨h1, h2, hq0, hq3, hzs.1.2.1, hzs.1.2.2.1, hzs.1.2.2.2⟩, ?_⟩
      change w.1.2.2 + (columnAnchorEval id (b::as) + w.2.1.2.1 -
        w.2.1.2.2 + columnWordValue w.2.2) =
        (a - w.1.1 + w.1.2.1) + w.2.1.1 at hadd
      change w.1.1 - w.1.2.1 + w.1.2.2 -
        (w.2.1.1 - w.2.1.2.1 + w.2.1.2.2 - columnWordValue w.2.2) =
        a - columnAnchorEval id (b::as)
      linear_combination hadd

/-- Compatible splice data gives a longer word for the same relation. -/
theorem relationWordSplice_mem {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (a b : ZMod N) (as : List (ZMod N))
    {p : ColumnWordSpliceData N as.length}
    (hq : p.1 ∈ mixedRelationQuadruples B B R)
    (hyrep : p.2.1 ∈ relationTripleRepresentations B R a)
    (hzrep : p.2.2 ∈ relationWordRepresentations B R (b::as))
    (hy : p.2.1.2.2 = p.1 2) (hz : p.2.2.1.1 = p.1 1) :
    columnWordSplice p ∈ relationWordRepresentations B R (a::b::as) := by
  have hrec := columnWordUnsplice_splice a (columnAnchorEval id (b::as)) p
    (Finset.mem_filter.mp hyrep).2.1
    (relationWordRepresentations_spec B R (b::as) _ hzrep).2 hy hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hrec]; exact ⟨hyrep, hzrep, hq⟩⟩

/-- The one-anchor family is exactly the rich-count family, with the last
two entries permuted. -/
theorem relationTripleRepresentations_card {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (a : ZMod N) : (relationTripleRepresentations B R a).card = richCount B R a := by
  unfold richCount
  refine Finset.card_bij (fun t _ => (t.1, t.2.2, t.2.1)) ?_ ?_ ?_
  · intro t ht
    simp only [relationTripleRepresentations, Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, he, hr⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨h1, h3, h2⟩, by linear_combination he, hr⟩
  · intro t _ u _ he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.1 (Prod.ext he.2.2 he.2.1)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, he, hr⟩ := ht
    refine ⟨(t.1, t.2.2, t.2.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨h1, Finset.mem_product.mpr ⟨h3, h2⟩⟩, ?_, hr⟩, rfl⟩
    linear_combination he

end LeanProofs.GowersSzemeredi

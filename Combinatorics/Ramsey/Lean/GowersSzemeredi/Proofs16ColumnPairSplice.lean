import GowersSzemeredi.Proofs16FibreGluingCount

/-! Glue two column triples through an exact mixed quadruple. The six
output entries recover the input, so counting loses no multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

abbrev ColumnPairSpliceData (N : Nat) := (Fin 4 → ZMod N) ×
  (ZMod N × ZMod N × ZMod N) × (ZMod N × ZMod N × ZMod N)

def columnPairSplice {N : Nat} (p : ColumnPairSpliceData N) : Fin 6 → ZMod N :=
  ![p.2.1.1,p.2.1.2.1,p.1 0,p.1 3,p.2.2.2.1,p.2.2.2.2]

def columnPairUnsplice {N : Nat} (a b : ZMod N) (s : Fin 6 → ZMod N) : ColumnPairSpliceData N :=
  (![s 2,b+s 4-s 5,a-s 0+s 1,s 3],
    (s 0,s 1,a-s 0+s 1),(b+s 4-s 5,s 4,s 5))

def columnPairRepresentations {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (a b : ZMod N) : Finset (Fin 6 → ZMod N) :=
  Finset.univ.filter (fun s =>
    (columnPairUnsplice a b s).2.1 ∈ columnTripleRepresentations B T L r a ∧
    (columnPairUnsplice a b s).2.2 ∈ columnTripleRepresentations B T L r b ∧
    (columnPairUnsplice a b s).1 ∈ exactColumnQuadruples B T L r)

/-- The two anchor equations reconstruct the old middle endpoints. -/
theorem columnPairUnsplice_splice {N : Nat} (a b : ZMod N) (p : ColumnPairSpliceData N)
    (ha : a = p.2.1.1-p.2.1.2.1+p.2.1.2.2)
    (hb : b = p.2.2.1-p.2.2.2.1+p.2.2.2.2)
    (hy : p.2.1.2.2 = p.1 2) (hz : p.2.2.1 = p.1 1) :
    columnPairUnsplice a b (columnPairSplice p) = p := by
  apply Prod.ext
  · funext i; fin_cases i
    · rfl
    · change b+p.2.2.2.1-p.2.2.2.2 = p.1 1
      linear_combination hb+hz
    · change a-p.2.1.1+p.2.1.2.1 = p.1 2
      linear_combination ha+hy
    · rfl
  · apply Prod.ext
    · refine Prod.ext rfl (Prod.ext rfl ?_)
      change a-p.2.1.1+p.2.1.2.1 = p.2.1.2.2
      linear_combination ha
    · refine Prod.ext ?_ (Prod.ext rfl rfl)
      change b+p.2.2.2.1-p.2.2.2.2 = p.2.2.1
      linear_combination hb

/-- Valid gluing data inject into six-entry representations. -/
theorem columnPairSplice_injOn {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a b : ZMod N)
    (Q : Finset (Fin 4 → ZMod N)) :
    Set.InjOn (columnPairSplice (N := N)) ↑(fibreGluings Q
      (columnTripleRepresentations B T L r a) (columnTripleRepresentations B T L r b)
      (fun y => y.2.2) (fun z => z.1) (fun q => q 2) (fun q => q 1)) := by
  have hrec : ∀ p ∈ fibreGluings Q (columnTripleRepresentations B T L r a)
      (columnTripleRepresentations B T L r b) (fun y => y.2.2) (fun z => z.1) (fun q => q 2) (fun q => q 1),
      columnPairUnsplice a b (columnPairSplice p) = p := by
    intro p hp
    obtain ⟨hprod,hy,hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hpair⟩ := Finset.mem_product.mp hprod
    obtain ⟨hyrep,hzrep⟩ := Finset.mem_product.mp hpair
    exact columnPairUnsplice_splice a b p
      (columnTripleRepresentations_spec B T L r hyrep).2.2.2.2.1
      (columnTripleRepresentations_spec B T L r hzrep).2.2.2.2.1 hy hz
  intro p hp q hq heq
  exact (hrec p hp).symm.trans ((congrArg (columnPairUnsplice a b) heq).trans (hrec q hq))

/-- Exact connecting quadruples produce valid nested representations. -/
theorem columnPairSplice_mem {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a b : ZMod N)
    {p : ColumnPairSpliceData N} (hq : p.1 ∈ exactColumnQuadruples B T L r)
    (hyrep : p.2.1 ∈ columnTripleRepresentations B T L r a)
    (hzrep : p.2.2 ∈ columnTripleRepresentations B T L r b)
    (hy : p.2.1.2.2 = p.1 2) (hz : p.2.2.1 = p.1 1) :
    columnPairSplice p ∈ columnPairRepresentations B T L r a b := by
  have hrec := columnPairUnsplice_splice a b p
    (columnTripleRepresentations_spec B T L r hyrep).2.2.2.2.1
    (columnTripleRepresentations_spec B T L r hzrep).2.2.2.2.1 hy hz
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by rw [hrec]; exact ⟨hyrep,hzrep,hq⟩⟩

/-- A glued representation records the index difference and its map
identity on the output and two recoverable intermediate domains. -/
theorem columnPairRepresentations_spec {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) {a b : ZMod N}
    {s : Fin 6 → ZMod N} (hs : s ∈ columnPairRepresentations B T L r a b) :
    (∀ i, s i ∈ B) ∧ a-b = s 0-s 1+s 2-s 3+s 4-s 5 ∧
      (∀ y, y ∈ bohr (T a) r → y ∈ bohr (T b) r →
        (∀ i, y ∈ bohr (T (s i)) r) → y ∈ bohr (T (a-s 0+s 1)) r →
        y ∈ bohr (T (b+s 4-s 5)) r →
        L a y-L b y = L (s 0) y-L (s 1) y+L (s 2) y-L (s 3) y+L (s 4) y-L (s 5) y) := by
  obtain ⟨_,hy,hz,hq⟩ := Finset.mem_filter.mp hs
  have hyS := columnTripleRepresentations_spec B T L r hy
  have hzS := columnTripleRepresentations_spec B T L r hz
  obtain ⟨_,hqB,hadd,hval⟩ := Finset.mem_filter.mp hq
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i
    · exact hyS.2.1
    · exact hyS.2.2.1
    · exact hqB 0
    · exact hqB 3
    · exact hzS.2.2.1
    · exact hzS.2.2.2.1
  · change s 2+(b+s 4-s 5) = (a-s 0+s 1)+s 3 at hadd
    linear_combination -hadd
  · intro y ha hb hsy holdy holdz
    have e1 := hyS.2.2.2.2.2 y ha (hsy 0) (hsy 1) holdy
    have e2 := hzS.2.2.2.2.2 y hb holdz (hsy 4) (hsy 5)
    have hqy : ∀ i, y ∈ bohr (T ((columnPairUnsplice a b s).1 i)) r := by
      intro i; fin_cases i
      · exact hsy 2
      · exact holdz
      · exact holdy
      · exact hsy 3
    have e3 := hval y hqy
    change L a y = L (s 0) y-L (s 1) y+L (a-s 0+s 1) y at e1
    change L b y = L (b+s 4-s 5) y-L (s 4) y+L (s 5) y at e2
    change L (s 2) y+L (b+s 4-s 5) y = L (a-s 0+s 1) y+L (s 3) y at e3
    linear_combination e1-e2-e3

end LeanProofs.GowersSzemeredi

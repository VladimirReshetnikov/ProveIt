import GowersSzemeredi.Proofs16ColumnWordSplice

/-! Compatible representations of arbitrary finite lists of column anchors.
Recovered intermediate column domains are part of the identity hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnAnchorEval {N : Nat} (f : ZMod N → ZMod N) : List (ZMod N) → ZMod N
  | [] => 0
  | a :: as => f a-columnAnchorEval f as

def columnWordRepresentations {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    (as : List (ZMod N)) → Finset (ColumnWord N as.length)
  | [] => Finset.univ
  | [a] => Finset.univ.filter (fun w => w.1 ∈ columnTripleRepresentations B T L r a)
  | a :: b :: as => Finset.univ.filter (fun w =>
      let p := columnWordUnsplice a (columnAnchorEval id (b::as)) w
      p.2.1 ∈ columnTripleRepresentations B T L r a ∧
      p.2.2 ∈ columnWordRepresentations B T L r (b::as) ∧
      p.1 ∈ exactColumnQuadruples B T L r)

def columnWordDomain {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N)) (r : Real) :
    (as : List (ZMod N)) → ColumnWord N as.length → ZMod N → Prop
  | [], _, _ => True
  | [a], w, y => y ∈ bohr (T a) r ∧ y ∈ bohr (T w.1.1) r ∧
      y ∈ bohr (T w.1.2.1) r ∧ y ∈ bohr (T w.1.2.2) r
  | a :: b :: as, w, y =>
      let p := columnWordUnsplice a (columnAnchorEval id (b::as)) w
      (y ∈ bohr (T a) r ∧ y ∈ bohr (T p.2.1.1) r ∧
        y ∈ bohr (T p.2.1.2.1) r ∧ y ∈ bohr (T p.2.1.2.2) r) ∧
      columnWordDomain T r (b::as) p.2.2 y ∧ (∀ i, y ∈ bohr (T (p.1 i)) r)

/-- Every recursively compatible word represents the alternating anchor sum. -/
theorem columnWordRepresentations_spec {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    ∀ (as : List (ZMod N)) (w : ColumnWord N as.length),
      w ∈ columnWordRepresentations B T L r as →
      columnWordIn B w ∧ columnWordValue w = columnAnchorEval id as ∧
      ∀ y, columnWordDomain T r as w y →
        columnWordEval (fun x => L x y) w = columnAnchorEval (fun x => L x y) as := by
  intro as
  induction as with
  | nil => intro w _; exact ⟨True.intro,rfl,fun _ _ => rfl⟩
  | cons a as ih =>
    cases as with
    | nil =>
      intro w hw
      have ht := columnTripleRepresentations_spec B T L r (Finset.mem_filter.mp hw).2
      refine ⟨⟨ht.2.1,ht.2.2.1,ht.2.2.2.1,True.intro⟩,?_,?_⟩
      · simpa [columnWordValue,columnWordEval,columnAnchorEval] using ht.2.2.2.2.1.symm
      · intro y hy
        exact (by simpa [columnWordEval,columnAnchorEval] using
          (ht.2.2.2.2.2 y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2).symm)
    | cons b as =>
      intro w hw
      obtain ⟨_,hy,hz,hq⟩ := Finset.mem_filter.mp hw
      have hys := columnTripleRepresentations_spec B T L r hy
      have hzs := ih _ hz
      obtain ⟨_,hqB,hadd,hmap⟩ := Finset.mem_filter.mp hq
      refine ⟨?_,?_,?_⟩
      · exact ⟨hys.2.1,hys.2.2.1,hqB 0,hqB 3,hzs.1.2.1,hzs.1.2.2.1,hzs.1.2.2.2⟩
      · change w.1.2.2+(columnAnchorEval id (b::as)+w.2.1.2.1-w.2.1.2.2+columnWordValue w.2.2) =
          (a-w.1.1+w.1.2.1)+w.2.1.1 at hadd
        change w.1.1-w.1.2.1+w.1.2.2-
          (w.2.1.1-w.2.1.2.1+w.2.1.2.2-columnWordValue w.2.2) = a-columnAnchorEval id (b::as)
        linear_combination hadd
      · intro y hd
        obtain ⟨ht,hdz,hdq⟩ := hd
        have ey := hys.2.2.2.2.2 y ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
        have ez := hzs.2.2 y hdz
        have eq := hmap y hdq
        change L a y = L w.1.1 y-L w.1.2.1 y+L (a-w.1.1+w.1.2.1) y at ey
        change L (columnAnchorEval id (b::as)+w.2.1.2.1-w.2.1.2.2+columnWordValue w.2.2) y-
          L w.2.1.2.1 y+L w.2.1.2.2 y-columnWordEval (fun x => L x y) w.2.2 =
          columnAnchorEval (fun x => L x y) (b::as) at ez
        change L w.1.2.2 y+L (columnAnchorEval id (b::as)+w.2.1.2.1-w.2.1.2.2+columnWordValue w.2.2) y =
          L (a-w.1.1+w.1.2.1) y+L w.2.1.1 y at eq
        change L w.1.1 y-L w.1.2.1 y+L w.1.2.2 y-
          (L w.2.1.1 y-L w.2.1.2.1 y+L w.2.1.2.2 y-columnWordEval (fun x => L x y) w.2.2) =
          L a y-columnAnchorEval (fun x => L x y) (b::as)
        linear_combination -ey-ez+eq

/-- Splicing a valid triple with a valid nonempty word yields a valid longer word. -/
theorem columnWordSplice_mem {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a b : ZMod N) (as : List (ZMod N))
    {p : ColumnWordSpliceData N as.length}
    (hq : p.1 ∈ exactColumnQuadruples B T L r)
    (hyrep : p.2.1 ∈ columnTripleRepresentations B T L r a)
    (hzrep : p.2.2 ∈ columnWordRepresentations B T L r (b::as))
    (hy : p.2.1.2.2 = p.1 2) (hz : p.2.2.1.1 = p.1 1) :
    columnWordSplice p ∈ columnWordRepresentations B T L r (a::b::as) := by
  have hrec := columnWordUnsplice_splice a (columnAnchorEval id (b::as)) p
    (columnTripleRepresentations_spec B T L r hyrep).2.2.2.2.1
    (columnWordRepresentations_spec B T L r (b::as) _ hzrep).2.1 hy hz
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,by rw [hrec]; exact ⟨hyrep,hzrep,hq⟩⟩

end LeanProofs.GowersSzemeredi

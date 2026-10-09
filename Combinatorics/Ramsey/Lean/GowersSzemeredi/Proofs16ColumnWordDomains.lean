import GowersSzemeredi.Proofs16ColumnWordRepresentations

/-! Only two recovered columns per splice are needed in addition to the
anchors and output entries. This is the auxiliary rank budget for removal. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnWordEntries {N : Nat} : {k : Nat} → ColumnWord N k → List (ZMod N)
  | 0, _ => []
  | _+1, w => w.1.1 :: w.1.2.1 :: w.1.2.2 :: columnWordEntries w.2

def columnWordAux {N : Nat} : (as : List (ZMod N)) → ColumnWord N as.length → List (ZMod N)
  | [], _ => []
  | [_], _ => []
  | a :: b :: as, w =>
      let p := columnWordUnsplice a (columnAnchorEval id (b::as)) w
      p.2.1.2.2 :: p.2.2.1.1 :: columnWordAux (b::as) p.2.2

theorem columnWordEntries_length {N k : Nat} (w : ColumnWord N k) :
    (columnWordEntries w).length = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [columnWordEntries, List.length_cons, ih]; omega

theorem columnWordAux_length {N : Nat} (a : ZMod N) (as : List (ZMod N))
    (w : ColumnWord N (a::as).length) : (columnWordAux (a::as) w).length = 2*as.length := by
  induction as generalizing a with
  | nil => rfl
  | cons b as ih => simp only [columnWordAux, List.length_cons, ih]; omega

theorem columnWordEntries_mem {N k : Nat} (B : Finset (ZMod N)) (w : ColumnWord N k)
    (hw : columnWordIn B w) : ∀ x ∈ columnWordEntries w, x ∈ B := by
  induction k with
  | zero => simp [columnWordEntries]
  | succ k ih =>
    intro x hx
    simp only [columnWordEntries,List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact hw.1
    · exact hw.2.1
    · exact hw.2.2.1
    · exact ih w.2 hw.2.2.2 x hx

/-- All auxiliary columns of a valid representation belong to its ambient set. -/
theorem columnWordAux_mem {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (as : List (ZMod N))
    (w : ColumnWord N as.length) (hw : w ∈ columnWordRepresentations B T L r as) :
    ∀ x ∈ columnWordAux as w, x ∈ B := by
  induction as with
  | nil => simp [columnWordAux]
  | cons a as ih =>
    cases as with
    | nil => simp [columnWordAux]
    | cons b as =>
      obtain ⟨_,hy,hz,_⟩ := Finset.mem_filter.mp hw
      have hys := columnTripleRepresentations_spec B T L r hy
      have hzs := columnWordRepresentations_spec B T L r (b::as) _ hz
      intro x hx
      simp only [columnWordAux,List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hys.2.2.2.1
      · exact hzs.1.1
      · exact ih _ hz x hx

/-- Anchor, output, and two auxiliary columns per splice suffice for the
full recursive domain. No other intermediate columns are required. -/
theorem columnWordDomain_of_entries_aux {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (r : Real) (as : List (ZMod N))
    (w : ColumnWord N as.length) (y : ZMod N)
    (ha : ∀ x ∈ as, y ∈ bohr (T x) r)
    (hw : ∀ x ∈ columnWordEntries w, y ∈ bohr (T x) r)
    (hu : ∀ x ∈ columnWordAux as w, y ∈ bohr (T x) r) :
    columnWordDomain T r as w y := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    cases as with
    | nil =>
      exact ⟨ha a (by simp), hw _ (by simp [columnWordEntries]),
        hw _ (by simp [columnWordEntries]),hw _ (by simp [columnWordEntries])⟩
    | cons b as =>
      let p := columnWordUnsplice a (columnAnchorEval id (b::as)) w
      have hyl : y ∈ bohr (T p.2.1.2.2) r := hu _ (by simp [columnWordAux,p])
      have hzf : y ∈ bohr (T p.2.2.1.1) r := hu _ (by simp [columnWordAux,p])
      have hzentries : ∀ x ∈ columnWordEntries p.2.2, y ∈ bohr (T x) r := by
        intro x hx
        change x ∈ p.2.2.1.1 :: w.2.1.2.1 :: w.2.1.2.2 :: columnWordEntries w.2.2 at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hzf
        · exact hw x (by simp only [columnWordEntries,List.mem_cons] at hx ⊢; tauto)
      have hzaux : ∀ x ∈ columnWordAux (b::as) p.2.2, y ∈ bohr (T x) r := by
        intro x hx
        exact hu x (by simp only [columnWordAux,List.mem_cons]; exact Or.inr (Or.inr hx))
      refine ⟨⟨ha a (by simp),hw _ (by simp [columnWordUnsplice,columnWordEntries]),
        hw _ (by simp [columnWordUnsplice,columnWordEntries]),hyl⟩,?_,?_⟩
      · exact ih _ (fun x hx => ha x (List.mem_cons_of_mem a hx)) hzentries hzaux
      · intro i; fin_cases i
        · exact hw _ (by simp [columnWordUnsplice,columnWordEntries])
        · exact hzf
        · exact hyl
        · exact hw _ (by simp [columnWordUnsplice,columnWordEntries])

/-- Flattening the triple blocks gives the ordinary alternating list evaluation. -/
theorem columnWordEval_eq_entries {N k : Nat} (f : ZMod N → ZMod N) (w : ColumnWord N k) :
    columnWordEval f w = columnAnchorEval f (columnWordEntries w) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [columnWordEval,columnWordEntries,columnAnchorEval,ih]; ring

end LeanProofs.GowersSzemeredi

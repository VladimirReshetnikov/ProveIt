import GowersSzemeredi.Proofs16ColumnWords

/-! An injective splice prepends a triple to a word of any positive length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

abbrev ColumnWordSpliceData (N k : Nat) := (Fin 4 → ZMod N) ×
  (ZMod N × ZMod N × ZMod N) × ColumnWord N (k+1)

def columnWordSplice {N k : Nat} (p : ColumnWordSpliceData N k) : ColumnWord N (k+2) :=
  ((p.2.1.1,p.2.1.2.1,p.1 0),((p.1 3,p.2.2.1.2.1,p.2.2.1.2.2),p.2.2.2))

def columnWordUnsplice {N k : Nat} (a b : ZMod N) (w : ColumnWord N (k+2)) : ColumnWordSpliceData N k :=
  (![w.1.2.2,b+w.2.1.2.1-w.2.1.2.2+columnWordValue w.2.2,a-w.1.1+w.1.2.1,w.2.1.1],
    (w.1.1,w.1.2.1,a-w.1.1+w.1.2.1),
    ((b+w.2.1.2.1-w.2.1.2.2+columnWordValue w.2.2,w.2.1.2.1,w.2.1.2.2),w.2.2))

/-- Anchor values recover both replaced entries at every length. -/
theorem columnWordUnsplice_splice {N k : Nat} (a b : ZMod N) (p : ColumnWordSpliceData N k)
    (ha : a = p.2.1.1-p.2.1.2.1+p.2.1.2.2)
    (hb : columnWordValue p.2.2 = b)
    (hy : p.2.1.2.2 = p.1 2) (hz : p.2.2.1.1 = p.1 1) :
    columnWordUnsplice a b (columnWordSplice p) = p := by
  have hy' : a-p.2.1.1+p.2.1.2.1 = p.2.1.2.2 := by linear_combination ha
  have hz' : b+p.2.2.1.2.1-p.2.2.1.2.2+columnWordValue p.2.2.2 = p.2.2.1.1 := by
    change p.2.2.1.1-p.2.2.1.2.1+p.2.2.1.2.2-columnWordValue p.2.2.2 = b at hb
    linear_combination -hb
  apply Prod.ext
  · funext i; fin_cases i
    · rfl
    · exact hz'.trans hz
    · exact hy'.trans hy
    · rfl
  · exact Prod.ext (Prod.ext rfl (Prod.ext rfl hy')) (Prod.ext (Prod.ext hz' rfl) rfl)

/-- No multiplicity is lost when the input families have fixed values. -/
theorem columnWordSplice_injOn {N k : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (S : Finset (ZMod N × ZMod N × ZMod N))
    (R : Finset (ColumnWord N (k+1))) (a b : ZMod N)
    (hS : ∀ y ∈ S, a = y.1-y.2.1+y.2.2)
    (hR : ∀ z ∈ R, columnWordValue z = b) :
    Set.InjOn (columnWordSplice (N := N) (k := k)) ↑(fibreGluings Q S R
      (fun y => y.2.2) (fun z => z.1.1) (fun q => q 2) (fun q => q 1)) := by
  have hrec : ∀ p ∈ fibreGluings Q S R (fun y => y.2.2) (fun z => z.1.1)
      (fun q => q 2) (fun q => q 1), columnWordUnsplice a b (columnWordSplice p) = p := by
    intro p hp
    obtain ⟨hprod,hy,hz⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hpair⟩ := Finset.mem_product.mp hprod
    obtain ⟨hys,hzr⟩ := Finset.mem_product.mp hpair
    exact columnWordUnsplice_splice a b p (hS _ hys) (hR _ hzr) hy hz
  intro p hp q hq he
  exact (hrec p hp).symm.trans ((congrArg (columnWordUnsplice a b) he).trans (hrec q hq))

/-- The splice subtracts represented values, as required for alternating blocks. -/
theorem columnWordSplice_value {N k : Nat} (p : ColumnWordSpliceData N k)
    (hq : p.1 0+p.1 1 = p.1 2+p.1 3)
    (hy : p.2.1.2.2 = p.1 2) (hz : p.2.2.1.1 = p.1 1) :
    columnWordValue (columnWordSplice p) =
      (p.2.1.1-p.2.1.2.1+p.2.1.2.2)-columnWordValue p.2.2 := by
  change p.2.1.1-p.2.1.2.1+p.1 0-
    (p.1 3-p.2.2.1.2.1+p.2.2.1.2.2-columnWordValue p.2.2.2) =
    (p.2.1.1-p.2.1.2.1+p.2.1.2.2)-
    (p.2.2.1.1-p.2.2.1.2.1+p.2.2.1.2.2-columnWordValue p.2.2.2)
  linear_combination hq-hy+hz

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16ColumnWordRepresentations

/-! Repeating an existing anchor in cancelling pairs transfers a fixed
higher even relation to every shorter even relation on the same domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def columnPairPadding {N : Nat} (a : ZMod N) (as : List (ZMod N)) : Nat → List (ZMod N)
  | 0 => as
  | n+1 => a :: a :: columnPairPadding a as n

theorem columnPairPadding_length {N : Nat} (a : ZMod N) (as : List (ZMod N)) (n : Nat) :
    (columnPairPadding a as n).length = 2*n+as.length := by
  induction n with
  | zero => simp [columnPairPadding]
  | succ n ih => simp only [columnPairPadding,List.length_cons,ih]; omega

theorem columnPairPadding_eval {N : Nat} (f : ZMod N → ZMod N)
    (a : ZMod N) (as : List (ZMod N)) (n : Nat) :
    columnAnchorEval f (columnPairPadding a as n) = columnAnchorEval f as := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [columnPairPadding,columnAnchorEval,sub_sub_cancel,ih]

theorem columnPairPadding_mem {N : Nat} (a : ZMod N) (as : List (ZMod N)) (n : Nat)
    (p : ZMod N → Prop) (ha : p a) (has : ∀ x ∈ as, p x) :
    ∀ x ∈ columnPairPadding a as n, p x := by
  induction n with
  | zero => exact has
  | succ n ih => simpa only [columnPairPadding,List.mem_cons,forall_eq_or_imp] using And.intro ha (And.intro ha ih)

/-- Shorter relations use a member of their own list for padding, so no
extra column-domain hypothesis or common frequency is needed. -/
theorem even_zero_relations_mono {N k m : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (s : Real) (hm : m ≤ k)
    (hzero : ∀ as : List (ZMod N), as.length = 2*k → (∀ x ∈ as, x ∈ P) →
      columnAnchorEval id as = 0 → ∀ y ∈ bohr Gamma s,
        (∀ x ∈ as, y ∈ bohr (T x) s) → columnAnchorEval (fun x => L x y) as = 0)
    (as : List (ZMod N)) (hlen : as.length = 2*m) (has : ∀ x ∈ as, x ∈ P)
    (hadd : columnAnchorEval id as = 0) (y : ZMod N) (hy : y ∈ bohr Gamma s)
    (hd : ∀ x ∈ as, y ∈ bohr (T x) s) : columnAnchorEval (fun x => L x y) as = 0 := by
  cases as with
  | nil => rfl
  | cons a as =>
    have h := hzero (columnPairPadding a (a::as) (k-m))
      (by rw [columnPairPadding_length,hlen]; omega)
      (columnPairPadding_mem a (a::as) (k-m) _ (has a (by simp)) has)
      (by simpa only [columnPairPadding_eval] using hadd) y hy
      (columnPairPadding_mem a (a::as) (k-m) _ (hd a (by simp)) hd)
    simpa only [columnPairPadding_eval] using h

end LeanProofs.GowersSzemeredi

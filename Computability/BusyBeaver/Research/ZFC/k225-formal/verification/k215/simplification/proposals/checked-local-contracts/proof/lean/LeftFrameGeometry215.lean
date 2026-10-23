import LeftFrameTemplates215

/-!
Bind the inherited template metadata to exact physical input and output tapes.
Only the RIGHT side is normalized. No unframed normL equality is used.
The whole-tape theorem is uniform in the prefix, gap and all valid registers.
Source-occurrence/routed-port coverage remains a separate integration obligation.
-/

namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215

open KZip KRuntimeCore KLeftFrame KTableCore

def suffixPort (q : Nat) (S : List Bool) : SConf :=
  (q, false, S.dropLast.reverse.map .bit,
    [.bit (S.getLastD false), .run false 1 16, .bit true, .box (.plain .none)])

def resultRight (S E : List Bool) : List Seg :=
  E.map .bit ++ [.run false 1 (16 + S.length - E.length), .bit true, .box (.plain .none)]

def checkGeometry (t : LocalTemplate) : Bool :=
  decide (0 < t.suffix.length) && decide (t.result.length ≤ t.suffix.length) &&
    (t.start == suffixPort t.start.1 t.suffix) &&
    (norm t.right == norm (resultRight t.suffix t.result))

theorem all_geometry_checked : templates.all checkGeometry = true := by
  decide +kernel

theorem template_geometry {t : LocalTemplate} (ht : t ∈ templates) :
    0 < t.suffix.length ∧ t.result.length ≤ t.suffix.length ∧
      t.start = suffixPort t.start.1 t.suffix ∧
      norm t.right = norm (resultRight t.suffix t.result) := by
  have h : checkGeometry t = true := List.all_eq_true.mp all_geometry_checked t ht
  simp only [checkGeometry, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem flat_bits (n : Nat) (vs : List Nat) (P : List Bool) :
    flat n vs (P.map .bit) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.map_cons, flat_cons, segList, ih]; rfl

private theorem flat_append (n : Nat) (vs : List Nat) (xs ys : List Seg) :
    flat n vs (xs ++ ys) = flat n vs xs ++ flat n vs ys := by
  simp [flat]

theorem suffixPort_conc (q : Nat) (P S : List Bool) (n : Nat) (vs : List Nat) :
    conc n vs (addLeft (P.reverse.map .bit ++ [.bit true]) (suffixPort q S)) =
      zc q ((P ++ S.dropLast).reverse ++ [true])
        (S.getLastD false :: List.replicate (n + 16) false ++ true :: sepsR vs) := by
  simp only [suffixPort, addLeft, conc, flat_append, flat_bits, flat_cons, flat_nil,
    segList, Nat.one_mul, boxList, List.reverse_append, List.append_assoc,
    List.cons_append, List.nil_append, List.append_nil]

theorem resultRight_flat (S E : List Bool) (n : Nat) (vs : List Nat) :
    flat n vs (resultRight S E) =
      E ++ List.replicate (n + (16 + S.length - E.length)) false ++ true :: sepsR vs := by
  simp only [resultRight, flat_append, flat_bits, flat_cons, flat_nil,
    segList, Nat.one_mul, boxList, List.append_assoc,
    List.cons_append, List.nil_append, List.append_nil]

theorem flat_right_of_norm {xs ys : List Seg} (h : norm xs = norm ys)
    (n : Nat) (vs : List Nat) : flat n vs xs = flat n vs ys := by
  rw [← flatT_norm, h, flatT_norm]

/-- All 35 templates are positive exact whole-tape contracts. Prefix cells and
the register file are preserved; the gap absorbs the suffix-length difference.
No concrete choice of prefix, natural gap, or register values is fixed. -/
theorem every_template_full (B : BoxLemmas tm215)
    (rows : KHome.Rows tm215) (hb : KHome.Boundary tm215)
    {t : LocalTemplate} (ht : t ∈ templates)
    (P : List Bool) {j : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215
      (zc t.start.1 ((P ++ t.suffix.dropLast).reverse ++ [true])
        (t.suffix.getLastD false :: List.replicate (n + 16) false ++ true :: sepsR vs))
      (zc 84 [true]
        (P ++ t.result ++ List.replicate (n + (16 + t.suffix.length - t.result.length)) false ++
          true :: sepsR vs)) := by
  obtain ⟨_, _, hstart, hright⟩ := template_geometry ht
  have hh := every_template_sound B rows hb ht P hs n hv
  rw [hstart, suffixPort_conc] at hh
  rw [flat_right_of_norm hright n vs, resultRight_flat] at hh
  simpa only [List.append_assoc] using hh

#print axioms all_geometry_checked
#print axioms template_geometry
#print axioms every_template_full

end SetTheory.BusyBeaver.ZFC.KLeftFrame215

/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import MoserWorm.UpperBound.Certificate.Checker

namespace MoserWorm.UpperBound.Certificate.Partition

abbrev R4 := ℕ × ℕ × ℕ × ℕ
theorem forIn_loop_eq {α : Type} (p : α → Bool) (cells : List α) :
    (forIn (m := Id) cells ((none : Option Bool), ()) (fun x _ =>
      if (!p x) = true then pure (ForInStep.done (some false, ()))
      else pure (ForInStep.yield (none, ())))) =
    pure (if cells.all p then ((none : Option Bool), ()) else (some false, ())) := by
  induction cells with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.forIn_cons]
    by_cases h : p hd
    · simp only [h, Bool.not_true, Bool.false_eq_true, if_false, List.all_cons, Bool.true_and]
      exact ih
    · simp [h]

def insideOK (rect cell : R4) : Bool :=
  rect.1 ≤ cell.1 && cell.1 ≤ cell.2.1 && cell.2.1 ≤ rect.2.1 &&
    rect.2.2.1 ≤ cell.2.2.1 && cell.2.2.1 ≤ cell.2.2.2 && cell.2.2.2 ≤ rect.2.2.2

def splitStruct (cells : List (R4 × CTree)) (rect : R4) : Bool :=
  cells.all (fun x => insideOK rect x.1) &&
  checkTree.pairwiseOk (cells.map (fun x => x.1)) &&
  ((cells.map (fun x => x.1)).foldl
      (fun acc x => acc + (x.2.1 - x.1 + 1) * (x.2.2.2 - x.2.2.1 + 1)) 0
    == (rect.2.1 - rect.1 + 1) * (rect.2.2.2 - rect.2.2.1 + 1))

theorem checkTree_split_eq (ctx : Ctx) (fuel : ℕ)
    (cells : List (R4 × CTree)) (assign : List (ℕ × Fin 2)) (rect : R4) :
    checkTree ctx (fuel + 1) (.split cells) assign rect =
      (splitStruct cells rect &&
       cells.all (fun x => checkTree ctx fuel x.2 assign x.1)) := by
  simp only [checkTree]
  rw [forIn_loop_eq, forIn_loop_eq]
  simp only [splitStruct, insideOK]
  split
  case isFalse h => rw [Bool.not_eq_true] at h; simp only [h, Bool.false_and]; rfl
  case isTrue hA =>
    rw [hA, Bool.true_and]
    split
    case isTrue h => rw [Bool.not_eq_true'] at h; simp only [h, Bool.false_and]; rfl
    case isFalse h =>
      have h' : checkTree.pairwiseOk (List.map (fun x => x.1) cells) = true := by
        simpa using h
      rw [h', Bool.true_and]
      split
      case isTrue h2 =>
        simp only [bne_iff_ne, ne_eq] at h2
        rw [beq_eq_false_iff_ne.mpr h2, Bool.false_and]; rfl
      case isFalse h2 =>
        simp only [bne_iff_ne, ne_eq, not_not] at h2
        rw [beq_iff_eq.mpr h2, Bool.true_and]
        split
        case isTrue hB => rw [hB]; rfl
        case isFalse hB =>
          have hB' : (cells.all fun x => checkTree ctx fuel x.2 assign x.1) = false := by
            simpa using hB
          rw [hB']; rfl

/-- One frontier obligation: subtree, assignment path, rectangle. -/
abbrev Ob := CTree × List (ℕ × Fin 2) × R4

theorem checkTree_pl_eq (ctx : Ctx) (fuel : ℕ) (m : ℕ) (c0 c1 : CTree)
    (assign : List (ℕ × Fin 2)) (rect : R4) :
    checkTree ctx (fuel + 1) (.pl m c0 c1) assign rect =
      ((2 * m + 1 < ctx.eRows.size) &&
       !(assign.any (fun (m', _) => m' == m)) &&
       checkTree ctx fuel c0 ((m, 0) :: assign) rect &&
       checkTree ctx fuel c1 ((m, 1) :: assign) rect) := rfl

theorem checkTree_leaf_eq (ctx : Ctx) (fuel : ℕ) (mu : List (RowKey × ℚ))
    (assign : List (ℕ × Fin 2)) (rect : R4) :
    checkTree ctx (fuel + 1) (.leaf mu) assign rect = checkLeaf ctx assign rect mu := rfl

/-- Frontier of obligations at cut depth `d` (leaves may stop early). -/
def cutFrontier : ℕ → CTree → List (ℕ × Fin 2) → R4 → List Ob
  | 0, t, as, r => [(t, as, r)]
  | d + 1, t, as, r =>
    match t with
    | .pl m c0 c1 => cutFrontier d c0 ((m, 0) :: as) r ++ cutFrontier d c1 ((m, 1) :: as) r
    | .split cells => cells.flatMap (fun x => cutFrontier d x.2 as x.1)
    | .leaf mu => [(.leaf mu, as, r)]

/-- Structural checks above the cut depth `d`. -/
def cutTop (ctx : Ctx) : ℕ → CTree → List (ℕ × Fin 2) → R4 → Bool
  | 0, _, _, _ => true
  | d + 1, t, as, r =>
    match t with
    | .pl m c0 c1 =>
        (2 * m + 1 < ctx.eRows.size) &&
        !(as.any (fun (m', _) => m' == m)) &&
        cutTop ctx d c0 ((m, 0) :: as) r &&
        cutTop ctx d c1 ((m, 1) :: as) r
    | .split cells =>
        splitStruct cells r && cells.all (fun x => cutTop ctx d x.2 as x.1)
    | .leaf _ => true

/-- Main reassembly: the full check follows from the structural top checks and
the frontier obligations, with exact fuel bookkeeping. -/
theorem checkTree_of_cut (ctx : Ctx) :
    ∀ (d fuel : ℕ) (t : CTree) (assign : List (ℕ × Fin 2)) (rect : R4),
      1 ≤ fuel →
      cutTop ctx d t assign rect = true →
      (∀ x ∈ cutFrontier d t assign rect, checkTree ctx fuel x.1 x.2.1 x.2.2 = true) →
      checkTree ctx (fuel + d) t assign rect = true := by
  intro d
  induction d with
  | zero =>
    intro fuel t as r _ _ hf
    exact hf (t, as, r) (by simp [cutFrontier])
  | succ d ih =>
    intro fuel t as r h1 htop hf
    rw [Nat.add_succ]
    match t with
    | .pl m c0 c1 =>
      rw [checkTree_pl_eq]
      simp only [cutTop, Bool.and_eq_true] at htop
      obtain ⟨⟨⟨hm, ha⟩, h0⟩, hc1⟩ := htop
      simp only [cutFrontier] at hf
      rw [hm, ha]
      rw [ih fuel c0 ((m, 0) :: as) r h1 h0
            (fun x hx => hf x (List.mem_append_left _ hx)),
          ih fuel c1 ((m, 1) :: as) r h1 hc1
            (fun x hx => hf x (List.mem_append_right _ hx))]
      rfl
    | .split cells =>
      rw [checkTree_split_eq]
      simp only [cutTop, Bool.and_eq_true] at htop
      obtain ⟨hs, hall⟩ := htop
      rw [hs, Bool.true_and, List.all_eq_true]
      intro x hx
      simp only [cutFrontier] at hf
      rw [List.all_eq_true] at hall
      exact ih fuel x.2 as x.1 h1 (hall x hx)
        (fun y hy => hf y (List.mem_flatMap.mpr ⟨x, hx, hy⟩))
    | .leaf mu =>
      simp only [cutFrontier] at hf
      have h := hf (.leaf mu, as, r) (by simp)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [checkTree_leaf_eq] at h
      exact h

/-! ### Wiring to `checkCert`/`checkAll` -/

/-- The context and root rectangle of a certificate, as built by `checkCert`. -/
def theCtxR (c : Cert) : Option (Ctx × R4) :=
  match buildLabels c.specs.toList with
  | none => none
  | some T =>
    some ({ T := T, eRows := eRowsArr c T (namedByAngle T), target := c.target },
          (0, T.kR, 0, T.kL))

/-- All of `checkCert` except the tree recursion. -/
def checkHeader (c : Cert) : Bool :=
  checkLiterals c &&
  c.specs.all (fun p => isOrtho (specMap p)) &&
  match buildLabels c.specs.toList with
  | none => false
  | some T =>
    T.kR == c.kR && T.kL == c.kL && labelsOK T &&
    (eRowsArr c T (namedByAngle T)).all Option.isSome

theorem checkCert_of_parts (c : Cert) (ctx : Ctx) (rect : R4)
    (hh : checkHeader c = true) (hc : theCtxR c = some (ctx, rect))
    (ht : checkTree ctx 1000 c.tree [] rect = true) :
    checkCert c = true := by
  unfold checkCert
  unfold checkHeader at hh
  unfold theCtxR at hc
  cases hb : buildLabels c.specs.toList with
  | none => rw [hb] at hc; cases hc
  | some T =>
    rw [hb] at hh hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨hctx, hrect⟩ := hc
    simp only [Bool.and_eq_true] at hh ⊢
    exact ⟨hh.1, hh.2, by rw [hctx, hrect]; exact ht⟩

end MoserWorm.UpperBound.Certificate.Partition

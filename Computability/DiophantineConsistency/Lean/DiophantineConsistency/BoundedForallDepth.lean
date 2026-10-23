import DiophantineConsistency.GraphSizeBounds

/-! # Numerical bounds for the one bounded-universal compiler template

The constants below are computed from fixed graph constructors. The variables
`m`, `p`, and `q` describe supplied syntax; no expression tree is constructed by
the resulting witness-count formula.
-/

namespace DiophantineConsistency.BoundedForallDepth

open Rep (Thin)

-- Name the existing wrapper without changing its frozen source module.
local macro "templateDvdGraphs" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `DiophantineConsistency.BoundedForallRepresentation
    `DiophantineConsistency.BoundedForallRepresentation.dvdGraphs))
local macro "unfoldTemplateDvd" : tactic => do
  let id := Lean.mkIdent (Lean.mkPrivateNameCore
    `DiophantineConsistency.BoundedForallRepresentation
    `DiophantineConsistency.BoundedForallRepresentation.dvdGraphs)
  `(tactic| unfold $id)

/-- Fixed witness counts are checked by reducing only their projections. -/
theorem sub_count : GraphRep.subCoordinates.witnessCount = 1 := rfl
theorem mod_count : GraphRep.modCoordinates.witnessCount = 2 := rfl
set_option maxRecDepth 10000 in
theorem pow_count : PowerRepresentation.coordinates.witnessCount = 111 := rfl
set_option maxRecDepth 10000 in
theorem binomial_count : FactorialRepresentation.binomialCoordinates.witnessCount = 598 := rfl
set_option maxRecDepth 10000 in
theorem factorial_count : FactorialRepresentation.factorialCoordinates.witnessCount = 1697 := rfl

/-- Closed arithmetic form of the bounded-universal witness recurrence. -/
theorem certificateCost_eq (m p q : ℕ) :
    BoundedForallSize.certificateCost m p q =
      m * (4 * p + 4 * q + 11798) + 10 * p + 10 * q + 20694 := by
  simp only [BoundedForallSize.certificateCost, BoundedForallSize.coordinateCost,
    BoundedForallSize.indexCost, BoundedForallSize.evaluationCost,
    BoundedForallSize.modulusCost, BoundedForallSize.scaleCost,
    BoundedForallSize.productCost, BoundedForallSize.addCost,
    BoundedForallSize.mulCost, BoundedForallSize.subCost,
    BoundedForallSize.modCost, BoundedForallSize.powCost,
    BoundedForallSize.binomialCost, BoundedForallSize.factorialCost,
    sub_count, mod_count, pow_count, binomial_count, factorial_count]
  ring

/-- The source residual's total split size alone determines the new witness count. -/
theorem boundedForall_witnessCount {σ : Type} {P : (Option σ → ℕ) → Prop}
    (r : Rep (Option σ) P) (b : σ) :
    (r.boundedForall b).witnessCount =
      r.witnessCount * (4 * r.expression.splitSize + 11790) +
        10 * r.expression.splitSize + 20674 := by
  rw [BoundedForallSize.boundedForall_count, certificateCost_eq]
  have hp := ExpressionSize.natGraph_witnessCount r.expression.splitNatural.1
  have hn := ExpressionSize.natGraph_witnessCount r.expression.splitNatural.2
  have hsp := (ExpressionSize.splitSize_correct r.expression).1
  have hsn := (ExpressionSize.splitSize_correct r.expression).2
  rw [hsp] at hp
  rw [hsn] at hn
  have hs : r.expression.splitSize = (ExpressionSize.splitSize r.expression).positive +
      (ExpressionSize.splitSize r.expression).negative := by
    rw [Expr.splitSize_eq, hsp, hsn]
  have he : 4 * ((ExpressionSize.splitSize r.expression).positive - 1) +
      4 * ((ExpressionSize.splitSize r.expression).negative - 1) + 11798 =
      4 * r.expression.splitSize + 11790 := by omega
  rw [he]
  omega

/- Fixed graph-depth ceilings, checked from the finite constructor data. -/
set_option maxRecDepth 10000 in
theorem pow_depth : PowerRepresentation.coordinates.depth ≤ 512 := by decide
set_option maxRecDepth 10000 in
theorem binomial_depth : FactorialRepresentation.binomialCoordinates.depth ≤ 512 := by decide

theorem div_depth : GraphRep.divCoordinates.depth ≤ 512 := by decide
theorem sub_depth : GraphRep.subCoordinates.depth ≤ 512 := by decide
theorem mod_depth : GraphRep.modCoordinates.depth ≤ 512 := by decide

theorem pow_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.pow s).depth ≤ h + 8 := by
  unfold GraphRep.pow
  refine (GraphRep.compose_depth_le _ _ (by omega) (pow_depth.trans hh) ?_).trans (by omega)
  intro i
  fin_cases i <;> assumption

theorem binomial_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.binomial s).depth ≤ h + 8 := by
  unfold GraphRep.binomial
  refine (GraphRep.compose_depth_le _ _ (by omega) (binomial_depth.trans hh) ?_).trans (by omega)
  intro i
  fin_cases i <;> assumption


theorem sub_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.sub s).depth ≤ h + 8 := by
  unfold GraphRep.sub
  refine (GraphRep.compose_depth_le _ _ (by omega) (sub_depth.trans hh) ?_).trans (by omega)
  intro i
  fin_cases i <;> assumption

theorem mod_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.mod s).depth ≤ h + 8 := by
  unfold GraphRep.mod
  refine (GraphRep.compose_depth_le _ _ (by omega) (mod_depth.trans hh) ?_).trans (by omega)
  intro i
  fin_cases i <;> assumption

theorem div_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 512 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.div s).depth ≤ h + 8 := by
  unfold GraphRep.div
  refine (GraphRep.compose_depth_le _ _ (by omega) (div_depth.trans hh) ?_).trans (by omega)
  intro i
  fin_cases i <;> assumption

theorem factorial_depth : FactorialRepresentation.factorialCoordinates.depth ≤ 16384 := by
  let n : GraphRep (fun v : Fin 1 → ℕ => v 0) := GraphRep.coordinate 0
  let shift := n.add (GraphRep.constant 2)
  let radius := shift.pow shift
  let c := (radius.add n).binomial n
  let numerator := ((radius.add (GraphRep.constant 1)).pow n).add
    (c.sub (GraphRep.constant 1))
  have hn : n.depth ≤ 512 := by decide
  have hcst (a : ℕ) : (GraphRep.constant (σ := Fin 1) a).depth ≤ 512 := by
    rw [GraphRep.depth_constant]; decide
  have hshift : shift.depth ≤ 518 := GraphRep.depth_add_le _ _ hn (hcst 2)
  have hradius : radius.depth ≤ 526 := pow_depth_le _ _ (by decide) hshift hshift
  have hradiusAdd : (radius.add n).depth ≤ 532 :=
    GraphRep.depth_add_le _ _ hradius (hn.trans (by decide))
  have hc : c.depth ≤ 540 := binomial_depth_le _ _ (by decide) hradiusAdd (hn.trans (by decide))
  have hleftAdd : (radius.add (GraphRep.constant 1)).depth ≤ 532 :=
    GraphRep.depth_add_le _ _ hradius ((hcst 1).trans (by decide))
  have hleft : ((radius.add (GraphRep.constant 1)).pow n).depth ≤ 540 :=
    pow_depth_le _ _ (by decide) hleftAdd (hn.trans (by decide))
  have hright : (c.sub (GraphRep.constant 1)).depth ≤ 548 :=
    sub_depth_le _ _ (by decide) hc ((hcst 1).trans (by decide))
  have hnum : numerator.depth ≤ 554 :=
    GraphRep.depth_add_le _ _ (hleft.trans (by decide)) hright
  have hlast : (numerator.div c).depth ≤ 562 :=
    div_depth_le _ _ (by decide) hnum (hc.trans (by decide))
  change (numerator.div c).depth ≤ 16384
  exact hlast.trans (by decide)

theorem factorial_depth_le {σ : Type*} {f : (σ → ℕ) → ℕ}
    (r : GraphRep f) {h : ℕ} (hh : 16384 ≤ h) (hr : r.depth ≤ h) :
    r.factorial.depth ≤ h + 6 := by
  unfold GraphRep.factorial
  exact (GraphRep.compose_depth_le _ _ (by omega) (factorial_depth.trans hh)
    (fun _ => hr)).trans (by omega)

theorem product_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (rn : GraphRep f) (rt : GraphRep g) {h : ℕ} (hh : 16384 ≤ h)
    (hn : rn.depth ≤ h) (ht : rt.depth ≤ h) :
    (BoundedForallRepresentation.productGraph rn rt).depth ≤ h + 66 := by
  let q := ((((rn.add (GraphRep.constant 1)).mul rt).add
    (GraphRep.constant 1)).pow rn).add (GraphRep.constant 2)
  have hc (n : ℕ) : (GraphRep.constant (σ := σ) n).depth ≤ h := by
    rw [GraphRep.depth_constant]; omega
  have h1 := GraphRep.depth_add_le rn (GraphRep.constant 1) hn (hc 1)
  have h2 := GraphRep.depth_mul_le (rn.add (GraphRep.constant 1)) rt h1 (ht.trans (by omega))
  have h3 := GraphRep.depth_add_le ((rn.add (GraphRep.constant 1)).mul rt)
    (GraphRep.constant 1) h2 ((hc 1).trans (by omega))
  have h4 := pow_depth_le _ rn (by omega) h3 (hn.trans (by omega))
  have hq : q.depth ≤ h + 32 :=
    (GraphRep.depth_add_le _ _ h4 ((hc 2).trans (by omega))).trans (by omega)
  have hpow := pow_depth_le rt rn (by omega) ht hn
  have hfact := factorial_depth_le rn hh hn
  have hadd := GraphRep.depth_add_le q rn hq (hn.trans (by omega))
  have hbin := binomial_depth_le (q.add rn) rn (by omega) hadd (hn.trans (by omega))
  have hmul := GraphRep.depth_mul_le rn.factorial ((q.add rn).binomial rn)
    (hfact.trans (by omega)) hbin
  have hfirst := GraphRep.depth_mul_le (rt.pow rn)
    (rn.factorial.mul ((q.add rn).binomial rn)) (hpow.trans (by omega)) hmul
  have hd0 := GraphRep.depth_mul_le rt q (ht.trans (by omega)) hq
  have hden := sub_depth_le (rt.mul q) (GraphRep.constant 1) (by omega) hd0
    ((hc 1).trans (by omega))
  exact mod_depth_le _ _ (by omega) (hfirst.trans (by omega)) (hden.trans (by omega))

theorem modEq_depth_le {σ : Type*} {f g k : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep k) {h : ℕ} (hh : 3 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) (ht : t.depth ≤ h) :
    (PowerRepresentation.modEqGraphs r s t).depth ≤ h + 8 := by
  unfold PowerRepresentation.modEqGraphs
  refine (Rep.compose_depth_le (h := h) _ _ (by omega) ?_ ?_).trans (by omega)
  · have hfixed : (ArithmeticRep.modEq (0 : Fin 3) 1 2).depth = 3 := rfl
    rw [hfixed]
    omega
  · intro i
    fin_cases i <;> assumption

/- This metadata lemma unfolds the existing private divisibility wrapper only.
It does not evaluate either of the supplied graph expressions. -/
private theorem dvdGraphs_depth_le {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) {h : ℕ} (hh : 2 ≤ h)
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) :
    (templateDvdGraphs r s).depth ≤ h + 6 := by
  unfoldTemplateDvd
  simp only [Rep.depth_ofIff]
  refine (Rep.compose_depth_le (h := h) _ _ (by omega) ?_ ?_).trans (by omega)
  · have hdvd : (ArithmeticRep.dvd (0 : Fin 2) 1).depth = 2 := rfl
    rw [hdvd]; exact hh
  · intro i
    fin_cases i <;> assumption

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in

theorem finiteRep_depth_le {σ : Type} {m : ℕ}
    (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ) {h : ℕ} (hh : 16384 ≤ h)
    (he : e.graphRep.depth ≤ h) (hf : f.graphRep.depth ≤ h) :
    (BoundedForallRepresentation.finiteRep e f b).depth ≤ 2 * m + h + 96 := by
  let n : GraphRep (fun v : BoundedForallRepresentation.CertificateVar σ m → ℕ =>
      v (BoundedForallRepresentation.parameter b)) :=
    GraphRep.coordinate (BoundedForallRepresentation.parameter b)
  let t := (((e.graphRep.reindex (BoundedForallRepresentation.upperMap b)).add
    (f.graphRep.reindex (BoundedForallRepresentation.upperMap b))).add n).factorial
  let B := BoundedForallRepresentation.productGraph n t
  have hc {τ : Type} (i : τ) : (GraphRep.coordinate i).depth ≤ h := by
    rw [GraphRep.depth_coordinate]; omega
  have hz {τ : Type} (a : ℕ) : (GraphRep.constant (σ := τ) a).depth ≤ h := by
    rw [GraphRep.depth_constant]; omega
  have hn : n.depth ≤ h := hc (BoundedForallRepresentation.parameter b)
  have he' : (e.graphRep.reindex (BoundedForallRepresentation.upperMap b)).depth ≤ h := by
    rw [GraphRep.depth_reindex]; exact he
  have hf' : (f.graphRep.reindex (BoundedForallRepresentation.upperMap b)).depth ≤ h := by
    rw [GraphRep.depth_reindex]; exact hf
  have hsum := GraphRep.depth_add_le _ _ he' hf'
  have hsum' := GraphRep.depth_add_le _ n hsum (hn.trans (by omega))
  have ht : t.depth ≤ h + 18 := (factorial_depth_le _ (by omega) hsum').trans (by omega)
  have hB : B.depth ≤ h + 84 := product_depth_le n t (by omega) (hn.trans (by omega)) ht
  have hindexFirst : ((GraphRep.coordinate BoundedForallRepresentation.index).add
      (GraphRep.constant (σ := BoundedForallRepresentation.CertificateVar σ m) 1)).depth ≤ h + 6 :=
    (GraphRep.depth_add_le _ _
      (hc (BoundedForallRepresentation.index (σ := σ) (m := m)))
      (hz (τ := BoundedForallRepresentation.CertificateVar σ m) 1)).trans (by omega)
  have hindexMul := GraphRep.depth_mul_le _ t (hindexFirst.trans (by omega)) ht
  have hindexAdd := GraphRep.depth_add_le _ (GraphRep.constant 1) hindexMul
    ((hz 1).trans (by omega))
  have hindex := modEq_depth_le _ (GraphRep.constant 0) B (by omega)
    (hindexAdd.trans (by omega)) ((hz 0).trans (by omega)) hB
  have heval := modEq_depth_le (e.graphRep.reindex BoundedForallRepresentation.encodedMap)
    (f.graphRep.reindex BoundedForallRepresentation.encodedMap) B (by omega)
    (by rw [GraphRep.depth_reindex]; exact he.trans (by omega))
    (by rw [GraphRep.depth_reindex]; exact hf.trans (by omega)) hB
  simp only [BoundedForallRepresentation.finiteRep, Rep.depth_ofIff, Rep.depth_conjunction]
  rw [show 2 * m + h + 96 = 2 + (2 * m + h + 94) by omega]
  apply Nat.add_le_add_left
  apply max_le
  · refine (Rep.allFin_depth_le m (h + 90) _ _ ?_).trans (by omega)
    intro i
    let u := (GraphRep.coordinate (BoundedForallRepresentation.upper i)).add
      (GraphRep.constant (σ := BoundedForallRepresentation.CertificateVar σ m) 1)
    let rhs := u.factorial.mul ((GraphRep.coordinate (BoundedForallRepresentation.encoded i)).binomial u)
    have hu : u.depth ≤ h + 6 := (GraphRep.depth_add_le _ _
      (hc (BoundedForallRepresentation.upper (σ := σ) i))
      (hz (τ := BoundedForallRepresentation.CertificateVar σ m) 1)).trans (by omega)
    have huFact := factorial_depth_le u (by omega) hu
    have huBin := binomial_depth_le (GraphRep.coordinate (BoundedForallRepresentation.encoded i))
      u (by omega) ((hc (BoundedForallRepresentation.encoded (σ := σ) i)).trans (by omega)) hu
    have hrhs : rhs.depth ≤ h + 20 :=
      (GraphRep.depth_mul_le _ _ (huFact.trans (by omega)) huBin).trans (by omega)
    exact dvdGraphs_depth_le B rhs (by omega) hB (hrhs.trans (by omega))

  · exact (Nat.add_le_add_left (max_le hindex heval) 2).trans (by omega)

/- One bounded quantifier has a linear depth bound in its input metadata. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem boundedForall_depth_le {σ : Type} {P : (Option σ → ℕ) → Prop}
    (r : Rep (Option σ) P) (b : σ) :
    (r.boundedForall b).depth ≤ 2 * r.witnessCount +
      max 16384 (12 * r.depth + 1) + 96 := by
  have hs := r.expression.splitNatural_depth_le
  have hd : r.expression.depth = r.depth := rfl
  rw [hd] at hs
  have he := NatExpr.graphRep_depth_le r.expression.splitNatural.1
  have hf := NatExpr.graphRep_depth_le r.expression.splitNatural.2
  simp only [Rep.boundedForall, BoundedForallRepresentation.representation,
    BoundedForallRepresentation.certificateRep, Rep.depth_ofIff, Rep.depth_existsBlock]
  apply finiteRep_depth_le _ _ _ (le_max_left _ _)
  · exact he.trans (by change 6 * r.expression.splitNatural.1.depth + 1 ≤ _; omega)
  · exact hf.trans (by change 6 * r.expression.splitNatural.2.depth + 1 ≤ _; omega)

end DiophantineConsistency.BoundedForallDepth

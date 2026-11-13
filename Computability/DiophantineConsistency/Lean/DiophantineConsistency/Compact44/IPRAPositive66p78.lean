import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Compact44.P66p78Graph
import DiophantineConsistency.Compact44.P66Root
import DiophantineConsistency.Compact44.C44Short15ConvData
import DiophantineConsistency.Mixed121.Short15Units
import DiophantineConsistency.Mixed121.Short15Index

/-! # iPRA endpoints for package 66's 15-positive, degree-30 equation

The equation is `66-gap-congruence/algebra/p15_78_degree30.json`: 15 positive
unknowns `J F α z f h i T w Y r η ζ u γ`, 78 operations and exact degree 30, at
the compact44 ports `CompactSymbolicPortProjections.portsInt (paramKernel rho)`
(`C44Short15Facts.intPorts`). Its output is
`A² + paired² + auxiliary² + strong²` (`P66p78Graph`). In every model of `𝗜𝚺₁`
it has a positive zero iff machine 215 halts:

* forward: `A = 0` forces `Y = s·q³` with `s > 0` (`P66Root.first_int`); at the
  valuation `v'` that reads `s` and `w` in slots 8 and 9, the registers are those
  of `Short15Graph` (`P66Vals.link`), `A = q⁶(N0(ℓ + r + s) − 1)`, and
  `paired = 0` is `N1·Nk·Nt = 1`, so `N1 = 1` (`Short15Units.n1_ne_neg`) and
  `Nk = Nt = ±1`. The auxiliary residual is `Na(V, V + u) − 1`, the strong one
  is `S`, and `Short15Index.oracle_gap` with `C44Short15Facts.halts_core` give
  the halt;
* converse: `C44Short15ConvData.canonical` with `i = Δ·i_halt`, `T = T_halt`,
  `Y = s·q³`, `r = τ − (ℓ + s)` and `u = y − w_aux`.

The generic helpers of `IPRAOrdinary12Chain` give native, standard and
equality-only iPRA equivalences with the selected Foundation ZFC consistency
predicate. The endpoints are about the Lean graph; its correspondence with the
JSON and the coefficient binding is the check
`research/fifteen-p66-endpoint/tools/generate_short15_c44.py --check`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.IPRAPositive66p78
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open Short15Graph
open C44Short15Facts (c44 intPorts)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 15) := (P66p78Graph.graph intPorts).output

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pull_first (Q E K r Y : V)
    (h : (ι Q * (ι E + ι r) + ι Y) * (ι Q * (ι E + ι r) + ι Y) -
      (ι Q * ι Q) * (ι E * (ι E + ι K) + 1) = 0) :
    (Q * (E + r) + Y) * (Q * (E + r) + Y) = Q * Q * (E * (E + K) + 1) := by
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination h

/-- A positive zero gives an internal halt of machine 215. -/
theorem halts (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hz : InternalZero expression v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hA, hP, hX, hS⟩ := (P66p78Graph.zero_iff intPorts v).mp hz
  set vv := P66Vals.vals intPorts (ι (v 0)) (fun q => ι (v 8) * q) (fun j => ι (v j)) with hvv
  have evv : P66p78Graph.vv intPorts (fun j => ι (v j)) = vv := rfl
  rw [P66p78Graph.A_eval, evv] at hA
  rw [P66p78Graph.paired_eval, evv] at hP
  rw [P66p78Graph.aux_eval, evv] at hX
  rw [P66p78Graph.strong_eval, evv] at hS
  obtain ⟨cq, -, cq3, -, -, ck, -, -, -, -, -, cell⟩ :=
    P66Root.c_regs c44 v (v 0) (v 8 * ((c44 0 : V) * v 0 + 1)) (ι (v 0)) (fun q => ι (v 8) * q) rfl
      (by simp only [map_mul])
  have hA' := hA
  rw [cq3, cell, ck] at hA'
  have hq0 : 0 < (c44 0 : V) * v 0 + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hQ3 : 0 < (((c44 0 : V) * v 0 + 1) * ((c44 0 : V) * v 0 + 1)) * ((c44 0 : V) * v 0 + 1) :=
    mul_pos (mul_pos hq0 hq0) hq0
  obtain ⟨s, hs0, hYs⟩ := P66Root.first_int _ (v 9) _ (v 10) _ hQ3 (hv 9) (pull_first _ _ _ _ _ hA')
  -- the Short15 valuation
  obtain ⟨v', hv'⟩ : ∃ v' : Fin 15 → V,
      v' = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, s, v 8, v 10, v 11, v 12, v 13, v 14] := ⟨_, rfl⟩
  have e0 : v' 0 = v 0 := by rw [hv']; rfl
  have e1 : v' 1 = v 1 := by rw [hv']; rfl
  have e2 : v' 2 = v 2 := by rw [hv']; rfl
  have e3 : v' 3 = v 3 := by rw [hv']; rfl
  have e4 : v' 4 = v 4 := by rw [hv']; rfl
  have e5 : v' 5 = v 5 := by rw [hv']; rfl
  have e6 : v' 6 = v 6 := by rw [hv']; rfl
  have e7 : v' 7 = v 7 := by rw [hv']; rfl
  have e8 : v' 8 = s := by rw [hv']; rfl
  have e9 : v' 9 = v 8 := by rw [hv']; rfl
  have e11 : v' 11 = v 11 := by rw [hv']; rfl
  have e12 : v' 12 = v 12 := by rw [hv']; rfl
  have e13 : v' 13 = v 13 := by rw [hv']; rfl
  have e14 : v' 14 = v 14 := by rw [hv']; rfl
  have hv'pos : ∀ j, 0 < v' j := by
    intro j
    rw [hv']
    fin_cases j
    exacts [hv 0, hv 1, hv 2, hv 3, hv 4, hv 5, hv 6, hv 7, hs0, hv 8, hv 10, hv 11, hv 12, hv 13, hv 14]
  have hYι : ι (v 9) = ι s * vv.q3 := by rw [cq3, hYs, map_mul]
  obtain ⟨lqm, -, -, -, lE, lk, lc, -, -, lΔ, lell, lRR, lC, lqF, lD, lA, lVn⟩ :=
    P66Vals.link intPorts (ι (v 0)) (fun q => ι (v 8) * q) (fun j => ι (v j)) (fun j => ι (v' j))
      (by show ι (v' 0) = ι (v 0); rw [e0]) (by show ι (v' 1) = ι (v 1); rw [e1])
      (by show ι (v' 2) = ι (v 2); rw [e2]) (by show ι (v' 4) = ι (v 4); rw [e4])
      (by show ι (v' 7) = ι (v 7); rw [e7]) (by show ι (v' 11) = ι (v 11); rw [e11])
      (by show ι (v' 12) = ι (v 12); rw [e12]) (by show ι (v 8) * vv.q = ι (v' 9) * vv.q; rw [e9])
      (by show ι (v 9) = ι (v' 8) * vv.q3; rw [e8]; exact hYι)
  have lD' : (vals intPorts (fun j => ι (v' j))).D = vv.X + vv.a * vv.c + ι (v 14) * vv.H := by
    rw [lD]; show vv.X + vv.a * vv.c + ι (v' 14) * vv.H = _; rw [e14]
  have lVn' : (vals intPorts (fun j => ι (v' j))).Vn = P66Vals.ordV vv (ι (v 4)) (ι (v 7)) vv.RR := lVn
  -- the residuals at v'
  have hN1e : vv.D0 * vv.D0 - vv.Delta * (vv.c * vv.c) = rN1 intPorts (fun j => ι (v' j)) := by
    rw [rN1, lD', lΔ, lc, show vv.D0 = vv.a * vv.c + (vv.X + ι (v 14) * vv.H) from rfl]; ring
  have hNke : (vv.k - ι (v 5) * vv.E) - vv.RR = rNk intPorts (fun j => ι (v' j)) := by
    rw [rNk, lk, lE, lRR]; show _ = (vv.k - ι (v' 5) * vv.E) - vv.RR; rw [e5]
  have hNte : (((intPorts 1 : ℤ) : DiffRing V) + ι (v 8)) * vv.C + vv.qF - ι (v 3) * vv.qm =
      rNt intPorts (fun j => ι (v' j)) := by
    rw [rNt, lC, lqF, lqm]
    show _ = (((intPorts 1 : ℤ) : DiffRing V) + ι (v' 9)) * vv.C + vv.qF - ι (v' 3) * vv.qm
    rw [e9, e3]
  rw [hN1e, hNke, hNte] at hP
  have hm : rN1 intPorts (fun j => ι (v' j)) *
      (rNk intPorts (fun j => ι (v' j)) * rNt intPorts (fun j => ι (v' j))) = 1 := by
    rw [← mul_assoc]; exact sub_eq_zero.mp hP
  have hN1 := (Short15Units.unit_pm (Or.inl hm)).1.resolve_right (Short15Units.n1_ne_neg _ _)
  rw [hN1, one_mul] at hm
  have hsign := Short15Units.sign_of_mul hm
  -- the first norm at τ = ℓ + r + s
  have hq3ne : vv.q3 ≠ 0 := by rw [cq3]; exact ne_of_gt (Short15Root.ι_pos' hQ3)
  rw [hYι] at hA
  have key : vv.q3 * vv.q3 *
      (((vv.ell + ι (v 10) + ι s) * (vv.ell + ι (v 10) + ι s) - vv.ell * (vv.ell + vv.k)) - 1) = 0 := by
    linear_combination hA
  have hn0 := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (mul_ne_zero hq3ne hq3ne))
  let τ : V := Short15Root.ellV c44 v' + v 10 + s
  have hιτ : ι τ = vv.ell + ι (v 10) + ι s := by
    show ι (Short15Root.ellV c44 v' + v 10 + s) = _
    rw [map_add, map_add, ← Short15Root.c_ell, lell]
  have hN0 : rN0 intPorts (fun j => ι (v' j)) (ι τ) = 1 := by
    rw [rN0, lell, lk, hιτ]; exact hn0
  have hτ := Short15Root.first c44 v' τ hN0
  -- the strong and auxiliary norms at v'
  have hSe : rS intPorts (fun j => ι (v' j)) (ι (v' 6)) = 0 := by
    rw [rS, lc, lA, e6]; exact hS
  have hstrong := Short15Root.strong c44 v' (v' 6) hSe
  rw [P66Vals.rAux_eq] at hX
  have hNa : rNa (vals intPorts (fun j => ι (v' j))).Aaux (vals intPorts (fun j => ι (v' j))).Vn
      ((vals intPorts (fun j => ι (v' j))).Vn + ι (v' 13)) = 1 := by
    rw [lA, lVn', e13]; linear_combination hX
  have hc0 : 0 < Short15Root.cV c44 v' := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv'pos 11)
  exact C44Short15Facts.halts_core v' hv'pos τ hτ hN1
    (fun hF hR => Short15Index.oracle_gap _ _ _ (v' 4) (v' 6) (v' 7) (v' 13) hc0 (hv'pos 6) (hv'pos 4) hR
      hstrong (Short15Root.aux_gap c44 v' hF (hv'pos 4) hNa)) hsign

/-- An internal halt of machine 215 gives a positive zero. -/
theorem converse (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 15 → V, (∀ j, 0 < v j) ∧ InternalZero expression v := by
  obtain ⟨J, F, α, z, f, h, iH, TH, s, w, τ, η, ζ, y, wa, γ, ellM, ΔM, hJ, hF, hα, hz, hf, hh, hiH,
    hTH, hs, hw, hτ, hη, hζ, hy, hwy, hγ, hΔ, -, hτs, -, -, -, hfacts⟩ := C44Short15ConvData.canonical T hT
  have hq0 : 0 < (c44 0 : V) * J + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hQ3 : 0 < (((c44 0 : V) * J + 1) * ((c44 0 : V) * J + 1)) * ((c44 0 : V) * J + 1) :=
    mul_pos (mul_pos hq0 hq0) hq0
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 15 → V, v = ![J, F, α, z, f, h, ΔM * iH, TH, w,
      s * ((((c44 0 : V) * J + 1) * ((c44 0 : V) * J + 1)) * ((c44 0 : V) * J + 1)), τ - (ellM + s),
      η, ζ, y - wa, γ] := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v' : Fin 15 → V,
      v' = ![J, F, α, z, f, h, ΔM * iH, TH, s, w, τ, η, ζ, y - wa, γ] := ⟨_, rfl⟩
  have hpos : ∀ j, 0 < v j := by
    intro j
    rw [hvdef]
    fin_cases j
    exacts [hJ, hF, hα, hz, hf, hh, mul_pos hΔ hiH, hTH, hw, mul_pos hs hQ3, tsub_pos_of_lt hτs, hη, hζ,
      tsub_pos_of_lt hwy, hγ]
  refine ⟨v, hpos, ?_⟩
  have d0 : v 0 = J := by rw [hvdef]; rfl
  have d4 : v 4 = f := by rw [hvdef]; rfl
  have d6 : v 6 = ΔM * iH := by rw [hvdef]; rfl
  have d8 : v 8 = w := by rw [hvdef]; rfl
  have d9 : v 9 = s * ((((c44 0 : V) * J + 1) * ((c44 0 : V) * J + 1)) * ((c44 0 : V) * J + 1)) := by
    rw [hvdef]; rfl
  have d10 : v 10 = τ - (ellM + s) := by rw [hvdef]; rfl
  have d13 : v 13 = y - wa := by rw [hvdef]; rfl
  have e0 : ι (v' 0) = ι (v 0) := by
    rw [show v' 0 = J by rw [hv']; rfl, show v 0 = J by rw [hvdef]; rfl]
  have e1 : ι (v' 1) = ι (v 1) := by
    rw [show v' 1 = F by rw [hv']; rfl, show v 1 = F by rw [hvdef]; rfl]
  have e2 : ι (v' 2) = ι (v 2) := by
    rw [show v' 2 = α by rw [hv']; rfl, show v 2 = α by rw [hvdef]; rfl]
  have e3 : ι (v' 3) = ι (v 3) := by
    rw [show v' 3 = z by rw [hv']; rfl, show v 3 = z by rw [hvdef]; rfl]
  have e4 : ι (v' 4) = ι (v 4) := by
    rw [show v' 4 = f by rw [hv']; rfl, show v 4 = f by rw [hvdef]; rfl]
  have e5 : ι (v' 5) = ι (v 5) := by
    rw [show v' 5 = h by rw [hv']; rfl, show v 5 = h by rw [hvdef]; rfl]
  have e6 : ι (v' 6) = ι (v 6) := by
    rw [show v' 6 = ΔM * iH by rw [hv']; rfl, show v 6 = ΔM * iH by rw [hvdef]; rfl]
  have e7 : ι (v' 7) = ι (v 7) := by
    rw [show v' 7 = TH by rw [hv']; rfl, show v 7 = TH by rw [hvdef]; rfl]
  have e9 : ι (v' 9) = ι (v 8) := by
    rw [show v' 9 = w by rw [hv']; rfl, show v 8 = w by rw [hvdef]; rfl]
  have e11 : ι (v' 11) = ι (v 11) := by
    rw [show v' 11 = η by rw [hv']; rfl, show v 11 = η by rw [hvdef]; rfl]
  have e12 : ι (v' 12) = ι (v 12) := by
    rw [show v' 12 = ζ by rw [hv']; rfl, show v 12 = ζ by rw [hvdef]; rfl]
  have e14 : ι (v' 14) = ι (v 14) := by
    rw [show v' 14 = γ by rw [hv']; rfl, show v 14 = γ by rw [hvdef]; rfl]
  obtain ⟨vell, vΔ, hNt, hNk, hN1, hN0, hnorm, hVn, hNa⟩ := hfacts (fun j => ι (v' j))
    (by show ι (v' 0) = _; rw [hv']; rfl) (by show ι (v' 1) = _; rw [hv']; rfl)
    (by show ι (v' 2) = _; rw [hv']; rfl) (by show ι (v' 3) = _; rw [hv']; rfl)
    (by show ι (v' 4) = _; rw [hv']; rfl) (by show ι (v' 5) = _; rw [hv']; rfl)
    (by show ι (v' 8) = _; rw [hv']; rfl) (by show ι (v' 9) = _; rw [hv']; rfl)
    (by show ι (v' 11) = _; rw [hv']; rfl) (by show ι (v' 12) = _; rw [hv']; rfl)
    (by show ι (v' 14) = _; rw [hv']; rfl)
  have e7' : ι (v' 7) = ι TH := by rw [hv']; rfl
  have e4' : ι (v' 4) = ι f := by rw [hv']; rfl
  set vv := P66Vals.vals intPorts (ι (v 0)) (fun q => ι (v 8) * q) (fun j => ι (v j)) with hvv
  have evv : P66p78Graph.vv intPorts (fun j => ι (v j)) = vv := rfl
  obtain ⟨-, -, cq3, -, -, -, -, -, -, -, -, -⟩ :=
    P66Root.c_regs c44 v (v 0) (v 8 * ((c44 0 : V) * v 0 + 1)) (ι (v 0)) (fun q => ι (v 8) * q) rfl
      (by simp only [map_mul])
  have hYι : ι (v 9) = ι s * vv.q3 := by rw [cq3, d9, d0, map_mul]
  obtain ⟨lqm, -, -, -, lE, lk, lc, -, -, lΔ, lell, lRR, lC, lqF, lD, lA, lVn⟩ :=
    P66Vals.link intPorts (ι (v 0)) (fun q => ι (v 8) * q) (fun j => ι (v j)) (fun j => ι (v' j))
      e0 e1 e2 e4 e7 e11 e12 (by show ι (v 8) * vv.q = ι (v' 9) * vv.q; rw [e9])
      (by show ι (v 9) = ι (v' 8) * vv.q3; rw [hv']; exact hYι)
  have lD' : (vals intPorts (fun j => ι (v' j))).D = vv.X + vv.a * vv.c + ι (v 14) * vv.H := by
    rw [lD]; show vv.X + vv.a * vv.c + ι (v' 14) * vv.H = _; rw [e14]
  have lVn' : (vals intPorts (fun j => ι (v' j))).Vn = P66Vals.ordV vv (ι (v 4)) (ι (v 7)) vv.RR := lVn
  have hN1e : vv.D0 * vv.D0 - vv.Delta * (vv.c * vv.c) = rN1 intPorts (fun j => ι (v' j)) := by
    rw [rN1, lD', lΔ, lc, show vv.D0 = vv.a * vv.c + (vv.X + ι (v 14) * vv.H) from rfl]; ring
  have hNke : (vv.k - ι (v 5) * vv.E) - vv.RR = rNk intPorts (fun j => ι (v' j)) := by
    rw [rNk, lk, lE, lRR]; show _ = (vv.k - ι (v' 5) * vv.E) - vv.RR; rw [e5]
  have hNte : (((intPorts 1 : ℤ) : DiffRing V) + ι (v 8)) * vv.C + vv.qF - ι (v 3) * vv.qm =
      rNt intPorts (fun j => ι (v' j)) := by
    rw [rNt, lC, lqF, lqm]
    show _ = (((intPorts 1 : ℤ) : DiffRing V) + ι (v' 9)) * vv.C + vv.qF - ι (v' 3) * vv.qm
    rw [e9, e3]
  have hlv : vv.ell = ι ellM := by rw [← lell]; exact vell
  rw [rN0, lell, lk] at hN0
  have hVnw : P66Vals.ordV vv (ι (v 4)) (ι (v 7)) vv.RR = ι wa := by
    rw [← lVn']
    show ι (v' 4) * ι (v' 4) * ((vals intPorts (fun j => ι (v' j))).c * ι (v' 7) -
      (vals intPorts (fun j => ι (v' j))).RR) - (vals intPorts (fun j => ι (v' j))).c = ι wa
    rw [e7']; exact hVn
  rw [lA] at hNa
  rw [expression, P66p78Graph.zero_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P66p78Graph.A_eval, evv, hYι, d10, P72Root.ι_tsub (le_of_lt hτs), map_add, ← hlv]
    linear_combination (vv.q3 * vv.q3) * hN0
  · rw [P66p78Graph.paired_eval, evv, hN1e, hNke, hNte, hN1, hNk, hNt]; ring
  · rw [P66p78Graph.aux_eval, evv, P66Vals.rAux_eq, hVnw, d13, P72Root.ι_tsub (le_of_lt hwy)]
    rw [show ι wa + (ι y - ι wa) = ι y by ring]
    linear_combination hNa
  · rw [P66p78Graph.strong_eval, evv, d6, map_mul,
      show vv.U = vv.Delta * (ι (v 4) * ι (v 4) - 1) from rfl, ← lΔ, ← lc, vΔ, d4]
    try dsimp only at hnorm
    rw [vΔ, e4'] at hnorm
    linear_combination (-(ι ΔM)) * hnorm

end Model

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => halts v hv hz, fun ⟨T, hT⟩ => converse T hT⟩

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

#print axioms halts
#print axioms converse
#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAPositive66p78

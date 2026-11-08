import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Compact44.P66p88Graph
import DiophantineConsistency.Compact44.IPRAPositive66p87

/-! # iPRA endpoints for package 66's 15-positive, degree-24 equation

The equation is `66-gap-congruence/algebra/p15_88_degree24.json`: 15 positive
unknowns `j F α z f h i T X Y r η ζ u γ`, 88 operations and exact degree 24, at
the compact44 ports `CompactSymbolicPortProjections.portsInt (paramKernel rho)`.
Its output is `A² + B² + index_res² + transport_res² + auxiliary² + strong²`
(`P66p88Graph`), with `J = 3j + 1` and the shifted transport variable
`z = z_old − 1`. In every model of `𝗜𝚺₁` it has a positive zero iff machine 215
halts:

* forward: as for `IPRAPositive66p87`, `A = 0` and `B = 0` give `Y = s·q³` and
  `X = w·q`. At the valuation `v'` reading `z + 1`, `s`, `w` and `γ + w`,
  `index_res = Nk − 1` and `transport_res = q(Nt − 1)`, so `Nk = Nt = 1`, and
  `R̂ = R`, so the auxiliary ordinate is the squared-modulus one;
* converse: `C44Short15ConvData.canonical` with `j`, `z₀` (`z = z₀ + 1`),
  `X = q·w`, `Y = s·q³`, `r = τ − (ℓ + s)`, `u = y − w_aux` and `γ − w`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.IPRAPositive66p88
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly ModelDifferenceRing ArithmeticGcdNormalization
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open Short15Graph
open C44Short15Facts (c44 intPorts)
open IPRAPositive66p78 (pull_first)
open IPRAPositive66p87 (pull_second bez_H)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 15) := (P66p88Graph.graph intPorts).output

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive zero gives an internal halt of machine 215. -/
theorem halts (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hz : InternalZero expression v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hA, hB, hI, hT, hX, hS⟩ := (P66p88Graph.zero_iff intPorts v).mp hz
  set vv := P66Vals.vals intPorts (3 * ι (v 0) + 1) (fun _ => ι (v 8)) (fun j => ι (v j)) with hvv
  have evv : P66p88Graph.vv intPorts (fun j => ι (v j)) = vv := rfl
  rw [P66p88Graph.A_eval, evv] at hA
  rw [P66p88Graph.B_eval, evv] at hB
  rw [P66p88Graph.index_eval, evv] at hI
  rw [P66p88Graph.transport_eval, evv] at hT
  rw [P66p88Graph.aux_eval, evv] at hX
  rw [P66p88Graph.strong_eval, evv] at hS
  obtain ⟨cq, cq2, cq3, cX, -, ck, cc, -, cH, cΔ, cD0, cell⟩ :=
    P66Root.c_regs c44 v (3 * v 0 + 1) (v 8) (3 * ι (v 0) + 1) (fun _ => ι (v 8))
      (by simp only [map_add, map_mul, map_ofNat, map_one]) rfl
  have hq0 : 0 < (c44 0 : V) * (3 * v 0 + 1) + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hQ3 : 0 < (((c44 0 : V) * (3 * v 0 + 1) + 1) * ((c44 0 : V) * (3 * v 0 + 1) + 1)) *
      ((c44 0 : V) * (3 * v 0 + 1) + 1) := mul_pos (mul_pos hq0 hq0) hq0
  have hA' := hA
  rw [cq3, cell, ck] at hA'
  obtain ⟨s, hs0, hYs⟩ := P66Root.first_int _ (v 9) _ (v 10) _ hQ3 (hv 9) (pull_first _ _ _ _ _ hA')
  -- X = w·q
  have hB' := hB
  rw [cq, cD0, cX, cH, cq2, cΔ, cc] at hB'
  have hBm := pull_second _ _ _ _ _ _ hB'
  rw [hYs] at hBm
  obtain ⟨wq, hwq⟩ := P66Root.second_int _ _ _ _ _ hq0 (bez_H (v 0) (v 8) s) hBm
  have hwq0 : 0 < wq := by
    rcases (Arithmetic.zero_le wq).lt_or_eq with h0 | h0
    · exact h0
    · exfalso; rw [← h0, mul_zero] at hwq; exact absurd hwq (ne_of_gt (hv 8))
  have hXq : vv.X = ι wq * vv.q := by rw [cX, cq, hwq, map_mul]; ring
  -- the Short15 valuation
  obtain ⟨v', hv'⟩ : ∃ v' : Fin 15 → V,
      v' = ![3 * v 0 + 1, v 1, v 2, v 3 + 1, v 4, v 5, v 6, v 7, s, wq, v 10, v 11, v 12, v 13, v 14 + wq] :=
    ⟨_, rfl⟩
  have e0 : v' 0 = 3 * v 0 + 1 := by rw [hv']; rfl
  have e1 : v' 1 = v 1 := by rw [hv']; rfl
  have e2 : v' 2 = v 2 := by rw [hv']; rfl
  have e3 : v' 3 = v 3 + 1 := by rw [hv']; rfl
  have e4 : v' 4 = v 4 := by rw [hv']; rfl
  have e5 : v' 5 = v 5 := by rw [hv']; rfl
  have e6 : v' 6 = v 6 := by rw [hv']; rfl
  have e7 : v' 7 = v 7 := by rw [hv']; rfl
  have e8 : v' 8 = s := by rw [hv']; rfl
  have e9 : v' 9 = wq := by rw [hv']; rfl
  have e11 : v' 11 = v 11 := by rw [hv']; rfl
  have e12 : v' 12 = v 12 := by rw [hv']; rfl
  have e13 : v' 13 = v 13 := by rw [hv']; rfl
  have e14 : v' 14 = v 14 + wq := by rw [hv']; rfl
  have hv'pos : ∀ j, 0 < v' j := by
    intro j
    rw [hv']
    fin_cases j
    exacts [add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) _root_.zero_lt_one, hv 1, hv 2, add_pos (hv 3) _root_.zero_lt_one, hv 4, hv 5,
      hv 6, hv 7, hs0, hwq0, hv 10, hv 11, hv 12, hv 13, add_pos (hv 14) hwq0]
  have hYι : ι (v 9) = ι s * vv.q3 := by rw [cq3, hYs, map_mul]
  obtain ⟨lqm, -, -, -, lE, lk, lc, -, -, lΔ, lell, lRR, lC, lqF, lD, lA, lVn⟩ :=
    P66Vals.link intPorts (3 * ι (v 0) + 1) (fun _ => ι (v 8)) (fun j => ι (v j)) (fun j => ι (v' j))
      (by show ι (v' 0) = _; rw [e0]; simp only [map_add, map_mul, map_ofNat, map_one])
      (by show ι (v' 1) = ι (v 1); rw [e1])
      (by show ι (v' 2) = ι (v 2); rw [e2]) (by show ι (v' 4) = ι (v 4); rw [e4])
      (by show ι (v' 7) = ι (v 7); rw [e7]) (by show ι (v' 11) = ι (v 11); rw [e11])
      (by show ι (v' 12) = ι (v 12); rw [e12]) (by show ι (v 8) = ι (v' 9) * vv.q; rw [e9]; exact hXq)
      (by show ι (v 9) = ι (v' 8) * vv.q3; rw [e8]; exact hYι)
  have lD' : (vals intPorts (fun j => ι (v' j))).D = vv.X + vv.a * vv.c + (ι (v 14) + ι wq) * vv.H := by
    rw [lD]; show vv.X + vv.a * vv.c + ι (v' 14) * vv.H = _; rw [e14, map_add]
  have lVn' : (vals intPorts (fun j => ι (v' j))).Vn = P66Vals.ordV vv (ι (v 4)) (ι (v 7)) vv.RR := lVn
  have hNke : (vv.k - ι (v 5) * vv.E) - vv.RR = rNk intPorts (fun j => ι (v' j)) := by
    rw [rNk, lk, lE, lRR]; show _ = (vv.k - ι (v' 5) * vv.E) - vv.RR; rw [e5]
  have hNte : (((intPorts 1 : ℤ) : DiffRing V) + ι wq) * vv.C + vv.qF - (ι (v 3) + 1) * vv.qm =
      rNt intPorts (fun j => ι (v' j)) := by
    rw [rNt, lC, lqF, lqm]
    show _ = (((intPorts 1 : ℤ) : DiffRing V) + ι (v' 9)) * vv.C + vv.qF - ι (v' 3) * vv.qm
    rw [e9, e3, map_add, map_one]
  have hqne : vv.q ≠ 0 := by rw [cq]; exact ne_of_gt (Short15Root.ι_pos' hq0)
  -- the main norm
  rw [show vv.D0 = vv.a * vv.c + (vv.X + ι (v 14) * vv.H) from rfl,
    show vv.q2 = vv.q * vv.q from rfl] at hB
  have key1 : vv.q * vv.q * (rN1 intPorts (fun j => ι (v' j)) - 1) = 0 := by
    rw [rN1, lD', lΔ, lc]
    linear_combination hB - vv.H * (2 * vv.q * (vv.a * vv.c + (vv.X + ι (v 14) * vv.H)) +
      vv.X * vv.H + ι wq * vv.q * vv.H) * hXq
  have hN1 := sub_eq_zero.mp ((mul_eq_zero.mp key1).resolve_left (mul_ne_zero hqne hqne))
  -- the index and the shifted transport
  have hNk : rNk intPorts (fun j => ι (v' j)) = 1 := by rw [← hNke]; linear_combination hI
  have hq1 : vv.q = vv.qm + 1 := rfl
  have hqF : vv.qF = vv.q - ι (v 1) := rfl
  have key2 : vv.q * (rNt intPorts (fun j => ι (v' j)) - 1) = 0 := by
    rw [← hNte]
    linear_combination hT - vv.C * hXq + vv.q * hqF + vv.q * hq1
  have hNt := sub_eq_zero.mp ((mul_eq_zero.mp key2).resolve_left hqne)
  have hsign : (rNk intPorts (fun j => ι (v' j)) = 1 ∧ rNt intPorts (fun j => ι (v' j)) = 1) ∨
      (rNk intPorts (fun j => ι (v' j)) = -1 ∧ rNt intPorts (fun j => ι (v' j)) = -1) :=
    Or.inl ⟨hNk, hNt⟩
  have hRh : (vv.k - ι (v 5) * vv.E) - 1 = vv.RR := by linear_combination hI
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
  rw [hRh, P66Vals.rAux_eq] at hX
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
  obtain ⟨J, F, α, z, f, h, iH, TH, s, w, τ, η, ζ, y, wa, γ, ellM, ΔM, -, hF, hα, hz, hf, hh, hiH,
    hTH, hs, hw, hτ, hη, hζ, hy, hwy, hγ, hΔ, -, hτs, hwγ, hj3, hz1, hfacts⟩ :=
    C44Short15ConvData.canonical T hT
  obtain ⟨j, hj0, rfl⟩ := hj3
  obtain ⟨z0, hz0, rfl⟩ := hz1
  have hq0 : 0 < (c44 0 : V) * (3 * j + 1) + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hQ3 : 0 < (((c44 0 : V) * (3 * j + 1) + 1) * ((c44 0 : V) * (3 * j + 1) + 1)) *
      ((c44 0 : V) * (3 * j + 1) + 1) := mul_pos (mul_pos hq0 hq0) hq0
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 15 → V, v = ![j, F, α, z0, f, h, ΔM * iH, TH,
      ((c44 0 : V) * (3 * j + 1) + 1) * w,
      s * ((((c44 0 : V) * (3 * j + 1) + 1) * ((c44 0 : V) * (3 * j + 1) + 1)) *
        ((c44 0 : V) * (3 * j + 1) + 1)), τ - (ellM + s), η, ζ, y - wa, γ - w] := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v' : Fin 15 → V,
      v' = ![3 * j + 1, F, α, z0 + 1, f, h, ΔM * iH, TH, s, w, τ, η, ζ, y - wa, γ] := ⟨_, rfl⟩
  have hpos : ∀ j, 0 < v j := by
    intro j'
    rw [hvdef]
    fin_cases j'
    exacts [hj0, hF, hα, hz0, hf, hh, mul_pos hΔ hiH, hTH, mul_pos hq0 hw, mul_pos hs hQ3,
      tsub_pos_of_lt hτs, hη, hζ, tsub_pos_of_lt hwy, tsub_pos_of_lt hwγ]
  refine ⟨v, hpos, ?_⟩
  have d0 : v 0 = j := by rw [hvdef]; rfl
  have d4 : v 4 = f := by rw [hvdef]; rfl
  have d6 : v 6 = ΔM * iH := by rw [hvdef]; rfl
  have d8 : v 8 = ((c44 0 : V) * (3 * j + 1) + 1) * w := by rw [hvdef]; rfl
  have d9 : v 9 = s * ((((c44 0 : V) * (3 * j + 1) + 1) * ((c44 0 : V) * (3 * j + 1) + 1)) *
      ((c44 0 : V) * (3 * j + 1) + 1)) := by rw [hvdef]; rfl
  have d10 : v 10 = τ - (ellM + s) := by rw [hvdef]; rfl
  have d13 : v 13 = y - wa := by rw [hvdef]; rfl
  have d14 : v 14 = γ - w := by rw [hvdef]; rfl
  have e0 : ι (v' 0) = 3 * ι (v 0) + 1 := by
    rw [hv', hvdef]; show ι (3 * j + 1) = 3 * ι j + 1; simp only [map_add, map_mul, map_ofNat, map_one]
  have e1 : ι (v' 1) = ι (v 1) := by
    rw [show v' 1 = F by rw [hv']; rfl, show v 1 = F by rw [hvdef]; rfl]
  have e2 : ι (v' 2) = ι (v 2) := by
    rw [show v' 2 = α by rw [hv']; rfl, show v 2 = α by rw [hvdef]; rfl]
  have e3 : ι (v' 3) = ι (v 3) + 1 := by
    rw [hv', hvdef]; show ι (z0 + 1) = ι z0 + 1; rw [map_add, map_one]
  have e4 : ι (v' 4) = ι (v 4) := by
    rw [show v' 4 = f by rw [hv']; rfl, show v 4 = f by rw [hvdef]; rfl]
  have e5 : ι (v' 5) = ι (v 5) := by
    rw [show v' 5 = h by rw [hv']; rfl, show v 5 = h by rw [hvdef]; rfl]
  have e7 : ι (v' 7) = ι (v 7) := by
    rw [show v' 7 = TH by rw [hv']; rfl, show v 7 = TH by rw [hvdef]; rfl]
  have e11 : ι (v' 11) = ι (v 11) := by
    rw [show v' 11 = η by rw [hv']; rfl, show v 11 = η by rw [hvdef]; rfl]
  have e12 : ι (v' 12) = ι (v 12) := by
    rw [show v' 12 = ζ by rw [hv']; rfl, show v 12 = ζ by rw [hvdef]; rfl]
  have e9' : ι (v' 9) = ι w := by rw [hv']; rfl
  have e14' : ι (v' 14) = ι γ := by rw [hv']; rfl
  obtain ⟨vell, vΔ, hNt, hNk, hN1, hN0, hnorm, hVn, hNa⟩ := hfacts (fun j => ι (v' j))
    (by show ι (v' 0) = _; rw [hv']; rfl) (by show ι (v' 1) = _; rw [hv']; rfl)
    (by show ι (v' 2) = _; rw [hv']; rfl) (by show ι (v' 3) = _; rw [hv']; rfl)
    (by show ι (v' 4) = _; rw [hv']; rfl) (by show ι (v' 5) = _; rw [hv']; rfl)
    (by show ι (v' 8) = _; rw [hv']; rfl) (by show ι (v' 9) = _; rw [hv']; rfl)
    (by show ι (v' 11) = _; rw [hv']; rfl) (by show ι (v' 12) = _; rw [hv']; rfl)
    (by show ι (v' 14) = _; rw [hv']; rfl)
  have e7' : ι (v' 7) = ι TH := by rw [hv']; rfl
  have e4' : ι (v' 4) = ι f := by rw [hv']; rfl
  set vv := P66Vals.vals intPorts (3 * ι (v 0) + 1) (fun _ => ι (v 8)) (fun j => ι (v j)) with hvv
  have evv : P66p88Graph.vv intPorts (fun j => ι (v j)) = vv := rfl
  obtain ⟨cq, -, cq3, cX, -, -, -, -, -, -, -, -⟩ :=
    P66Root.c_regs c44 v (3 * v 0 + 1) (v 8) (3 * ι (v 0) + 1) (fun _ => ι (v 8))
      (by simp only [map_add, map_mul, map_ofNat, map_one]) rfl
  have hYι : ι (v 9) = ι s * vv.q3 := by rw [cq3, d9, d0, map_mul]
  have hXq : vv.X = ι w * vv.q := by rw [cX, cq, d8, d0, map_mul]; ring
  obtain ⟨lqm, -, -, -, lE, lk, lc, -, -, lΔ, lell, lRR, lC, lqF, lD, lA, lVn⟩ :=
    P66Vals.link intPorts (3 * ι (v 0) + 1) (fun _ => ι (v 8)) (fun j => ι (v j)) (fun j => ι (v' j))
      e0 e1 e2 e4 e7 e11 e12 (by show ι (v 8) = ι (v' 9) * vv.q; rw [e9']; exact hXq)
      (by show ι (v 9) = ι (v' 8) * vv.q3; rw [hv']; exact hYι)
  have lD' : (vals intPorts (fun j => ι (v' j))).D = vv.X + vv.a * vv.c + ι γ * vv.H := by
    rw [lD]; show vv.X + vv.a * vv.c + ι (v' 14) * vv.H = _; rw [e14']
  have lVn' : (vals intPorts (fun j => ι (v' j))).Vn = P66Vals.ordV vv (ι (v 4)) (ι (v 7)) vv.RR := lVn
  have hNke : (vv.k - ι (v 5) * vv.E) - vv.RR = rNk intPorts (fun j => ι (v' j)) := by
    rw [rNk, lk, lE, lRR]; show _ = (vv.k - ι (v' 5) * vv.E) - vv.RR; rw [e5]
  have hNte : (((intPorts 1 : ℤ) : DiffRing V) + ι w) * vv.C + vv.qF - (ι (v 3) + 1) * vv.qm =
      rNt intPorts (fun j => ι (v' j)) := by
    rw [rNt, lC, lqF, lqm]
    show _ = (((intPorts 1 : ℤ) : DiffRing V) + ι (v' 9)) * vv.C + vv.qF - ι (v' 3) * vv.qm
    rw [e9', e3]
  have hlv : vv.ell = ι ellM := by rw [← lell]; exact vell
  rw [rN0, lell, lk] at hN0
  rw [rN1, lD', lΔ, lc] at hN1
  rw [← hNke] at hNk
  rw [← hNte] at hNt
  have hVnw : P66Vals.ordV vv (ι (v 4)) (ι (v 7)) vv.RR = ι wa := by
    rw [← lVn']
    show ι (v' 4) * ι (v' 4) * ((vals intPorts (fun j => ι (v' j))).c * ι (v' 7) -
      (vals intPorts (fun j => ι (v' j))).RR) - (vals intPorts (fun j => ι (v' j))).c = ι wa
    rw [e7']; exact hVn
  rw [lA] at hNa
  have hγι : ι (v 14) = ι γ - ι w := by rw [d14, P72Root.ι_tsub (le_of_lt hwγ)]
  rw [expression, P66p88Graph.zero_iff]
  have hq1 : vv.q = vv.qm + 1 := rfl
  have hqF : vv.qF = vv.q - ι (v 1) := rfl
  have hRh : (vv.k - ι (v 5) * vv.E) - 1 = vv.RR := by linear_combination hNk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P66p88Graph.A_eval, evv, hYι, d10, P72Root.ι_tsub (le_of_lt hτs), map_add, ← hlv]
    linear_combination (vv.q3 * vv.q3) * hN0
  · rw [P66p88Graph.B_eval, evv, show vv.D0 = vv.a * vv.c + (vv.X + ι (v 14) * vv.H) from rfl,
      show vv.q2 = vv.q * vv.q from rfl, hγι]
    linear_combination (vv.q * vv.q) * hN1 + vv.H * (2 * (vv.q * (vv.X + vv.a * vv.c + ι γ * vv.H)) +
      vv.H * (vv.X - ι w * vv.q)) * hXq
  · rw [P66p88Graph.index_eval, evv]
    linear_combination hNk
  · rw [P66p88Graph.transport_eval, evv]
    linear_combination vv.q * hNt + vv.C * hXq - vv.q * hqF - vv.q * hq1
  · rw [P66p88Graph.aux_eval, evv, hRh, P66Vals.rAux_eq, hVnw, d13, P72Root.ι_tsub (le_of_lt hwy)]
    rw [show ι wa + (ι y - ι wa) = ι y by ring]
    linear_combination hNa
  · rw [P66p88Graph.strong_eval, evv, d6, map_mul,
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

end DiophantineConsistency.IPRAPositive66p88

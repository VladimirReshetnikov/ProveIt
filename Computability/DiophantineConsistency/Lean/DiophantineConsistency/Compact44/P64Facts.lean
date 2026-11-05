import DiophantineConsistency.Compact44.P64Norm
import DiophantineConsistency.Compact44.P64Early
import DiophantineConsistency.Compact44.P72Facts

/-! # A positive zero of package 64's degree-30 equation gives the six leaf facts

`P64Norm.residuals` reduces a zero to `A0 = M = W = Lt = 0` and `Na = 1`, and
`P64Root` reads each in the model. The generic sections then apply:

* `P72Window.window_ring`;
* `P64Early.early`, for the modulus `U = Y²`;
* `P72Exact.indices_ordinary`, for the ordinary strong norm;
* `P72Power.power_of_mod`. Here `q ∣ X` is immediate from `X = wq`, and
  `g ≡ X + ac (mod H)` follows by cancelling `U` in the carrier once
  `2n = R + 1`.

A positive zero at symbolic compact44 ports thus gives
`CompactLeafFacts.LeafFacts` at `![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, and
`CompactLeafFactsHalt.halts_of_facts` gives an internal halt of machine 215. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P64Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactLeafFacts
open P64Graph P64Root P72Mu
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts_ports (B K L H : ℕ) (hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))
    (hL : L = lowNat) (hH : H = highNat)
    (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (ports B K L H j : ℤ))).output v) :
    ∃ X : V, 0 < X ∧
      LeafFacts (ports B K L H) ![v 0, v 1, v 2, 1, 1, X, v 7, 1, v 10, v 11, 1, 1] := by
  set p : Fin 4 → ℕ := ports B K L H with hpdef
  obtain ⟨hA0, hM, hW, hNa, hLt⟩ := P64Norm.residuals p v hv hz
  have hb : 0 < (p 0 : V) := by
    obtain ⟨h, _⟩ := CompactMaskBoundFinish.bounds (B : V) 1 hB (by simp)
    change 0 < (B : V); exact h
  obtain ⟨hFα, htr⟩ := transport p v hv hLt
  obtain ⟨hY, τ, hτ⟩ := first_root p v hA0
  have hF : v 1 ≤ (p 0 : V) * v 0 + 1 := le_trans le_self_add (le_of_lt hFα)
  obtain ⟨g, hgg, hcar⟩ := main_root p v hv hb hF hY hM
  have haux := aux_norm p v hF (hv 4) hNa
  have hstrong := strong p v hW
  dsimp only at haux hstrong
  -- names
  set J : V := v 0 with hJdef
  have hJ0 : 0 < J := hv 0
  set q : V := (p 0 : V) * J + 1 with hqdef
  set X : V := v 8 * q with hXdef
  set k : V := v 10 + v 11 with hkdef
  set c : V := k * v 7 + v 10 with hcdef
  set a : V := X * v 7 + v 7 with hadef
  set Hh : V := 4 * a + 3 with hHdef
  set R : V := ((p 0 : V) * J * (q - v 1) + v 2) * (q * q - 1) + ((p 2 : V) + q * (p 3 : V)) * J
    with hRdef
  set U : V := v 7 * v 7 with hUdef
  obtain ⟨_, hl', hh', _⟩ := CompactMaskBoundFinish.bounds (B : V) J hB hJ0
  have hl : (p 2 : V) < (p 0 : V) := by change (L : V) < (B : V); rw [hL]; exact hl'
  have hh : (p 3 : V) < 2 * (p 0 : V) := by
    change ((B + H : ℕ) : V) < 2 * (B : V); rw [Nat.cast_add, hH]; exact hh'
  have h46 : (46 : V) ≤ (p 0 : V) := by
    have h64 : (64 : V) = Exp.exp (6 : V) := by
      have h := ArithmeticStandardCasts.cast_exp (V := V) 6
      norm_num at h
      exact h.symm
    have hbig : (64 : V) ≤ (B : V) + 1 := by
      rw [hB, h64]; exact exp_monotone_le.mpr (by norm_num)
    change (46 : V) ≤ (B : V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46 : V) < 64) hbig
  obtain ⟨y0, hy0eq⟩ := hY
  have hy0 : 0 < y0 := by
    rcases (Arithmetic.zero_le y0).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hy0eq; exact (ne_of_gt (hv 7)) hy0eq
  have hYq : v 7 = q * (q * q) * y0 := by rw [hy0eq]; ring
  have hq47 : 47 ≤ q := by
    rw [hqdef]
    calc (47 : V) = 46 * 1 + 1 := by norm_num
      _ ≤ (p 0 : V) * J + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  have hqX : q ≤ X := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 8))
  have hX0 : 0 < X := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hq3) hqX
  -- the rank window
  set C : V := q - (v 1 + v 2) with hCdef
  have hC0 : 0 < C := tsub_pos_of_lt hFα
  have hq1 : 1 ≤ q := le_add_self
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have e1 : ι (q - v 1) = ι q - ι (v 1) := ι_tsub hF
  have e3 : ι (q * q - 1) = ι (q * q) - 1 := by simpa using ι_tsub (V := V) hqq1
  have eC : ι C = ι q - (ι (v 1) + ι (v 2)) := by rw [hCdef, ι_tsub (le_of_lt hFα), map_add ι (v 1) (v 2)]
  have hιq : ι q = ι (v 1) + (ι C + ι (v 2)) := by rw [eC]; ring
  have hιβJ : ι (p 0 : V) * ι J = ι q - 1 := by
    rw [hqdef]; simp [map_add, map_mul]
  have hι1 : ∀ {x : V}, 0 < x → (1 : DiffRing V) ≤ ι x := fun h => by
    simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)
  have eR : ι R = ((ι q - 1) * (ι q - ι (v 1)) + ι (v 2)) * (ι q * ι q - 1) +
      (ι (p 2 : V) + ι (p 3 : V) * ι q) * ι J := by
    rw [hRdef]
    simp only [map_add, map_mul, e1, e3]
    rw [← hιβJ]; ring
  have hwin : R + 1 < q * (q * (q * q)) := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_add, eR, map_one]
    simp only [map_mul]
    apply P72Window.window_ring hιq (hι1 (hv 1)) (hι1 (hv 2)) (hι1 hC0) (hι1 hJ0) hιβJ
    · simpa using (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hl)
    · have h := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hh)
      simpa [map_add, map_mul, map_ofNat] using h
  have hR26 : 26 ≤ R := by
    apply (ι_le_ι (V := V)).mp
    rw [eR, map_ofNat]
    have hq' : (47 : DiffRing V) ≤ ι q := by
      have h := (ι_le_ι (V := V)).mpr hq47; rwa [map_ofNat] at h
    have hα : (1 : DiffRing V) ≤ ι (v 2) := hι1 (hv 2)
    have hFq : ι (v 1) ≤ ι q := (ι_le_ι (V := V)).mpr hF
    have hW' : 0 ≤ (ι (p 2 : V) + ι (p 3 : V) * ι q) * ι J := by
      have := ι_nonneg (p 2 : V); have := ι_nonneg (p 3 : V); have := ι_nonneg J; positivity
    have hG : 1 ≤ (ι q - 1) * (ι q - ι (v 1)) + ι (v 2) := by
      have : 0 ≤ (ι q - 1) * (ι q - ι (v 1)) := mul_nonneg (by linarith) (by linarith)
      linarith
    have hqq : (26 : DiffRing V) ≤ ι q * ι q - 1 := by
      have h1 : ι q ≤ ι q * ι q := le_mul_of_one_le_left (by linarith) (by linarith)
      linarith
    have hprod := mul_le_mul hG hqq (by norm_num) (by linarith)
    linarith
  -- the generic sections
  have hH' : Hh = 3 + 4 * a := by rw [hHdef]; ring
  have hτ' : τ * τ = 1 + ((X * v 7) * v 7) * (((X * v 7) * v 7) + 1) * k * k := by
    rw [hτ]; ring
  have ha : a = X * v 7 + v 7 := rfl
  obtain ⟨n, s, μ, hny, hnx, _, hks, _, hRμ, hnmod⟩ :=
    P64Early.early q X (v 7) k R Hh U g c a (v 13) y0 τ hq3 hX0 hy0 hYq hH' ha rfl hτ' hcar hwin
  have hD : a * a + (4 * a + 3) = delta a := by unfold delta; ring
  have hmn : g * g = 1 + delta a * c * c := by rw [hgg, ← hD, hHdef]; ring
  obtain ⟨m, _, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a g c hmn
  have hs' : (v 5 * c * c) * (v 5 * c * c) + delta a = delta a * (v 4 * v 4) := by
    calc (v 5 * c * c) * (v 5 * c * c) + delta a =
        (v 5 * (c * c)) * (v 5 * (c * c)) + (a * a + (4 * a + 3)) := by rw [hD]; ring
      _ = (a * a + (4 * a + 3)) * (v 4 * v 4) := hstrong
      _ = delta a * (v 4 * v 4) := by rw [hD]
  have hc' : c = v 10 + v 7 * k := by rw [hcdef]; ring
  obtain ⟨hn13, hnm, hmR, hnR⟩ :=
    P72Exact.indices_ordinary q X (v 7) k R g c a y0 (v 5) (v 4) (v 6) (v 12) n s μ m (v 10)
      hq3 hX0 hy0 hYq (hv 10) hc' (hv 5) (hv 4) ha hR26 hny hks hRμ hnmod hmy hmn hs' haux
  -- g ≡ X + ac (mod H)
  have hU0 : 0 < U := mul_pos (hv 7) (hv 7)
  have hH0 : 0 < Hh := by rw [hHdef]; exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)
  have hcar' : U * (g + Hh * (4 * X * s)) = U * (X + a * c + Hh * v 13) := by
    have h1 : U * g + Hh * k = U * (g + Hh * (4 * X * s)) + Hh * (R + 1) := by
      rw [hks, ← hnR, hUdef]; ring
    have h2 : U * (X + a * c) + Hh * (U * v 13 + R + 1) = U * (X + a * c + Hh * v 13) + Hh * (R + 1) := by
      ring
    rw [h1, h2] at hcar
    exact add_right_cancel hcar
  have hgX : g + Hh * (4 * X * s) = X + a * c + Hh * v 13 := mul_left_cancel₀ (ne_of_gt hU0) hcar'
  have hgmod : g % Hh = (X + a * c) % Hh := by
    have h : (g + Hh * (4 * X * s)) % Hh = (X + a * c + Hh * v 13) % Hh := by rw [hgX]
    rwa [mod_add_mul' _ _ hH0, mod_add_mul' _ _ hH0] at h
  have hX16 : 16 ≤ X := le_trans (le_trans (by norm_num) hq47) hqX
  have hX2 : X = Exp.exp R :=
    P72Power.power_of_mod X (v 7) k R Hh g c a n m (v 10) (v 11) hX16 (hv 7) (hv 11) rfl hc' hH' ha
      hny hn13 hnR hmR hmx hmy hgmod
  -- the leaf facts at the free-J layout
  have hq' : 1 + J * (p 0 : V) = q := by rw [hqdef]; ring
  have hqm : q - 1 = (p 0 : V) * J := by rw [hqdef]; exact add_tsub_cancel_right _ _
  have hR' : ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
      ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J = R := by
    rw [hq', hqm, pow_two, hRdef]
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hτ; exact absurd hτ.symm (ne_of_gt (by simp))
  have hg0 : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hgg; exact absurd hgg.symm (ne_of_gt (by simp))
  have hqXd : q ∣ X := ⟨v 8, by rw [hXdef]; ring⟩
  refine ⟨X, hX0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
      pi = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J ∧
      2 * j' = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J + 1 ∧
      xcoord j' (2 * ((X * v 7) * v 7 - 1) + 1) = first ∧
      2 * ycoord j' (2 * ((X * v 7) * v 7 - 1) + 1) = v 10 + v 11 ∧
      xcoord pi (X * v 7 + v 7) = main ∧ ycoord pi (X * v 7 + v 7) = v 10 + v 7 * (v 10 + v 11)
    rw [hR', ← hc']
    exact ⟨τ, g, n, m, hτ0, hg0, hn13, hnm, hmR, hnR, hnx, hny, hmx, hmy⟩
  · intro _
    show 0 < 1 + J * (p 0 : V) - (v 1 + v 2)
    rw [hq']; exact hC0
  · intro _
    show ((v 1 + v 2) * (X + (p 1 : V) * (1 + J * (p 0 : V))) + v 1 * (1 + J * (p 0 : V))) %
        (J * (p 0 : V)) = ((1 + J * (p 0 : V)) * (X + (p 1 : V) * (1 + J * (p 0 : V)))) %
        (J * (p 0 : V))
    have hb' : 0 < J * (p 0 : V) := mul_pos hJ0 hb
    rw [hq']
    have hqC : q = (v 1 + v 2) + C := (add_tsub_cancel_of_le (le_of_lt hFα)).symm
    have htr' : q * (X + (p 1 : V) * q) =
        ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * (q * v 3) := by
      calc q * (X + (p 1 : V) * q) = ((v 1 + v 2) + C) * (X + (p 1 : V) * q) := by rw [← hqC]
        _ = (v 1 + v 2) * (X + (p 1 : V) * q) + ((p 1 : V) + v 8) * C * q := by rw [hXdef]; ring
        _ = (v 1 + v 2) * (X + (p 1 : V) * q) + (v 1 + v 3 * ((p 0 : V) * J)) * q := by rw [htr]
        _ = ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * (q * v 3) := by ring
    rw [htr', mod_add_mul' _ _ hb']
  · intro _ _ _ _
    show X = Exp.exp (((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J)
    rw [hR']; exact hX2
  · intro _ _ _
    show 1 + J * (p 0 : V) ∣ 3 * X ∧ 1 + J * (p 0 : V) ≤ 3 * X
    rw [hq']
    exact ⟨dvd_mul_of_dvd_right hqXd 3,
      le_trans hqX (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))⟩
  · intro _ _
    show (1 + J * (p 0 : V)) ^ 3 ∣ v 7
    rw [hq']
    exact ⟨y0, by rw [hy0eq]; ring⟩

/-- A positive zero of package 64's degree-30 equation at the compact44 ports
gives an internal halt of machine 215. -/
theorem halts (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j =>
      (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j : ℤ))).output v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨X, hX, hF⟩ := facts_ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    (CompactFixedBeta.beta_identity (V := V)) rfl rfl v hv hz
  apply CompactLeafFactsHalt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hX, hv]

end P64Facts

#print axioms P64Facts.facts_ports
#print axioms P64Facts.halts

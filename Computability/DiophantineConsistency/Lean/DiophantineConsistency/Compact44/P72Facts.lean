import DiophantineConsistency.Compact44.P72Power
import DiophantineConsistency.Compact44.CompactLeafFactsHalt

/-! # A positive P13 zero gives the six compact44 leaf facts, hence halting

The sections chain together as follows: §4 `strong_root`, §5 `first_root`,
§6 `main_root`, `aux_norm`, `window_ring`, `early`, `exact` and `power`. A
positive zero of package 72's P13 at symbolic compact44 ports then gives
`CompactLeafFacts.LeafFacts` at the free-J-layout valuation
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, where `q = 1 + Jβ`. The masks enter
only through `L = lowNat` and `H = highNat`. `CompactLeafFactsHalt.halts_of_facts`
then gives an internal halt of machine 215. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P72Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactLeafFacts
open P72Graph P72Root P72Main P72Aux P72Mu
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem add_mod_congr {x y z b : V} (hb : 0 < b) (h : y % b = z % b) :
    (x + y) % b = (x + z) % b := by
  have ey : x + y = (x + y % b) + b * (y / b) := by
    calc x + y = x + (b * (y / b) + y % b) := by rw [div_add_mod]
      _ = (x + y % b) + b * (y / b) := by ring
  have ez : x + z = (x + z % b) + b * (z / b) := by
    calc x + z = x + (b * (z / b) + z % b) := by rw [div_add_mod]
      _ = (x + z % b) + b * (z / b) := by ring
  rw [ey, ez, mod_add_mul' _ _ hb, mod_add_mul' _ _ hb, h]
theorem facts_ports (B K L H : ℕ) (hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))
    (hL : L = lowNat) (hH : H = highNat) (hB3 : B % 3 = 1)
    (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (ports B K L H j : ℤ))).output v) :
    ∃ J : V, 0 < J ∧
      LeafFacts (ports B K L H) ![J, v 0, v 1, 1, 1, v 6, v 7, 1, v 9, v 10, 1, 1] := by
  set p : Fin 4 → ℕ := ports B K L H with hpdef
  obtain ⟨hA0, hA1, hAa, hAs⟩ := (zero_iff (fun j => (p j : ℤ)) v).mp hz
  have hb : 0 < (p 0 : V) := by
    obtain ⟨h, _⟩ := CompactMaskBoundFinish.bounds (B : V) 1 hB (by simp)
    change 0 < (B : V); exact h
  obtain ⟨f, j, hf, hq, hff⟩ := strong_root p v hv hb hAs
  set J : V := 3 * j + 1 with hJdef
  have hJ0 : 0 < J := by rw [hJdef]; exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by simp)
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
  obtain ⟨hY, hpair, τ, hτ⟩ := first_root p v hv hA0
  have hqJ : v 0 + (v 2 + v 1) = 1 + (p 0 : V) * J := hq
  obtain ⟨g, hgg, hcar⟩ := main_root p v hv hb J hqJ hY hA1
  have haux := aux_norm p v hv hb f j hf hq hAa
  -- names
  set q : V := v 0 + (v 2 + v 1) with hqdef
  set k : V := v 9 + v 10 with hkdef
  set c : V := v 9 + v 7 * k with hcdef
  set a : V := v 6 * v 7 + v 7 with hadef
  set Hh : V := 3 + 4 * a with hHdef
  set R : V := ((q - 1) * (q - v 0) + v 1) * (q * q - 1) + ((p 2 : V) + (p 3 : V) * q) * J with hRdef
  set S : V := 4 * (v 7 * q) with hSdef
  set M : V := S * q with hMdef
  obtain ⟨y0, hy0eq⟩ := hY
  have hy0 : 0 < y0 := by
    rcases (Arithmetic.zero_le y0).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hy0eq; exact (ne_of_gt (hv 7)) hy0eq
  have hq1 : 1 ≤ q := pos_iff_one_le.mp (add_pos_of_pos_of_nonneg (hv 0) (Arithmetic.zero_le _))
  have hq47 : 47 ≤ q := by
    rw [hqJ]
    calc (47 : V) = 1 + 46 * 1 := by norm_num
      _ ≤ 1 + (p 0 : V) * J := (add_le_add_iff_left 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  -- the rank window
  have hqF : v 0 ≤ q := le_add_of_nonneg_right (Arithmetic.zero_le _)
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have e1 : ι (q - 1) = ι q - 1 := by simpa using ι_tsub (V := V) hq1
  have e2 : ι (q - v 0) = ι q - ι (v 0) := ι_tsub hqF
  have e3 : ι (q * q - 1) = ι (q * q) - 1 := by simpa using ι_tsub (V := V) hqq1
  have hιq : ι q = ι (v 0) + (ι (v 2) + ι (v 1)) := by simp [hqdef, map_add]
  have hιqJ : ι (p 0 : V) * ι J = ι q - 1 := by
    rw [show ι q = ι (1 + (p 0 : V) * J) from congrArg ι hqJ]; simp [map_add, map_mul]
  have hι1 : ∀ {x : V}, 0 < x → (1 : DiffRing V) ≤ ι x := fun h => by
    simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)
  have hwin : R + 1 < q * (q * (q * q)) := by
    apply (ι_lt_ι (V := V)).mp
    simp only [hRdef, map_add, map_mul, map_one, e1, e2, e3]
    apply P72Window.window_ring hιq (hι1 (hv 0)) (hι1 (hv 1)) (hι1 (hv 2)) (hι1 hJ0) hιqJ
    · simpa using (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hl)
    · have h := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hh)
      simpa [map_add, map_mul, map_ofNat] using h
  have hR26 : 26 ≤ R := by
    apply (ι_le_ι (V := V)).mp
    simp only [hRdef, map_add, map_mul, e1, e2, e3, map_ofNat]
    have hq' : (47 : DiffRing V) ≤ ι q := by
      have h := (ι_le_ι (V := V)).mpr hq47; rwa [map_ofNat] at h
    have hα : (1 : DiffRing V) ≤ ι (v 1) := hι1 (hv 1)
    have hFq : ι (v 0) ≤ ι q := (ι_le_ι (V := V)).mpr hqF
    have hW : 0 ≤ (ι (p 2 : V) + ι (p 3 : V) * ι q) * ι J := by
      have := ι_nonneg (p 2 : V); have := ι_nonneg (p 3 : V); have := ι_nonneg J; positivity
    have hG : 1 ≤ (ι q - 1) * (ι q - ι (v 0)) + ι (v 1) := by
      have : 0 ≤ (ι q - 1) * (ι q - ι (v 0)) := mul_nonneg (by linarith) (by linarith)
      linarith
    have hqq : (26 : DiffRing V) ≤ ι q * ι q - 1 := by
      have h1 : ι q ≤ ι q * ι q := le_mul_of_one_le_left (by linarith) (by linarith)
      linarith
    have hprod := mul_le_mul hG hqq (by norm_num) (by linarith)
    linarith
  -- the residues of β and q
  have hβ3 : (p 0 : V) = 3 * ((B / 3 : ℕ) : V) + 1 := by
    change (B : V) = _
    have h := Nat.div_add_mod B 3
    rw [hB3] at h
    have h' := congrArg (fun n : ℕ => (n : V)) h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h'
    exact h'.symm
  obtain ⟨t, ht⟩ := q_mod_three (p 0 : V) j ((B / 3 : ℕ) : V) hβ3
  have hqt : q = 3 * t + 2 := hq.trans ht
  -- §6
  have hτ' : τ * τ = 1 + ((v 6 * v 7) * v 7) * (((v 6 * v 7) * v 7) + 1) * k * k := by
    rw [hτ]; ring
  obtain ⟨n, s, μ, hny, hnx, _, hks, hμ0, _, hRμ, hnmod⟩ :=
    P72Early.early q (v 6) (v 7) k R Hh M S g c a (v 12) t y0 τ hq3 (hv 6) hy0 hy0eq
      rfl rfl rfl rfl hτ' hcar hqt hwin
  have hmn : g * g = 1 + delta a * c * c := by rw [hgg]; unfold delta; ring
  obtain ⟨m, _, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a g c hmn
  have hqH : Bez q Hh 1 := by
    have h := bez_q_H q t (4 * (q * q * y0 * (v 6 + 1))) hqt
    have e : q * (4 * (q * q * y0 * (v 6 + 1))) + 3 = Hh := by
      rw [hHdef, hadef, hy0eq]; ring
    rwa [e] at h
  have hf0 : 0 < f := by rw [hf]; exact add_pos_of_pos_of_nonneg (hv 3) (Arithmetic.zero_le _)
  obtain ⟨hn13, hnm, hmR, hnR, hqX⟩ :=
    P72Exact.exact q (v 6) (v 7) k R Hh M S g c a (v 12) y0 (v 4) f (v 5) (v 11) n s μ m (v 9)
      hq3 (hv 6) hy0 hy0eq (hv 9) rfl (hv 4) hf0 rfl rfl rfl hcar hqH hR26 hny hks hRμ hnmod
      hmy hmn hff haux
  have hX2 : v 6 = Exp.exp R :=
    P72Power.power q (v 6) (v 7) k R Hh M S g c a (v 12) y0 s n m (v 9) (v 10)
      (le_trans (by norm_num) hq47) (hv 6) hqX hy0 hy0eq (hv 10) rfl rfl rfl rfl rfl rfl hcar hks hny
      hn13 hnR hmR hmx hmy
  -- the leaf facts at the free-J layout
  have hq' : 1 + J * (p 0 : V) = q := by rw [hqJ]; ring
  have hR' : ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 0) + v 1) *
      ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J = R := by
    rw [hq', hRdef, pow_two, mul_comm q (p 3 : V)]
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hτ; exact absurd hτ.symm (ne_of_gt (by simp))
  have hg0 : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hgg; exact absurd hgg.symm (ne_of_gt (by simp))
  refine ⟨J, hJ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
      pi = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 0) + v 1) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J ∧
      2 * j' = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 0) + v 1) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J + 1 ∧
      xcoord j' (2 * ((v 6 * v 7) * v 7 - 1) + 1) = first ∧
      2 * ycoord j' (2 * ((v 6 * v 7) * v 7 - 1) + 1) = v 9 + v 10 ∧
      xcoord pi (v 6 * v 7 + v 7) = main ∧ ycoord pi (v 6 * v 7 + v 7) = v 9 + v 7 * (v 9 + v 10)
    rw [hR']
    exact ⟨τ, g, n, m, hτ0, hg0, hn13, hnm, hmR, hnR, hnx, hny, hmx, hmy⟩
  · intro _
    show 0 < 1 + J * (p 0 : V) - (v 0 + v 1)
    rw [hq', hqdef, show v 0 + (v 2 + v 1) = (v 0 + v 1) + v 2 by ring, add_tsub_cancel_left]
    exact hv 2
  · intro _
    show ((v 0 + v 1) * (v 6 + (p 1 : V) * (1 + J * (p 0 : V))) + v 0 * (1 + J * (p 0 : V))) %
        (J * (p 0 : V)) = ((1 + J * (p 0 : V)) * (v 6 + (p 1 : V) * (1 + J * (p 0 : V)))) %
        (J * (p 0 : V))
    have hb' : J * (p 0 : V) = q - 1 := by rw [← hq']; simp
    rw [hq', hb']
    have hqm : 0 < q - 1 := tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) hq3)
    rw [add_mod_congr hqm hpair]
    congr 1
    rw [hqdef]; ring
  · intro _ _ _ _
    show v 6 = Exp.exp (((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 0) + v 1) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J)
    rw [hR']; exact hX2
  · intro _ _ _
    show 1 + J * (p 0 : V) ∣ 3 * v 6 ∧ 1 + J * (p 0 : V) ≤ 3 * v 6
    rw [hq']
    refine ⟨dvd_mul_of_dvd_right hqX 3, ?_⟩
    exact le_trans (Arithmetic.le_of_dvd (hv 6) hqX) (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  · intro _ _
    show (1 + J * (p 0 : V)) ^ 3 ∣ v 7
    rw [hq']
    exact ⟨y0, by rw [hy0eq]; ring⟩
/-- A positive zero of P13 at the compact44 ports gives an internal halt of
machine 215. -/
theorem halts (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j =>
      (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j : ℤ))).output v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨J, hJ, hF⟩ := facts_ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    (CompactFixedBeta.beta_identity (V := V)) rfl rfl betaNat_mod_three v hv hz
  apply CompactLeafFactsHalt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hJ, hv]

end P72Facts

#print axioms P72Facts.facts_ports
#print axioms P72Facts.halts

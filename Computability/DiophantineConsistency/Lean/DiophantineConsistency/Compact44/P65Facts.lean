import DiophantineConsistency.Compact44.P65Root
import DiophantineConsistency.Compact44.P72Facts

/-! # A positive zero of package 65's degree-26 equation gives the six leaf facts

The residual lemmas of `P65Root` feed the generic P13 sections unchanged:
`P72Window.window_ring`, `P72Early.early`, `P72Exact.exact_ordinary` (65's
strong norm is already the ordinary one, with index `i`) and `P72Power.power`.
A positive zero at symbolic compact44 ports then gives
`CompactLeafFacts.LeafFacts` at the free-J-layout valuation
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, with `J = 1 + 3j` and `X = q + x`.
`CompactLeafFactsHalt.halts_of_facts` gives an internal halt of machine 215. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P65Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactLeafFacts
open P65Graph P65Root P72Mu
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts_ports (B K L H : ℕ) (hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))
    (hL : L = lowNat) (hH : H = highNat) (hB3 : B % 3 = 1)
    (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (ports B K L H j : ℤ))).output v) :
    ∃ J X : V, 0 < J ∧ 0 < X ∧
      LeafFacts (ports B K L H) ![J, v 1, v 2, 1, 1, X, v 8, 1, v 10, v 11, 1, 1] := by
  set p : Fin 4 → ℕ := ports B K L H with hpdef
  obtain ⟨hA0, hNm, hAt, hAa, hAs⟩ := (zero_iff (fun j => (p j : ℤ)) v).mp hz
  have hb : 0 < (p 0 : V) := by
    obtain ⟨h, _⟩ := CompactMaskBoundFinish.bounds (B : V) 1 hB (by simp)
    change 0 < (B : V); exact h
  obtain ⟨hFα, htr⟩ := transport p v hv hAt
  obtain ⟨hY, τ, hτ⟩ := first_root p v hA0
  have hF : v 1 ≤ 1 + (p 0 : V) * (1 + 3 * v 0) :=
    le_trans le_self_add (le_of_lt hFα)
  obtain ⟨g, hgg, hcar⟩ := main_root p v hv hb hF hY hNm
  have haux := aux_norm p v hF (hv 4) hAa
  have hstrong := strong p v hAs
  dsimp only at haux hstrong
  -- names
  set J : V := 1 + 3 * v 0 with hJdef
  have hJ0 : 0 < J := lt_of_lt_of_le (by simp) le_self_add
  set q : V := 1 + (p 0 : V) * J with hqdef
  set X : V := q + v 7 with hXdef
  set k : V := v 10 + v 11 with hkdef
  set c : V := v 10 + v 8 * k with hcdef
  rw [show v 8 + v 8 * X = X * v 8 + v 8 by ring] at hgg hcar haux hstrong
  set a : V := X * v 8 + v 8 with hadef
  set Hh : V := 3 + 4 * a with hHdef
  set R : V := (v 2 + ((p 0 : V) * J) * (q - v 1)) * (q * q - 1) + J * ((p 2 : V) + (p 3 : V) * q)
    with hRdef
  set S : V := 4 * (v 8 * q) with hSdef
  set M : V := S * q with hMdef
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
    · exfalso; rw [← h, mul_zero] at hy0eq; exact (ne_of_gt (hv 8)) hy0eq
  have hq47 : 47 ≤ q := by
    rw [hqdef]
    calc (47 : V) = 1 + 46 * 1 := by norm_num
      _ ≤ 1 + (p 0 : V) * J := (add_le_add_iff_left 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  have hX0 : 0 < X := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hq3) le_self_add
  -- the rank window
  set C : V := q - (v 1 + v 2) with hCdef
  have hC0 : 0 < C := tsub_pos_of_lt hFα
  have hq1 : 1 ≤ q := le_self_add
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
    have hW : 0 ≤ (ι (p 2 : V) + ι (p 3 : V) * ι q) * ι J := by
      have := ι_nonneg (p 2 : V); have := ι_nonneg (p 3 : V); have := ι_nonneg J; positivity
    have hG : 1 ≤ (ι q - 1) * (ι q - ι (v 1)) + ι (v 2) := by
      have : 0 ≤ (ι q - 1) * (ι q - ι (v 1)) := mul_nonneg (by linarith) (by linarith)
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
  obtain ⟨t, ht⟩ := q_mod_three (p 0 : V) (v 0) ((B / 3 : ℕ) : V) hβ3
  have hqt : q = 3 * t + 2 := by rw [hqdef, hJdef, ← ht]; ring
  -- the generic sections
  have hτ' : τ * τ = 1 + ((X * v 8) * v 8) * (((X * v 8) * v 8) + 1) * k * k := by
    rw [hτ]; ring
  have ha : a = X * v 8 + v 8 := rfl
  obtain ⟨n, s, μ, hny, hnx, _, hks, hμ0, _, hRμ, hnmod⟩ :=
    P72Early.early q X (v 8) k R Hh M S g c a (v 13) t y0 τ hq3 hX0 hy0 hy0eq
      rfl ha rfl rfl hτ' hcar hqt hwin
  have hD : (3 + 4 * a) + a * a = delta a := by unfold delta; ring
  have hmn : g * g = 1 + delta a * c * c := by rw [hgg, ← hD]; ring
  obtain ⟨m, _, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a g c hmn
  have hqH : Bez q Hh 1 := by
    have h := bez_q_H q t (4 * (q * q * y0 * (X + 1))) hqt
    have e : q * (4 * (q * q * y0 * (X + 1))) + 3 = Hh := by
      rw [hHdef, hadef, hy0eq]; ring
    rwa [e] at h
  have hs' : (v 5 * c * c) * (v 5 * c * c) + delta a = delta a * (v 4 * v 4) := by
    calc (v 5 * c * c) * (v 5 * c * c) + delta a =
        (v 5 * (c * c)) * (v 5 * (c * c)) + ((3 + 4 * a) + a * a) := by rw [hD]; ring
      _ = ((3 + 4 * a) + a * a) * (v 4 * v 4) := hstrong
      _ = delta a * (v 4 * v 4) := by rw [hD]
  obtain ⟨hn13, hnm, hmR, hnR, hqX⟩ :=
    P72Exact.exact_ordinary q X (v 8) k R Hh M S g c a (v 13) y0 (v 5) (v 4) (v 6) (v 12) n s μ m
      (v 10) hq3 hX0 hy0 hy0eq (hv 10) rfl (hv 5) (hv 4) ha rfl rfl hcar hqH hR26 hny hks hRμ hnmod
      hmy hmn hs' haux
  have hX2 : X = Exp.exp R :=
    P72Power.power q X (v 8) k R Hh M S g c a (v 13) y0 s n m (v 10) (v 11)
      (le_trans (by norm_num) hq47) hX0 hqX hy0 hy0eq (hv 11) rfl rfl rfl ha rfl rfl hcar hks hny
      hn13 hnR hmR hmx hmy
  -- the leaf facts at the free-J layout
  have hq' : 1 + J * (p 0 : V) = q := by rw [hqdef]; ring
  have hqm : q - 1 = (p 0 : V) * J := by rw [hqdef]; exact add_tsub_cancel_left _ _
  have hR' : ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
      ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J = R := by
    rw [hq', hqm, pow_two, hRdef]; ring
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hτ; exact absurd hτ.symm (ne_of_gt (by simp))
  have hg0 : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hgg; exact absurd hgg.symm (ne_of_gt (by simp))
  refine ⟨J, X, hJ0, hX0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
      pi = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J ∧
      2 * j' = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J + 1 ∧
      xcoord j' (2 * ((X * v 8) * v 8 - 1) + 1) = first ∧
      2 * ycoord j' (2 * ((X * v 8) * v 8 - 1) + 1) = v 10 + v 11 ∧
      xcoord pi (X * v 8 + v 8) = main ∧ ycoord pi (X * v 8 + v 8) = v 10 + v 8 * (v 10 + v 11)
    rw [hR']
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
    have htr' : q * (X + (p 1 : V) * q) =
        ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * (q * v 3) := by
      rw [htr]; ring
    rw [htr', mod_add_mul' _ _ hb']
  · intro _ _ _ _
    show X = Exp.exp (((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J)
    rw [hR']; exact hX2
  · intro _ _ _
    show 1 + J * (p 0 : V) ∣ 3 * X ∧ 1 + J * (p 0 : V) ≤ 3 * X
    rw [hq']
    refine ⟨dvd_mul_of_dvd_right hqX 3, ?_⟩
    exact le_trans (Arithmetic.le_of_dvd hX0 hqX) (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  · intro _ _
    show (1 + J * (p 0 : V)) ^ 3 ∣ v 8
    rw [hq']
    exact ⟨y0, by rw [hy0eq]; ring⟩

/-- A positive zero of package 65's degree-26 equation at the compact44 ports
gives an internal halt of machine 215. -/
theorem halts (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j =>
      (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j : ℤ))).output v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨J, X, hJ, hX, hF⟩ := facts_ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    (CompactFixedBeta.beta_identity (V := V)) rfl rfl betaNat_mod_three v hv hz
  apply CompactLeafFactsHalt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hJ, hX, hv]

end P65Facts

#print axioms P65Facts.facts_ports
#print axioms P65Facts.halts

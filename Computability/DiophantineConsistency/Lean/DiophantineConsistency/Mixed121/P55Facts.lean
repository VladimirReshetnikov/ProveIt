import DiophantineConsistency.Mixed121.P55Norm
import DiophantineConsistency.Mixed121.Mixed121Halt
import DiophantineConsistency.Compact44.P62Early
import DiophantineConsistency.Compact44.P72Facts

/-! # A positive zero of package 55's degree-52 equation gives the six leaf facts

`P55Norm.residuals` reduces a zero to `M = W = 0` and `Na = N0 = Nt = 1`, and
`P55Root` reads each in the model. The generic sections then apply:

* `P72Window.window_ring` and `P62Early.early`, for the modulus `U = 4q⁴`. The
  first norm `τ² = ℓ(ℓ + k) + 1` is `N0 = 1` itself;
* `P72Exact.indices_ordinary`, for the ordinary strong norm and the auxiliary
  norm with `y = V + e`, as for package 64;
* `P72Power.power_of_mod`. Here `q ∣ X` is immediate from `X = wq`. Once
  `2n = R + 1`, `U` divides `H·4XY²s'` (since `Y = sq³`), and cancelling `U`
  in the carrier gives `g ≡ X + ac (mod H)`.

`facts_ports` holds at any ports with `0 < β`, `MC < β`, `MF + β < 2β` and
`46 ≤ β`; those are exactly `Mixed121Ports.leaf_bounds`. So a positive zero
at the wang943-mixed-121x8801 ports gives `CompactLeafFacts.LeafFacts` at
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, and `Mixed121Halt.halts_of_facts`
gives an internal halt of machine 215 (`halts`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P55Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
open CompactLeafFacts
open P55Graph P55Root
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts_ports (p : Fin 4 → ℕ) (hb : 0 < (p 0 : V)) (hl : (p 2 : V) < (p 0 : V))
    (hh : (p 3 : V) < 2 * (p 0 : V)) (h46 : (46 : V) ≤ (p 0 : V))
    (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).output v) :
    ∃ X Y : V, 0 < X ∧ 0 < Y ∧
      LeafFacts p ![v 0, v 1, v 2, 1, 1, X, Y, 1, v 10, v 11, 1, 1] := by
  obtain ⟨hM, hW, hNa, hN0, hNt⟩ := P55Norm.residuals p v hv hb hz
  obtain ⟨hFα, htr⟩ := transport p v hv hNt
  have hF : v 1 ≤ qV p v := le_trans le_self_add (le_of_lt hFα)
  obtain ⟨g, hgg, hcar⟩ := main_root p v hv hb hF hM
  have hstrong := strong p v hW
  have haux := aux_norm p v hF (hv 4) hNa
  have hτ := first p v hN0
  -- names
  set J : V := v 0 with hJdef
  have hJ0 : 0 < J := hv 0
  set q : V := qV p v with hqdef
  have hqv : q = (p 0 : V) * J + 1 := rfl
  set X : V := XV p v with hXdef
  set Y : V := YV p v with hYdef
  set k : V := kV v with hkdef
  set c : V := cV p v with hcdef
  set a : V := aV p v with hadef
  set Hh : V := HV p v with hHdef
  set R : V := RV p v with hRdef
  set U : V := UV p v with hUdef
  have hq47 : 47 ≤ q := by
    rw [hqv]
    calc (47 : V) = 46 * 1 + 1 := by norm_num
      _ ≤ (p 0 : V) * J + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hqX : q ≤ X := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 8))
  have hX0 : 0 < X := lt_of_lt_of_le hq0 hqX
  have hY0 : 0 < Y := mul_pos (hv 7) (mul_pos (mul_pos hq0 hq0) hq0)
  -- the rank window
  set C : V := q - (v 1 + v 2) with hCdef
  have hC0 : 0 < C := tsub_pos_of_lt hFα
  have hq1 : 1 ≤ q := le_add_self
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have e1 : ι (q - v 1) = ι q - ι (v 1) := ι_tsub hF
  have e3 : ι (q * q - 1) = ι (q * q) - 1 := by simpa using ι_tsub (V := V) hqq1
  have eC : ι C = ι q - (ι (v 1) + ι (v 2)) := by
    rw [hCdef, ι_tsub (le_of_lt hFα), map_add ι (v 1) (v 2)]
  have hιq : ι q = ι (v 1) + (ι C + ι (v 2)) := by rw [eC]; ring
  have hιβJ : ι (p 0 : V) * ι J = ι q - 1 := by rw [hqv]; simp [map_add, map_mul]
  have hι1 : ∀ {x : V}, 0 < x → (1 : DiffRing V) ≤ ι x := fun h => by
    simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)
  have eR : ι R = ((ι q - 1) * (ι q - ι (v 1)) + ι (v 2)) * (ι q * ι q - 1) +
      (ι (p 2 : V) + ι (p 3 : V) * ι q) * ι J := by
    rw [hRdef, RV, ← hqdef, ← hJdef]
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
  -- the early congruence
  have hYq : Y = v 7 * (q * q * q) := by rw [hYdef, YV]
  have hτ' : v 9 * v 9 = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k := by
    rw [hτ]; simp only [ellV, EV]; ring
  obtain ⟨n, s', μ, hny, hnx, _, hks, _, hRμ, hnmod⟩ :=
    P62Early.early q X Y k R Hh U g c a (v 13) (v 8) (v 7) (v 9) hq3 (hv 8) (hv 7) rfl hYq rfl rfl rfl
      hτ' hcar hwin
  -- the ordinary strong and auxiliary indices
  have hD : a * a + (4 * a + 3) = delta a := by unfold delta; ring
  have hmn : g * g = 1 + delta a * c * c := by rw [hgg, ← hD]; simp only [ΔV, HV]; ring
  obtain ⟨m, _, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a g c hmn
  have hYq' : Y = q * (q * q) * v 7 := by rw [hYq]; ring
  have hc' : c = v 10 + Y * k := by rw [hcdef, cV]; ring
  have ha' : a = X * Y + Y := rfl
  have hs' : (v 5 * c * c) * (v 5 * c * c) + delta a = delta a * (v 4 * v 4) := by
    have e : ΔV p v = delta a := by rw [ΔV, HV]; unfold delta; ring
    calc (v 5 * c * c) * (v 5 * c * c) + delta a = (v 5 * (c * c)) * (v 5 * (c * c)) + ΔV p v := by
          rw [e]; ring
      _ = ΔV p v * (v 4 * v 4) := hstrong
      _ = delta a * (v 4 * v 4) := by rw [e]
  obtain ⟨hn13, hnm, hmR, hnR⟩ :=
    P72Exact.indices_ordinary q X Y k R g c a (v 7) (v 5) (v 4) (v 6) (v 12) n s' μ m (v 10)
      hq3 hX0 (hv 7) hYq' (hv 10) hc' (hv 5) (hv 4) ha' hR26 hny hks hRμ hnmod hmy hmn hs' haux
  -- g ≡ X + ac (mod H)
  have hU0 : 0 < U := mul_pos (by norm_num) (mul_pos (mul_pos hq0 hq0) (mul_pos hq0 hq0))
  have hH0 : 0 < Hh := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)
  have hcar' : U * (g + Hh * (v 8 * v 7 * v 7 * q * q * q * s')) = U * (X + a * c + Hh * v 13) := by
    have h1 : U * g + Hh * k = U * (g + Hh * (v 8 * v 7 * v 7 * q * q * q * s')) + Hh * (R + 1) := by
      rw [hks, ← hnR, hUdef, UV, hXdef, XV, hYq]; ring
    have h2 : U * (X + a * c) + Hh * (U * v 13 + R + 1) = U * (X + a * c + Hh * v 13) + Hh * (R + 1) := by
      ring
    rw [h1, h2] at hcar
    exact add_right_cancel hcar
  have hgX : g + Hh * (v 8 * v 7 * v 7 * q * q * q * s') = X + a * c + Hh * v 13 :=
    mul_left_cancel₀ (ne_of_gt hU0) hcar'
  have hgmod : g % Hh = (X + a * c) % Hh := by
    have h : (g + Hh * (v 8 * v 7 * v 7 * q * q * q * s')) % Hh = (X + a * c + Hh * v 13) % Hh := by
      rw [hgX]
    rwa [mod_add_mul' _ _ hH0, mod_add_mul' _ _ hH0] at h
  have hX16 : 16 ≤ X := le_trans (le_trans (by norm_num) hq47) hqX
  have hH' : Hh = 3 + 4 * a := by rw [hHdef, HV]; ring
  have hX2 : X = Exp.exp R :=
    P72Power.power_of_mod X Y k R Hh g c a n m (v 10) (v 11) hX16 hY0 (hv 11) rfl hc' hH' ha'
      hny hn13 hnR hmR hmx hmy hgmod
  -- the leaf facts at the free-J layout
  have hq' : 1 + J * (p 0 : V) = q := by rw [hqv]; ring
  have hqm : q - 1 = (p 0 : V) * J := by rw [hqv]; exact add_tsub_cancel_right _ _
  have hR' : ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
      ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J = R := by
    rw [hq', hqm, pow_two, hRdef, RV]
  have hg0 : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hgg; exact absurd hgg.symm (ne_of_gt (by simp))
  have hqXd : q ∣ X := ⟨v 8, by rw [hXdef, XV]; ring⟩
  refine ⟨X, Y, hX0, hY0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
      pi = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J ∧
      2 * j' = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J + 1 ∧
      xcoord j' (2 * ((X * Y) * Y - 1) + 1) = first ∧
      2 * ycoord j' (2 * ((X * Y) * Y - 1) + 1) = v 10 + v 11 ∧
      xcoord pi (X * Y + Y) = main ∧ ycoord pi (X * Y + Y) = v 10 + Y * (v 10 + v 11)
    rw [hR', show v 10 + Y * (v 10 + v 11) = c from hc'.symm]
    exact ⟨v 9, g, n, m, hv 9, hg0, hn13, hnm, hmR, hnR, hnx, hny, hmx, hmy⟩
  · intro _
    show 0 < 1 + J * (p 0 : V) - (v 1 + v 2)
    rw [hq']; exact hC0
  · intro _
    show ((v 1 + v 2) * (X + (p 1 : V) * (1 + J * (p 0 : V))) + v 1 * (1 + J * (p 0 : V))) %
        (J * (p 0 : V)) = ((1 + J * (p 0 : V)) * (X + (p 1 : V) * (1 + J * (p 0 : V)))) %
        (J * (p 0 : V))
    have hb' : 0 < J * (p 0 : V) := mul_pos hJ0 hb
    rw [hq']
    have hz1 : 1 ≤ v 3 := pos_iff_one_le.mp (hv 3)
    have hKC : ((p 1 : V) + v 8) * C = v 1 + (v 3 - 1) * ((p 0 : V) * J) := by
      have h1 : ((p 1 : V) + v 8) * C + (1 + (p 0 : V) * J) =
          (v 1 + (v 3 - 1) * ((p 0 : V) * J)) + (1 + (p 0 : V) * J) := by
        calc ((p 1 : V) + v 8) * C + (1 + (p 0 : V) * J) = ((p 1 : V) + v 8) * C + q := by
              rw [hqv]; ring
          _ = 1 + v 1 + v 3 * ((p 0 : V) * J) := htr
          _ = (v 1 + (v 3 - 1) * ((p 0 : V) * J)) + (1 + (p 0 : V) * J) := by
              nth_rewrite 1 [← tsub_add_cancel_of_le hz1]; ring
      exact add_right_cancel h1
    have hqC : q = (v 1 + v 2) + C := (add_tsub_cancel_of_le (le_of_lt hFα)).symm
    have htr' : q * (X + (p 1 : V) * q) =
        ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * ((v 3 - 1) * q) := by
      calc q * (X + (p 1 : V) * q) = ((v 1 + v 2) + C) * (X + (p 1 : V) * q) := by rw [← hqC]
        _ = (v 1 + v 2) * (X + (p 1 : V) * q) + ((p 1 : V) + v 8) * C * q := by rw [hXdef, XV]; ring
        _ = (v 1 + v 2) * (X + (p 1 : V) * q) + (v 1 + (v 3 - 1) * ((p 0 : V) * J)) * q := by rw [hKC]
        _ = ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * ((v 3 - 1) * q) := by ring
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
    show (1 + J * (p 0 : V)) ^ 3 ∣ Y
    rw [hq']
    exact ⟨v 7, by rw [hYq]; ring⟩

attribute [local irreducible] Mixed121Ports.ports

/-- A positive zero of package 55's degree-52 equation at the
wang943-mixed-121x8801 ports gives an internal halt of machine 215. -/
theorem halts (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (Mixed121Ports.ports j : ℤ))).output v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hb, hl, hh, h46⟩ := Mixed121Ports.leaf_bounds (V := V)
  obtain ⟨X, Y, hX, hY, hF⟩ := facts_ports Mixed121Ports.ports hb hl hh h46 v hv hz
  apply Mixed121Halt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hX, hY, hv]

end P55Facts

#print axioms P55Facts.facts_ports
#print axioms P55Facts.halts

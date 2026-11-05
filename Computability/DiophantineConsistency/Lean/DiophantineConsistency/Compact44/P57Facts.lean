import DiophantineConsistency.Compact44.P57Root
import DiophantineConsistency.Compact44.P57Early
import DiophantineConsistency.Compact44.OrdinaryBlankSignedIndex
import DiophantineConsistency.Compact44.P72Facts

/-! # A positive zero of package 57's degree-258 equation gives the six leaf facts

The unit guard (`P57Units.units`) and the root recoveries (`P57Root`) feed:

* `P72Window.window_ring` and `P57Early.early_of_mod`. The carrier, in either
  sign `W = Ug ± Sτ`, gives `(H·k) % U = (H(R+1)) % U`;
* `P72Exact.index_window`, then the ordinary-blank signed index theorem, then
  `P72Exact.index_close`. The theorem is `signed_half_index_blank` or its `_plus`
  variant, according to the sign of the recovered strong root. The ordinary
  strong index is `Δ·i`, from the normalized `f² = ΔI² + 1`;
* `P72Power.power_of_mod`. Once `2n = R + 1`, `U ∣ k − R − 1`, and the
  carrier divided by `U` gives `g ≡ X + ac (mod H)` in either sign.

A positive zero at symbolic compact44 ports thus gives
`CompactLeafFacts.LeafFacts` at `![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, and
`CompactLeafFactsHalt.halts_of_facts` gives an internal halt of machine 215. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P57Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactLeafFacts
open P57Graph P57Root
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts_ports (B K L H : ℕ) (hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))
    (hL : L = lowNat) (hH : H = highNat)
    (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (ports B K L H j : ℤ))).output v) :
    ∃ X Y : V, 0 < X ∧ 0 < Y ∧
      LeafFacts (ports B K L H) ![v 0, v 1, v 2, 1, 1, X, Y, 1, v 8, v 9, 1, 1] := by
  set p : Fin 4 → ℕ := ports B K L H with hpdef
  obtain ⟨hNt, hN, hJ⟩ := P57Units.units p v hz
  have hb : 0 < (p 0 : V) := by
    obtain ⟨h, _⟩ := CompactMaskBoundFinish.bounds (B : V) 1 hB (by simp)
    change 0 < (B : V); exact h
  obtain ⟨hFα, htr⟩ := transport p v hv hNt
  have hF : v 1 ≤ qV p v := le_trans le_self_add (le_of_lt hFα)
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
  set S : V := SV p v with hSdef
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
  have hq47 : 47 ≤ q := by
    rw [hqv]
    calc (47 : V) = 46 * 1 + 1 := by norm_num
      _ ≤ (p 0 : V) * J + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hqX : q ≤ X := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 7))
  have hX0 : 0 < X := lt_of_lt_of_le hq0 hqX
  have hY0 : 0 < Y := mul_pos (hv 6) (mul_pos (mul_pos hq0 hq0) hq0)
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
  have hRU : R + 1 < U := lt_of_lt_of_le hwin (by
    rw [hUdef, UV, ← hqdef]
    calc q * (q * (q * q)) ≤ 4 * (q * (q * (q * q))) :=
          le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)
      _ = 4 * ((q * q) * (q * q)) := by ring)
  -- the restored roots
  obtain ⟨g, τ, hgg, hττ, hcar⟩ := four_root p v hv hb hF hRU hN
  obtain ⟨f, y0, hff, hf0, hy0, haux⟩ := strong_aux p v hv hF hJ
  -- the early congruence
  have hYq : Y = v 6 * (q * q * q) := by rw [hYdef, YV]
  have hτ' : τ * τ = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k := by
    rw [hττ]; simp only [AV, ellV, EV]; ring
  have hWplus : U * (X + a * c) + Hh * (U * (v 11 + ellV p v) + k) =
      Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v)) := by ring
  have hmodk : (Hh * k) % U = (Hh * (R + 1)) % U := by
    have hU0 : 0 < U := lt_of_le_of_lt (Arithmetic.zero_le _) hRU
    rcases hcar with h | h
    · have e : Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v)) = Hh * (R + 1) + U * (g + Hh * τ) := by
        calc Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v)) =
            U * (X + a * c) + Hh * (U * (v 11 + ellV p v) + k) := by ring
          _ = U * g + S * τ + Hh * (R + 1) := h
          _ = Hh * (R + 1) + U * (g + Hh * τ) := by rw [show S = U * Hh from rfl]; ring
      have h1 : (Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v))) % U =
          (Hh * (R + 1) + U * (g + Hh * τ)) % U := by rw [e]
      rwa [mod_add_mul' _ _ hU0, mod_add_mul' _ _ hU0] at h1
    · have e : Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v) + Hh * τ) = Hh * (R + 1) + U * g := by
        calc Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v) + Hh * τ) =
            U * (X + a * c) + Hh * (U * (v 11 + ellV p v) + k) + S * τ := by
              rw [show S = U * Hh from rfl]; ring
          _ = U * g + Hh * (R + 1) := h
          _ = Hh * (R + 1) + U * g := by ring
      have h1 : (Hh * k + U * (X + a * c + Hh * (v 11 + ellV p v) + Hh * τ)) % U =
          (Hh * (R + 1) + U * g) % U := by rw [e]
      rwa [mod_add_mul' _ _ hU0, mod_add_mul' _ _ hU0] at h1
  obtain ⟨n, s', μ, hny, hnx, _, hks, _, hRμ, hnmod⟩ :=
    P57Early.early_of_mod q X Y k R Hh U a (v 7) (v 6) τ hq3 (hv 7) (hv 6) rfl hYq rfl rfl rfl
      hτ' hmodk hwin
  -- the index window, the signed step, and the close
  have hD : a * a + (4 * a + 3) = delta a := by unfold delta; ring
  have hΔa : ΔV p v = delta a := by rw [ΔV, HV]; unfold delta; ring
  have hmn : g * g = 1 + delta a * c * c := by rw [hgg, GV, hΔa]; ring
  obtain ⟨m, _, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a g c hmn
  have hYq' : Y = q * (q * q) * v 6 := by rw [hYq]; ring
  have hc' : c = v 8 + Y * k := by rw [hcdef, cV]; ring
  have ha' : a = X * Y + Y := rfl
  obtain ⟨hn13, hnm, hm14, hhalf, hbig, _, _, hc0⟩ :=
    P72Exact.index_window q X Y k R c a (v 6) n s' μ m (v 8) hq3 hX0 (hv 6) hYq' (hv 8) hc' ha'
      hR26 hny hks hnmod hmy
  set i' : V := ΔV p v * v 4 with hi'def
  have hi'0 : 0 < i' := mul_pos (lt_of_lt_of_le (by norm_num : (0 : V) < 3)
    (le_add_self.trans' le_add_self)) (hv 4)
  have hQ : QV p v = (i' * c * c) * (i' * c * c) := by rw [QV, IV, hi'def]; ring
  have hs' : (i' * c * c) * (i' * c * c) + delta a = delta a * (f * f) := by
    rw [hff, DV, IV, hi'def, hΔa]; ring
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR26
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm14
  have hmR : m = R := by
    rcases haux with hb' | hp'
    · rw [hQ] at hb'
      exact OrdinaryBlankSignedIndex.signed_half_index_blank a c g f i' (v 5) R y0 m hc0 hi'0 hf0 hm0 hy0
        hmy hR0 hhalf hmn hs' hbig hb'
    · rw [hQ] at hp'
      exact OrdinaryBlankSignedIndex.signed_half_index_blank_plus a c g f i' (v 5) R y0 m hc0 hi'0 hf0 hm0
        hy0 hmy hR0 hhalf hmn hs' hbig hp'
  have hnR : 2 * n = R + 1 := P72Exact.index_close R n μ m hRμ hnmod hnm hmR
  -- g ≡ X + ac (mod H)
  have hU0 : 0 < U := lt_of_le_of_lt (Arithmetic.zero_le _) hRU
  have hH0 : 0 < Hh := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)
  set r' : V := v 7 * v 6 * v 6 * q * q * q * s' with hr'def
  have hkr : k = R + 1 + U * r' := by
    rw [hks, ← hnR, hUdef, UV, ← hqdef, hr'def, hXdef, XV, ← hqdef, hYq]; ring
  have hgmod : g % Hh = (X + a * c) % Hh := by
    rcases hcar with h | h
    · have e : U * (X + a * c + Hh * (v 11 + ellV p v + r')) = U * (g + Hh * τ) := by
        apply add_right_cancel (b := Hh * (R + 1))
        calc U * (X + a * c + Hh * (v 11 + ellV p v + r')) + Hh * (R + 1) =
            U * (X + a * c) + Hh * (U * (v 11 + ellV p v) + k) := by rw [hkr]; ring
          _ = U * g + S * τ + Hh * (R + 1) := h
          _ = U * (g + Hh * τ) + Hh * (R + 1) := by rw [hSdef, SV]; ring
      have e' := mul_left_cancel₀ (ne_of_gt hU0) e
      have h1 : (X + a * c + Hh * (v 11 + ellV p v + r')) % Hh = (g + Hh * τ) % Hh := by rw [e']
      rwa [mod_add_mul' _ _ hH0, mod_add_mul' _ _ hH0, eq_comm] at h1
    · have e : U * (X + a * c + Hh * (v 11 + ellV p v + r' + τ)) = U * g := by
        apply add_right_cancel (b := Hh * (R + 1))
        calc U * (X + a * c + Hh * (v 11 + ellV p v + r' + τ)) + Hh * (R + 1) =
            U * (X + a * c) + Hh * (U * (v 11 + ellV p v) + k) + S * τ := by
              rw [hkr, hSdef, SV]; ring
          _ = U * g + Hh * (R + 1) := h
      have e' := mul_left_cancel₀ (ne_of_gt hU0) e
      rw [← e', mod_add_mul' _ _ hH0]
  have hX16 : 16 ≤ X := le_trans (le_trans (by norm_num) hq47) hqX
  have hH' : Hh = 3 + 4 * a := by rw [hHdef, HV]; ring
  have hX2 : X = Exp.exp R :=
    P72Power.power_of_mod X Y k R Hh g c a n m (v 8) (v 9) hX16 hY0 (hv 9) rfl hc' hH' ha'
      hny hn13 hnR hmR hmx hmy hgmod
  -- the leaf facts at the free-J layout
  have hq' : 1 + J * (p 0 : V) = q := by rw [hqv]; ring
  have hqm : q - 1 = (p 0 : V) * J := by rw [hqv]; exact add_tsub_cancel_right _ _
  have hR' : ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
      ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J = R := by
    rw [hq', hqm, pow_two, hRdef, RV]
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hττ; exact absurd hττ.symm (ne_of_gt (lt_of_lt_of_le (by simp) le_add_self))
  have hg0 : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hgg; exact absurd hgg.symm (ne_of_gt (lt_of_lt_of_le (by simp) le_add_self))
  have hqXd : q ∣ X := ⟨v 7, by rw [hXdef, XV]; ring⟩
  refine ⟨X, Y, hX0, hY0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
      pi = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J ∧
      2 * j' = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J + 1 ∧
      xcoord j' (2 * ((X * Y) * Y - 1) + 1) = first ∧
      2 * ycoord j' (2 * ((X * Y) * Y - 1) + 1) = v 8 + v 9 ∧
      xcoord pi (X * Y + Y) = main ∧ ycoord pi (X * Y + Y) = v 8 + Y * (v 8 + v 9)
    rw [hR', show v 8 + Y * (v 8 + v 9) = c from hc'.symm]
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
    have hz1 : 1 ≤ v 3 := pos_iff_one_le.mp (hv 3)
    have hKC : ((p 1 : V) + v 7) * C = v 1 + (v 3 - 1) * ((p 0 : V) * J) := by
      have h1 : ((p 1 : V) + v 7) * C + (1 + (p 0 : V) * J) =
          (v 1 + (v 3 - 1) * ((p 0 : V) * J)) + (1 + (p 0 : V) * J) := by
        calc ((p 1 : V) + v 7) * C + (1 + (p 0 : V) * J) = ((p 1 : V) + v 7) * C + q := by
              rw [hqv]; ring
          _ = 1 + v 1 + v 3 * ((p 0 : V) * J) := htr
          _ = (v 1 + (v 3 - 1) * ((p 0 : V) * J)) + (1 + (p 0 : V) * J) := by
              nth_rewrite 1 [← tsub_add_cancel_of_le hz1]; ring
      exact add_right_cancel h1
    have hqC : q = (v 1 + v 2) + C := (add_tsub_cancel_of_le (le_of_lt hFα)).symm
    have htr' : q * (X + (p 1 : V) * q) =
        ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * ((v 3 - 1) * q) := by
      calc q * (X + (p 1 : V) * q) = ((v 1 + v 2) + C) * (X + (p 1 : V) * q) := by rw [← hqC]
        _ = (v 1 + v 2) * (X + (p 1 : V) * q) + ((p 1 : V) + v 7) * C * q := by rw [hXdef, XV]; ring
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
    exact ⟨v 6, by rw [hYq]; ring⟩

/-- A positive zero of package 57's degree-258 equation at the compact44 ports
gives an internal halt of machine 215. -/
theorem halts (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j =>
      (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j : ℤ))).output v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨X, Y, hX, hY, hF⟩ := facts_ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    (CompactFixedBeta.beta_identity (V := V)) rfl rfl v hv hz
  apply CompactLeafFactsHalt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hX, hY, hv]

end P57Facts

#print axioms P57Facts.facts_ports
#print axioms P57Facts.halts

import DiophantineConsistency.Mixed121.Short15Root
import DiophantineConsistency.Mixed121.Short15Index
import DiophantineConsistency.Mixed121.P55Facts
import DiophantineConsistency.Mixed121.Mixed121SparseKernel

/-! # Fifteen-positive forms: the six leaf facts and the halt

`facts_core` takes the model relations a zero gives (`Short15Root`):

* the first norm `τ² = ℓ(ℓ + k) + 1` at some root `τ`;
* the main norm `N1 = 1`, whose root is `D = X + ac + γH`;
* an index oracle: once `F ≤ q`, every Pell index `m` of `c` at base `a` with the
  window bounds `2R < c` and `(a + 2)Δ² < c` equals `R`. Each equation builds it
  from its auxiliary and strong norms (`Short15Index.oracle_*`);
* the sign `Nk = Nt = 1` or `Nk = Nt = −1`.

From the first norm, `k = 2n + 4XY²s'` (`ArithmeticPellFirstNorm`,
`ArithmeticPellCongruences.residue_quotients`), and `4XY²s' = E·4Ys'` with
`E = XY ≥ q⁴ > R + 1` (`Short15Index.window_ring0`). Then:

* **+ branch.** `k = R + 1 + hE` gives `(2n) % E = R + 1`, so `P72Exact.index_window`,
  the oracle and `P72Exact.index_close` give `13 ≤ n < m = R` and `2n = R + 1`;
  `D ≡ X + ac (mod H)` holds by construction, so `P72Power.power_of_mod` gives
  `X = 2^R`. The six leaf facts follow exactly as in `P55Facts`.
* **− branch.** `Nt = −1` and `0 < K0` still give `F + α ≤ q`, and
  `k + 1 = R + hE` gives `(2n + 1) % E = R` and `R + 1 ≤ k`. The window and the
  oracle give `m = R`, then `2n + 1 = R` (`Short15Index.close_neg`), which
  `Short15Index.minus_false` refutes.

`halts_core` instantiates this at the wang943-mixed-121x8801 ports and reaches
`Mixed121Halt.halts_of_facts`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Short15Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
open CompactLeafFacts
open Short15Graph Short15Root
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts_core (p : Fin 4 → ℕ) (hb : 0 < (p 0 : V)) (hl : (p 2 : V) < (p 0 : V))
    (hh : (p 3 : V) < 2 * (p 0 : V)) (h46 : (46 : V) ≤ (p 0 : V)) (hK : 0 < (p 1 : V))
    (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (τ : V)
    (hτ : τ * τ = ellV p v * (ellV p v + kV v) + 1)
    (hN1 : rN1 (fun j => (p j : ℤ)) (fun j => ι (v j)) = 1)
    (horacle : v 1 ≤ qV p v → 0 < RV p v → ∀ m g : V, 0 < m → ycoord m (aV p v) = cV p v →
      g * g = 1 + delta (aV p v) * cV p v * cV p v → 2 * RV p v < cV p v →
      (aV p v + 2) * delta (aV p v) * delta (aV p v) < cV p v → m = RV p v)
    (hsign : (rNk (fun j => (p j : ℤ)) (fun j => ι (v j)) = 1 ∧
        rNt (fun j => (p j : ℤ)) (fun j => ι (v j)) = 1) ∨
      (rNk (fun j => (p j : ℤ)) (fun j => ι (v j)) = -1 ∧
        rNt (fun j => (p j : ℤ)) (fun j => ι (v j)) = -1)) :
    ∃ X Y : V, 0 < X ∧ 0 < Y ∧
      LeafFacts p ![v 0, v 1, v 2, 1, 1, X, Y, 1, v 11, v 12, 1, 1] := by
  have hmn := main p v hN1
  have hFα : v 1 + v 2 ≤ qV p v := by
    rcases hsign with ⟨_, hNt⟩ | ⟨_, hNt⟩
    · exact le_of_lt (transport_pos p v hv hNt).1
    · exact transport_neg p v hv hK hNt
  have hF : v 1 ≤ qV p v := le_trans le_self_add hFα
  have hE : EV p v = XV p v * YV p v := rfl
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
  set g : V := DV p v with hgdef
  have hq47 : 47 ≤ q := by
    rw [hqv]
    calc (47 : V) = 46 * 1 + 1 := by norm_num
      _ ≤ (p 0 : V) * J + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hqX : q ≤ X := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 9))
  have hX0 : 0 < X := lt_of_lt_of_le hq0 hqX
  have hYq : Y = v 8 * (q * q * q) := by rw [hYdef, YV]
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos (hv 8) (mul_pos (mul_pos hq0 hq0) hq0)
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hqE : q * (q * (q * q)) ≤ X * Y := by
    have e : X * Y = (v 9 * v 8) * (q * (q * (q * q))) := by rw [hXdef, XV, hYq]; ring
    rw [e]
    exact le_mul_of_one_le_left (Arithmetic.zero_le _)
      (one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 9)) (pos_iff_one_le.mp (hv 8)))
  -- the main Pell index
  obtain ⟨m, _, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a g c hmn
  -- the first norm
  have hQ : 0 < (X * Y) * Y := mul_pos hXY0 hY0
  have hτ' : τ * τ = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k := by
    rw [hτ]; simp only [ellV, EV]; ring
  obtain ⟨n, _, hnx, hny⟩ :=
    ArithmeticPellFirstNorm.positive_parameter_solution ((X * Y) * Y) τ k hQ hτ'
  have hQ1 : (X * Y) * Y - 1 + 1 = (X * Y) * Y := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : 2 * ((X * Y) * Y) ∣ 2 * ((X * Y) * Y - 1) + 1 + 1 :=
    ⟨1, by calc 2 * ((X * Y) * Y - 1) + 1 + 1 = 2 * ((X * Y) * Y - 1 + 1) := by ring
      _ = 2 * ((X * Y) * Y) * 1 := by rw [hQ1]; ring⟩
  obtain ⟨_, s', _, hys⟩ := ArithmeticPellCongruences.residue_quotients n
    (2 * ((X * Y) * Y - 1) + 1) (2 * ((X * Y) * Y)) hB
  have hks : k = 2 * n + 4 * ((X * Y) * Y) * s' := by rw [← hny, hys]; ring
  -- the rank window
  set C : V := q - (v 1 + v 2) with hCdef
  have hq1 : 1 ≤ q := le_add_self
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have e1 : ι (q - v 1) = ι q - ι (v 1) := ι_tsub hF
  have e3 : ι (q * q - 1) = ι (q * q) - 1 := by simpa using ι_tsub (V := V) hqq1
  have eC : ι C = ι q - (ι (v 1) + ι (v 2)) := by
    rw [hCdef, ι_tsub hFα, map_add ι (v 1) (v 2)]
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
    apply Short15Index.window_ring0 hιq (hι1 (hv 1)) (hι1 (hv 2)) (ι_nonneg C) (hι1 hJ0) hιβJ
    · simpa using (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hl)
    · have h := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hh)
      simpa [map_add, map_mul, map_ofNat] using h
  have hRE : R + 1 < X * Y := lt_of_lt_of_le hwin hqE
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
  have horacle' := horacle hF (lt_of_lt_of_le (by norm_num) hR26)
  have hYq' : Y = q * (q * q) * v 8 := by rw [hYq]; ring
  have hc' : c = v 11 + Y * k := by rw [hcdef, cV]; ring
  have ha' : a = X * Y + Y := rfl
  have hrep : 4 * ((X * Y) * Y) * s' = X * Y * (4 * Y * s') := by ring
  rcases hsign with ⟨hNk, hNt⟩ | ⟨hNk, hNt⟩
  · -- the + branch
    obtain ⟨hFα', htr⟩ := transport_pos p v hv hNt
    have hkh : k = R + 1 + v 5 * EV p v := index_pos p v hF hNk
    have e : 2 * n + X * Y * (4 * Y * s') = R + 1 + X * Y * v 5 := by
      calc 2 * n + X * Y * (4 * Y * s') = k := by rw [hks, hrep]
        _ = R + 1 + X * Y * v 5 := by rw [hkh, hE]; ring
    have hnmod : (2 * n) % (X * Y) = R + 1 := by
      have h : (2 * n + X * Y * (4 * Y * s')) % (X * Y) = (R + 1 + X * Y * v 5) % (X * Y) := by rw [e]
      rwa [mod_add_mul' _ _ hXY0, mod_add_mul' _ _ hXY0, mod_eq_self_of_lt hRE] at h
    obtain ⟨hn13, hnm, hm14, hhalf, hbig, _, _, _⟩ :=
      P72Exact.index_window q X Y k R c a (v 8) n s' (X * Y) m (v 11) hq3 hX0 (hv 8) hYq' (hv 11) hc'
        ha' hR26 hny hks hnmod hmy
    have hmR : m = R := horacle' m g (lt_of_lt_of_le (by norm_num) hm14) hmy hmn hhalf hbig
    have hnR : 2 * n = R + 1 := P72Exact.index_close R n (X * Y) m hRE hnmod hnm hmR
    -- g ≡ X + ac (mod H)
    have hH0 : 0 < Hh := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)
    have hgH : g = X + a * c + Hh * v 14 := by rw [hgdef, DV]; ring
    have hgmod : g % Hh = (X + a * c) % Hh := by rw [hgH, mod_add_mul' _ _ hH0]
    have hX16 : 16 ≤ X := le_trans (le_trans (by norm_num) hq47) hqX
    have hH' : Hh = 3 + 4 * a := by rw [hHdef, HV]; ring
    have hX2 : X = Exp.exp R :=
      P72Power.power_of_mod X Y k R Hh g c a n m (v 11) (v 12) hX16 hY0 (hv 12) rfl hc' hH' ha'
        hny hn13 hnR hmR hmx hmy hgmod
    -- the leaf facts at the free-J layout
    have hC0 : 0 < C := tsub_pos_of_lt hFα'
    have hq' : 1 + J * (p 0 : V) = q := by rw [hqv]; ring
    have hqm : q - 1 = (p 0 : V) * J := by rw [hqv]; exact add_tsub_cancel_right _ _
    have hR' : ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
        ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J = R := by
      rw [hq', hqm, pow_two, hRdef, RV]
    have hτ0 : 0 < τ := by
      rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h, mul_zero] at hτ; exact absurd hτ.symm (ne_of_gt (by simp))
    have hg0 : 0 < g := by
      rcases (Arithmetic.zero_le g).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h, mul_zero] at hmn; exact absurd hmn.symm (ne_of_gt (by simp))
    have hqXd : q ∣ X := ⟨v 9, by rw [hXdef, XV]; ring⟩
    refine ⟨X, Y, hX0, hY0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _
      show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
        pi = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
          ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J ∧
        2 * j' = ((1 + J * (p 0 : V) - 1) * (1 + J * (p 0 : V) - v 1) + v 2) *
          ((1 + J * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + J * (p 0 : V)) * (p 3 : V)) * J + 1 ∧
        xcoord j' (2 * ((X * Y) * Y - 1) + 1) = first ∧
        2 * ycoord j' (2 * ((X * Y) * Y - 1) + 1) = v 11 + v 12 ∧
        xcoord pi (X * Y + Y) = main ∧ ycoord pi (X * Y + Y) = v 11 + Y * (v 11 + v 12)
      rw [hR', show v 11 + Y * (v 11 + v 12) = c from hc'.symm]
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
      have hKC : ((p 1 : V) + v 9) * C = v 1 + (v 3 - 1) * ((p 0 : V) * J) := by
        have h1 : ((p 1 : V) + v 9) * C + (1 + (p 0 : V) * J) =
            (v 1 + (v 3 - 1) * ((p 0 : V) * J)) + (1 + (p 0 : V) * J) := by
          calc ((p 1 : V) + v 9) * C + (1 + (p 0 : V) * J) = ((p 1 : V) + v 9) * C + q := by
                rw [hqv]; ring
            _ = 1 + v 1 + v 3 * ((p 0 : V) * J) := htr
            _ = (v 1 + (v 3 - 1) * ((p 0 : V) * J)) + (1 + (p 0 : V) * J) := by
                nth_rewrite 1 [← tsub_add_cancel_of_le hz1]; ring
        exact add_right_cancel h1
      have hqC : q = (v 1 + v 2) + C := (add_tsub_cancel_of_le (le_of_lt hFα')).symm
      have htr' : q * (X + (p 1 : V) * q) =
          ((v 1 + v 2) * (X + (p 1 : V) * q) + v 1 * q) + J * (p 0 : V) * ((v 3 - 1) * q) := by
        calc q * (X + (p 1 : V) * q) = ((v 1 + v 2) + C) * (X + (p 1 : V) * q) := by rw [← hqC]
          _ = (v 1 + v 2) * (X + (p 1 : V) * q) + ((p 1 : V) + v 9) * C * q := by rw [hXdef, XV]; ring
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
      exact ⟨v 8, by rw [hYq]; ring⟩
  · -- the − branch is impossible
    exfalso
    have hkh : k + 1 = R + v 5 * EV p v := index_neg p v hF hNk
    have e : 2 * n + 1 + X * Y * (4 * Y * s') = R + X * Y * v 5 := by
      calc 2 * n + 1 + X * Y * (4 * Y * s') = k + 1 := by rw [hks, hrep]; ring
        _ = R + X * Y * v 5 := by rw [hkh, hE]; ring
    have hmod : (2 * n + 1) % (X * Y) = R := by
      have h : (2 * n + 1 + X * Y * (4 * Y * s')) % (X * Y) = (R + X * Y * v 5) % (X * Y) := by rw [e]
      rwa [mod_add_mul' _ _ hXY0, mod_add_mul' _ _ hXY0,
        mod_eq_self_of_lt (lt_trans (lt_add_one R) hRE)] at h
    have hR2n : R ≤ 2 * n + 1 := by rw [← hmod]; exact mod_le _ _
    have hn13 : 13 ≤ n := by
      have h24 : 2 * 12 < 2 * n := by
        have h25 : (2 * 12 : V) + 1 < 2 * n + 1 := lt_of_lt_of_le (by
          calc (2 * 12 : V) + 1 = 25 := by norm_num
            _ < 26 := by norm_num
            _ ≤ R := hR26) hR2n
        exact (add_lt_add_iff_right 1).mp h25
      have h12 : 12 < n := lt_of_mul_lt_mul_left h24 (Arithmetic.zero_le _)
      simpa only [show (12 : V) + 1 = 13 by norm_num] using lt_iff_succ_le.mp h12
    have hRk : R + 1 ≤ k := by
      have h1 : X * Y ≤ v 5 * EV p v := by
        rw [hE]; exact le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 5))
      have h2 : R + 1 + 1 ≤ X * Y := lt_iff_succ_le.mp hRE
      apply (add_le_add_iff_right (1 : V)).mp
      rw [hkh]
      calc R + 1 + 1 ≤ X * Y := h2
        _ ≤ R + X * Y := le_add_self
        _ ≤ R + v 5 * EV p v := (add_le_add_iff_left R).mpr h1
    obtain ⟨hnm, hm14, hhalf, hbig, _⟩ :=
      Short15Index.index_window' q X Y k R c a (v 8) n m (v 11) hq3 hX0 (hv 8) hYq' (hv 11) hc' ha'
        hn13 hRk hny hmy
    have hmR : m = R := horacle' m g (lt_of_lt_of_le (by norm_num) hm14) hmy hmn hhalf hbig
    have h2n : 2 * n + 1 = R := Short15Index.close_neg R n (X * Y) m hRE hmod hnm hmR
    exact Short15Index.minus_false X Y k c a n m (v 11) (v 12) hX0 hY0 (hv 12) rfl hc' ha' hny hmy
      (hmR.trans h2n.symm)

/-- Stated for variables: an `rfl` at the concrete ports would make the kernel
compare million-bit numerals. -/
theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl

/-- `0 < K0` at the 121x8801 ports (`Mixed121SparseKernel.kernel_bounds`). -/
theorem K0_pos : 0 < ((Mixed121Ports.ports 1 : ℕ) : V) := by
  have h : 0 < Mixed121Ports.ports 1 := by
    unfold Mixed121Ports.ports
    rw [ports_one]
    exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) 1070003)
      Mixed121SparseKernel.kernel_bounds.1
  exact_mod_cast h

attribute [local irreducible] Mixed121Ports.ports

/-- The halt at the wang943-mixed-121x8801 ports. -/
theorem halts_core (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (τ : V)
    (hτ : τ * τ = ellV Mixed121Ports.ports v * (ellV Mixed121Ports.ports v + kV v) + 1)
    (hN1 : rN1 (fun j => (Mixed121Ports.ports j : ℤ)) (fun j => ι (v j)) = 1)
    (horacle : v 1 ≤ qV Mixed121Ports.ports v → 0 < RV Mixed121Ports.ports v → ∀ m g : V, 0 < m →
      ycoord m (aV Mixed121Ports.ports v) = cV Mixed121Ports.ports v →
      g * g = 1 + delta (aV Mixed121Ports.ports v) * cV Mixed121Ports.ports v * cV Mixed121Ports.ports v →
      2 * RV Mixed121Ports.ports v < cV Mixed121Ports.ports v →
      (aV Mixed121Ports.ports v + 2) * delta (aV Mixed121Ports.ports v) * delta (aV Mixed121Ports.ports v) <
        cV Mixed121Ports.ports v → m = RV Mixed121Ports.ports v)
    (hsign : (rNk (fun j => (Mixed121Ports.ports j : ℤ)) (fun j => ι (v j)) = 1 ∧
        rNt (fun j => (Mixed121Ports.ports j : ℤ)) (fun j => ι (v j)) = 1) ∨
      (rNk (fun j => (Mixed121Ports.ports j : ℤ)) (fun j => ι (v j)) = -1 ∧
        rNt (fun j => (Mixed121Ports.ports j : ℤ)) (fun j => ι (v j)) = -1)) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hb, hl, hh, h46⟩ := Mixed121Ports.leaf_bounds (V := V)
  obtain ⟨X, Y, hX, hY, hF⟩ := facts_core Mixed121Ports.ports hb hl hh h46 K0_pos v hv τ hτ hN1
    horacle hsign
  apply Mixed121Halt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hX, hY, hv]

end Short15Facts

#print axioms Short15Facts.facts_core
#print axioms Short15Facts.K0_pos
#print axioms Short15Facts.halts_core

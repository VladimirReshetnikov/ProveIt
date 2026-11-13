import DiophantineConsistency.Nine121.Source31Rows
import DiophantineConsistency.Mixed121.Mixed121Halt
import DiophantineConsistency.Compact44.P72Power
import DiophantineConsistency.Compact44.P72Window

/-! # A positive zero of the 31-input parent source gives the six leaf facts

In every model `V` of `𝗜𝚺₁`, let `x : Fin 31 → V` be positive with every parent
row (`Source31Rows.rows`) vanishing in the ring of differences. The ring
identities of `Source31Rows.facts` read in `V` as:

* `L + 1 = q²`, `N = q³`, `X = wq`, `a = E + Y`, `E = XY`, `c = η + Yk` with
  `q = βJ + 1`, `Y = sN`, `k = η + ζ`;
* the first norm `τ² = 1 + Q(Q + 1)k²` with `Q = XY²`;
* the main norm `D² = 1 + Δc²` with `D = X + ac + γ(4a + 3)`, `Δ = (a+1)(a+3)`;
* the index equation `k = R + 1 + hE` and `V + R = jc`, where `R` is the
  packing formula;
* `V + c = fo`, the strong norm `(ic²)² + Δ = Δf²` and the auxiliary norm
  `(ic²)²V² + y² = 1 + (ic²)²y²`;
* the transport `(K + w)(q − F − α) = F + (z − 1)(q − 1)`.

So `V ≡ −c (mod f)` and `V ≡ −R (mod c)` directly, which is exactly the input
of `ArithmeticPellHalfIndex.half_index`: no auxiliary `T` has to be
reconstructed. The first norm and `E ∣ k − R − 1` give the early congruence
`2n ≡ R + 1 (mod E)`; `P72Exact.index_window`, the half index and
`P72Power.power_of_mod` then give `LeafFacts` at
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, for any ports with
`0 < β`, `MC < β`, `MF < 2β`, `46 ≤ β` (`facts_ports`). At the 121x8801 ports
`Mixed121Halt.halts_of_facts` gives an internal halt of machine 215 (`halts`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.Source31Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellHalfIndex
open CompactLeafFacts
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Natural ports, read in the ring of differences. -/
def portsR (p : Fin 4 → ℕ) : Fin 4 → DiffRing V := fun j => (((p j : ℕ) : ℤ) : DiffRing V)

theorem portsR_eq (p : Fin 4 → ℕ) :
    (portsR p : Fin 4 → DiffRing V) = fun j => ι ((p j : ℕ) : V) := by
  funext j
  simp only [portsR, Int.cast_natCast, map_natCast]

private theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

theorem facts_ports (p : Fin 4 → ℕ) (hb : 0 < (p 0 : V)) (hl : (p 2 : V) < (p 0 : V))
    (hh : (p 3 : V) < 2 * (p 0 : V)) (h46 : (46 : V) ≤ (p 0 : V))
    (x : Fin 31 → V) (hx : ∀ i, 0 < x i)
    (hz : ∀ k, Source31Rows.rows (portsR p) (fun i => ι (x i)) k = 0) :
    ∃ X Y : V, 0 < X ∧ 0 < Y ∧
      LeafFacts p ![x 0, x 1, x 2, 1, 1, X, Y, 1, x 12, x 13, 1, 1] := by
  rw [portsR_eq] at hz
  obtain ⟨hL, hN, hX, ha, hE, hc, hτ, hD, hΔ, hmain, hidx, hRf, htr, hfo, hstr, haux⟩ :=
    Source31Rows.facts _ _ hz
  -- the base `q = βJ + 1`
  obtain ⟨q, hqdef⟩ : ∃ q : V, q = (p 0 : V) * x 0 + 1 := ⟨_, rfl⟩
  have hιq : ι q = ι ((p 0 : ℕ) : V) * ι (x 0) + 1 := by rw [hqdef, map_add, map_mul, map_one]
  rw [← hιq] at hL hN hX hRf htr
  have hq' : 1 + x 0 * (p 0 : V) = q := by rw [hqdef]; ring
  have hqm : q - 1 = (p 0 : V) * x 0 := by rw [hqdef]; exact add_tsub_cancel_right _ _
  -- the registers in `V`
  have VN : x 16 = q * (q * q) := by
    apply ι_injective; simp only [map_mul]; exact hN
  have VX : x 21 = x 10 * q := by
    apply ι_injective; simp only [map_mul]; exact hX
  have Va : x 20 = x 17 + x 9 * x 16 := by
    apply ι_injective; simp only [map_add, map_mul]; exact ha
  have VE : x 17 = x 21 * (x 9 * x 16) := by
    apply ι_injective; simp only [map_mul]; exact hE
  have Vc : x 19 = x 12 + x 9 * x 16 * (x 12 + x 13) := by
    apply ι_injective; simp only [map_add, map_mul]; exact hc
  have Vτ : x 11 * x 11 = 1 + ((x 21 * (x 9 * x 16)) * (x 9 * x 16)) *
      ((x 21 * (x 9 * x 16)) * (x 9 * x 16) + 1) * (x 12 + x 13) * (x 12 + x 13) := by
    apply ι_injective; simp only [map_add, map_mul, map_one]; exact hτ
  have VD : x 22 = x 21 + x 20 * x 19 + x 15 * (4 * x 20 + 3) := by
    apply ι_injective; simp only [map_add, map_mul, map_ofNat]; exact hD
  have VΔ : x 30 = delta (x 20) := by
    apply ι_injective; unfold delta; simp only [map_add, map_mul, map_ofNat, map_one]
    linear_combination hΔ
  have Vmain : x 22 * x 22 = 1 + delta (x 20) * x 19 * x 19 := by
    rw [← VΔ]; apply ι_injective; simp only [map_add, map_mul, map_one]
    linear_combination hmain
  have Vidx : x 26 + (x 12 + x 13) = 1 + x 8 * x 19 + x 5 * x 17 := by
    apply ι_injective; simp only [map_add, map_mul, map_one]; exact hidx
  have Vfo : x 26 + x 19 = x 4 * x 7 := by
    apply ι_injective; simp only [map_add, map_mul]; exact hfo
  have Vstr : (x 6 * x 19 * x 19) * (x 6 * x 19 * x 19) + delta (x 20) =
      delta (x 20) * x 4 * x 4 := by
    rw [← VΔ]; apply ι_injective; simp only [map_add, map_mul]
    linear_combination hstr
  have Vaux : (x 6 * x 19 * x 19) * (x 6 * x 19 * x 19) * x 26 * x 26 + x 14 * x 14 =
      1 + (x 6 * x 19 * x 19) * (x 6 * x 19 * x 19) * x 14 * x 14 := by
    apply ι_injective; simp only [map_add, map_mul, map_one]
    linear_combination haux
  -- sizes of the base
  have hJ0 : 0 < x 0 := hx 0
  have hq47 : 47 ≤ q := by
    rw [hqdef]
    calc (47 : V) = 46 * 1 + 1 := by norm_num
      _ ≤ (p 0 : V) * x 0 + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul h46 (pos_iff_one_le.mp hJ0)
          (by simp) (Arithmetic.zero_le _))
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq47
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq3
  -- the transport: `F + α < q`
  have hFα : x 1 + x 2 < q := by
    by_contra hle
    have hle' : ι q ≤ ι (x 1) + ι (x 2) := by
      rw [← map_add]; exact (ι_le_ι (V := V)).mpr (le_of_not_gt hle)
    have hKw : (0 : DiffRing V) ≤ ι ((p 1 : ℕ) : V) + ι (x 10) := by
      have := ι_nonneg ((p 1 : ℕ) : V); have := ι_nonneg (x 10); linarith
    have h1 : (ι ((p 1 : ℕ) : V) + ι (x 10)) * (ι q - ι (x 1) - ι (x 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hKw (by linarith)
    have hz1 : (0 : DiffRing V) ≤ ι (x 3) - 1 := by have := ι_one_le (hx 3); linarith
    have hq1' : (0 : DiffRing V) ≤ ι q - 1 := by
      have : (1 : DiffRing V) ≤ ι q := by simpa using (ι_le_ι (V := V)).mpr hq1
      linarith
    have h2 : (1 : DiffRing V) ≤ ι (x 1) + (ι (x 3) - 1) * (ι q - 1) := by
      have := ι_one_le (hx 1); have := mul_nonneg hz1 hq1'; linarith
    linarith
  have hF : x 1 ≤ q := le_trans le_self_add (le_of_lt hFα)
  obtain ⟨C, hCdef⟩ : ∃ C : V, C = q - (x 1 + x 2) := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hCdef]; exact tsub_pos_of_lt hFα
  have eC : ι C = ι q - ι (x 1) - ι (x 2) := by
    rw [hCdef, ι_tsub (le_of_lt hFα), map_add]; ring
  -- the rank
  obtain ⟨R, hRdef⟩ : ∃ R : V,
      R = ((q - 1) * (q - x 1) + x 2) * (q * q - 1) + ((p 2 : V) + q * (p 3 : V)) * x 0 := ⟨_, rfl⟩
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have eR : ι R = ((ι q - 1) * (ι q - ι (x 1)) + ι (x 2)) * (ι q * ι q - 1) +
      (ι ((p 2 : ℕ) : V) + ι q * ι ((p 3 : ℕ) : V)) * ι (x 0) := by
    rw [hRdef]
    simp only [map_add, map_mul, ι_tsub hq1, ι_tsub hF, ι_tsub hqq1, map_one]
  have Vjc : x 26 + R = x 8 * x 19 := by
    apply ι_injective; rw [map_add, eR, map_mul]; linear_combination -hRf
  have hιβJ : ι ((p 0 : ℕ) : V) * ι (x 0) = ι q - 1 := by rw [hιq]; ring
  have hwin : R + 1 < q * (q * (q * q)) := by
    apply (ι_lt_ι (V := V)).mp
    have hw := P72Window.window_ring (q := ι q) (F := ι (x 1)) (α := ι (x 2)) (C := ι C)
      (β := ι ((p 0 : ℕ) : V)) (J := ι (x 0)) (MC := ι ((p 2 : ℕ) : V)) (MF := ι ((p 3 : ℕ) : V))
      (by rw [eC]; ring) (ι_one_le (hx 1)) (ι_one_le (hx 2)) (ι_one_le hC0) (ι_one_le hJ0) hιβJ
      (by simpa using (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hl))
      (by have h := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hh)
          simpa [map_add, map_mul, map_ofNat] using h)
    rw [map_add, eR, map_one]
    simp only [map_mul]
    calc ((ι q - 1) * (ι q - ι (x 1)) + ι (x 2)) * (ι q * ι q - 1) +
          (ι ((p 2 : ℕ) : V) + ι q * ι ((p 3 : ℕ) : V)) * ι (x 0) + 1 =
        ((ι q - 1) * (ι q - ι (x 1)) + ι (x 2)) * (ι q * ι q - 1) +
          (ι ((p 2 : ℕ) : V) + ι ((p 3 : ℕ) : V) * ι q) * ι (x 0) + 1 := by ring
      _ < _ := hw
  have hR26 : 26 ≤ R := by
    apply (ι_le_ι (V := V)).mp
    rw [eR, map_ofNat]
    have hq' : (47 : DiffRing V) ≤ ι q := by
      have h := (ι_le_ι (V := V)).mpr hq47; rwa [map_ofNat] at h
    have hα : (1 : DiffRing V) ≤ ι (x 2) := ι_one_le (hx 2)
    have hFq : ι (x 1) ≤ ι q := (ι_le_ι (V := V)).mpr hF
    have hW' : 0 ≤ (ι ((p 2 : ℕ) : V) + ι q * ι ((p 3 : ℕ) : V)) * ι (x 0) := by
      have := ι_nonneg ((p 2 : ℕ) : V); have := ι_nonneg ((p 3 : ℕ) : V)
      have := ι_nonneg (x 0); have := ι_nonneg q; positivity
    have hG : 1 ≤ (ι q - 1) * (ι q - ι (x 1)) + ι (x 2) := by
      have : 0 ≤ (ι q - 1) * (ι q - ι (x 1)) := mul_nonneg (by linarith) (by linarith)
      linarith
    have hqq : (26 : DiffRing V) ≤ ι q * ι q - 1 := by
      have h1 : ι q ≤ ι q * ι q := le_mul_of_one_le_left (by linarith) (by linarith)
      linarith
    have hprod := mul_le_mul hG hqq (by norm_num) (by linarith)
    linarith
  -- names for the Pell registers
  obtain ⟨X, hXdef⟩ : ∃ X : V, X = x 21 := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : V, Y = x 9 * x 16 := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : V, k = x 12 + x 13 := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : V, a = x 20 := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : V, c = x 19 := ⟨_, rfl⟩
  rw [← hXdef, ← hYdef, ← hkdef] at Vτ
  rw [← hadef, ← hcdef] at Vmain Vstr
  rw [← hcdef] at Vaux Vfo
  have hX0 : 0 < X := by rw [hXdef]; exact hx 21
  have hY0 : 0 < Y := by rw [hYdef]; exact mul_pos (hx 9) (hx 16)
  have hqX : q ≤ X := by rw [hXdef, VX]; exact le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hx 10))
  have hYq : Y = q * (q * q) * x 9 := by rw [hYdef, VN]; ring
  have hq3Y : q * (q * q) ≤ Y := by
    rw [hYq]; exact le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (hx 9))
  have ha' : a = X * Y + Y := by rw [hadef, Va, VE, hXdef, hYdef]
  -- the first norm and the early congruence modulo `E = XY`
  have hQ : 0 < (X * Y) * Y := mul_pos (mul_pos hX0 hY0) hY0
  obtain ⟨n, -, hnx, hny⟩ :=
    ArithmeticPellFirstNorm.positive_parameter_solution ((X * Y) * Y) (x 11) k hQ Vτ
  have hQ1 : (X * Y) * Y - 1 + 1 = (X * Y) * Y := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : 2 * ((X * Y) * Y) ∣ 2 * ((X * Y) * Y - 1) + 1 + 1 :=
    ⟨1, by calc 2 * ((X * Y) * Y - 1) + 1 + 1 = 2 * ((X * Y) * Y - 1 + 1) := by ring
      _ = 2 * ((X * Y) * Y) * 1 := by rw [hQ1]; ring⟩
  obtain ⟨_, s', _, hys⟩ :=
    ArithmeticPellCongruences.residue_quotients n (2 * ((X * Y) * Y - 1) + 1) (2 * ((X * Y) * Y)) hB
  have hks : k = 2 * n + 4 * ((X * Y) * Y) * s' := by rw [← hny, hys]; ring
  have hkR : k = R + 1 + x 5 * (X * Y) := by
    have h1 : x 26 + k = x 26 + (R + 1 + x 5 * (X * Y)) := by
      rw [hkdef, Vidx, ← Vjc, hXdef, hYdef, ← VE]; ring
    exact add_left_cancel h1
  obtain ⟨E, hEdef⟩ : ∃ E : V, E = X * Y := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEdef]; exact mul_pos hX0 hY0
  have hRE : R + 1 < E := by
    have h1 : q * (q * (q * q)) ≤ E := by
      rw [hEdef]
      calc q * (q * (q * q)) = q * (q * (q * q)) := rfl
        _ ≤ X * Y := mul_le_mul hqX hq3Y (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    exact lt_of_lt_of_le hwin h1
  have hnmod : (2 * n) % E = R + 1 := by
    have h : (2 * n + E * (4 * Y * s')) % E = (R + 1 + E * x 5) % E := by
      congr 1
      calc 2 * n + E * (4 * Y * s') = 2 * n + 4 * ((X * Y) * Y) * s' := by rw [hEdef]; ring
        _ = k := hks.symm
        _ = R + 1 + E * x 5 := by rw [hkR, hEdef]; ring
    rwa [mod_add_mul' _ _ hE0, mod_add_mul' _ _ hE0, mod_eq_self_of_lt hRE] at h
  -- the main index
  obtain ⟨m, -, hmx, hmy⟩ := ArithmeticPellClassification.solution_index a (x 22) c Vmain
  have hc' : c = x 12 + Y * k := by rw [hcdef, Vc, hYdef, hkdef]
  obtain ⟨hn13, hnm, hm14, hhalf, hbig, hk0, hY2, hc0⟩ :=
    P72Exact.index_window q X Y k R c a (x 9) n s' E m (x 12) hq3 hX0 (hx 9) hYq (hx 12) hc' ha'
      hR26 hny hks hnmod hmy
  -- the half index: `c = ψ_a(R)`
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR26
  have huf : SignMod (x 4) (x 26) c :=
    Or.inr (mod_eq_zero_iff_dvd.mpr ⟨x 7, Vfo⟩)
  have huc : SignMod c (x 26) R :=
    Or.inr (mod_eq_zero_iff_dvd.mpr ⟨x 8, by rw [Vjc, hcdef]; ring⟩)
  obtain ⟨-, hcR⟩ := half_index a c (x 22) (x 4) (x 6) R (x 14) (x 26) hc0 (hx 6) (hx 4) hR0 (hx 14)
    Vmain Vstr hbig hhalf Vaux huf huc
  have hmR : m = R := ArithmeticPellCongruences.index_unique a m R (hmy.trans hcR)
  have hnR : 2 * n = R + 1 := P72Exact.index_close R n E m hRE hnmod hnm hmR
  -- `X = 2^R`
  have hH : 3 + 4 * a = 3 + 4 * a := rfl
  have hgmod : x 22 % (3 + 4 * a) = (X + a * c) % (3 + 4 * a) := by
    have hH0 : 0 < 3 + 4 * a := add_pos_of_pos_of_nonneg (by norm_num) (Arithmetic.zero_le _)
    have e : x 22 = (X + a * c) + (3 + 4 * a) * x 15 := by rw [VD, hXdef, hadef, hcdef]; ring
    rw [e, mod_add_mul' _ _ hH0]
  have hX16 : 16 ≤ X := le_trans (le_trans (by norm_num) hq47) hqX
  have hX2 : X = Exp.exp R :=
    P72Power.power_of_mod X Y k R (3 + 4 * a) (x 22) c a n m (x 12) (x 13) hX16 hY0 (hx 13) hkdef hc'
      hH ha' hny hn13 hnR hmR hmx hmy hgmod
  -- the leaf facts
  have hR' : ((1 + x 0 * (p 0 : V) - 1) * (1 + x 0 * (p 0 : V) - x 1) + x 2) *
      ((1 + x 0 * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + x 0 * (p 0 : V)) * (p 3 : V)) * x 0 = R := by
    rw [hq', pow_two, hRdef]
  have hqXd : q ∣ X := ⟨x 10, by rw [hXdef, VX]; ring⟩
  refine ⟨X, Y, hX0, hY0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    show ∃ first main j' pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j' ∧ j' < pi ∧
      pi = ((1 + x 0 * (p 0 : V) - 1) * (1 + x 0 * (p 0 : V) - x 1) + x 2) *
        ((1 + x 0 * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + x 0 * (p 0 : V)) * (p 3 : V)) * x 0 ∧
      2 * j' = ((1 + x 0 * (p 0 : V) - 1) * (1 + x 0 * (p 0 : V) - x 1) + x 2) *
        ((1 + x 0 * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + x 0 * (p 0 : V)) * (p 3 : V)) * x 0 + 1 ∧
      xcoord j' (2 * ((X * Y) * Y - 1) + 1) = first ∧
      2 * ycoord j' (2 * ((X * Y) * Y - 1) + 1) = x 12 + x 13 ∧
      xcoord pi (X * Y + Y) = main ∧ ycoord pi (X * Y + Y) = x 12 + Y * (x 12 + x 13)
    rw [hR', ← ha', ← hkdef, ← hc']
    exact ⟨x 11, x 22, n, m, hx 11, hx 22, hn13, hnm, hmR, hnR, hnx, hny, hmx, hmy⟩
  · intro _
    show 0 < 1 + x 0 * (p 0 : V) - (x 1 + x 2)
    rw [hq', ← hCdef]; exact hC0
  · intro _
    show ((x 1 + x 2) * (X + (p 1 : V) * (1 + x 0 * (p 0 : V))) + x 1 * (1 + x 0 * (p 0 : V))) %
        (x 0 * (p 0 : V)) = ((1 + x 0 * (p 0 : V)) * (X + (p 1 : V) * (1 + x 0 * (p 0 : V)))) %
        (x 0 * (p 0 : V))
    have hb' : 0 < x 0 * (p 0 : V) := mul_pos hJ0 hb
    rw [hq']
    have hz1 : 1 ≤ x 3 := pos_iff_one_le.mp (hx 3)
    have hKC : ((p 1 : V) + x 10) * C = x 1 + (x 3 - 1) * ((p 0 : V) * x 0) := by
      apply ι_injective
      simp only [map_mul, map_add, ι_tsub hz1, map_one]
      rw [eC, hιβJ]; linear_combination htr
    have hqC : q = (x 1 + x 2) + C := by rw [hCdef]; exact (add_tsub_cancel_of_le (le_of_lt hFα)).symm
    have htr' : q * (X + (p 1 : V) * q) =
        ((x 1 + x 2) * (X + (p 1 : V) * q) + x 1 * q) + x 0 * (p 0 : V) * ((x 3 - 1) * q) := by
      calc q * (X + (p 1 : V) * q) = ((x 1 + x 2) + C) * (X + (p 1 : V) * q) := by rw [← hqC]
        _ = (x 1 + x 2) * (X + (p 1 : V) * q) + ((p 1 : V) + x 10) * C * q := by
            rw [hXdef, VX]; ring
        _ = (x 1 + x 2) * (X + (p 1 : V) * q) + (x 1 + (x 3 - 1) * ((p 0 : V) * x 0)) * q := by
            rw [hKC]
        _ = ((x 1 + x 2) * (X + (p 1 : V) * q) + x 1 * q) + x 0 * (p 0 : V) * ((x 3 - 1) * q) := by
            ring
    rw [htr', mod_add_mul' _ _ hb']
  · intro _ _ _ _
    show X = Exp.exp (((1 + x 0 * (p 0 : V) - 1) * (1 + x 0 * (p 0 : V) - x 1) + x 2) *
        ((1 + x 0 * (p 0 : V)) ^ 2 - 1) + ((p 2 : V) + (1 + x 0 * (p 0 : V)) * (p 3 : V)) * x 0)
    rw [hR']; exact hX2
  · intro _ _ _
    show 1 + x 0 * (p 0 : V) ∣ 3 * X ∧ 1 + x 0 * (p 0 : V) ≤ 3 * X
    rw [hq']
    exact ⟨dvd_mul_of_dvd_right hqXd 3,
      le_trans hqX (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))⟩
  · intro _ _
    show (1 + x 0 * (p 0 : V)) ^ 3 ∣ Y
    rw [hq']
    exact ⟨x 9, by rw [hYq]; ring⟩

attribute [local irreducible] Mixed121Ports.ports

/-- A positive zero of the 31-input parent source at the wang943-mixed-121x8801
ports gives an internal halt of machine 215. -/
theorem halts (x : Fin 31 → V) (hx : ∀ i, 0 < x i)
    (hz : ∀ k, Source31Rows.rows (portsR Mixed121Ports.ports) (fun i => ι (x i)) k = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hb, hl, hh, h46⟩ := Mixed121Ports.leaf_bounds (V := V)
  obtain ⟨X, Y, hX, hY, hF⟩ := facts_ports Mixed121Ports.ports hb hl hh h46 x hx hz
  apply Mixed121Halt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hX, hY, hx]

end Nine121.Source31Facts

#print axioms Nine121.Source31Facts.facts_ports
#print axioms Nine121.Source31Facts.halts

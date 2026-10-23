import DiophantineConsistency.NativeQuadraticSource52
import DiophantineConsistency.NativeNineFinalizer52
import DiophantineConsistency.NativeBaseBounds52
import DiophantineConsistency.NativeSparseBounds52
import DiophantineConsistency.NativeCoefficientBounds

/-! # The package-52 source and its nine-coordinate arithmetic equation

The coefficient-height premise is explicit. This theorem assembles the
literal source, masks, binomial ratio and finalizer without claiming native
port calibration or an internal ZFC proof.
-/

namespace DiophantineConsistency.NativeNineSource52

open Jones1982 NativeQuadraticParent NativeNineRatio52

def sourceBase (a b : ℕ) : ℕ := NativeBaseBounds52.base (2 ^ a) b

def sourceN (a b : ℕ) : ℕ := NativeQuadraticSource52.N (sourceBase a b)

def sourceCap (a b : ℕ) : ℕ := NativeBaseBounds52.cap (sourceBase a b) b

def sourceRank (ports : Fin 4 → ℤ) (a b g : ℕ) : ℕ :=
  NativeQuadraticSource52.rank ports (sourceBase a b) b g

def value (ports : Fin 4 → ℤ) (a b g : ℕ) (v : NewVars) (n : ℕ) : ℤ :=
  v.finalValue (sourceRank ports a b g) (sourceN a b) b g (sourceCap a b) n

def HasZero (ports : Fin 4 → ℤ) (a : ℕ) : Prop :=
  ∃ b g : ℕ, 0 < b ∧ 0 < g ∧ ∃ v : NewVars,
    0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.i ∧ ∃ n : ℕ, value ports a b g v n = 0

/-- Exactly nine natural coordinates; the six required positive registers
are shifted by one, and phi, j and n are used directly. -/
def varsOfTuple (x : Fin 9 → ℕ) : NewVars :=
  ⟨x 2 + 1, x 3 + 1, x 4 + 1, x 5, x 6 + 1, x 7⟩

def naturalValue (ports : Fin 4 → ℤ) (a : ℕ) (x : Fin 9 → ℕ) : ℤ :=
  value ports a (x 0 + 1) (x 1 + 1) (varsOfTuple x) (x 8)

theorem exists_naturalValue_zero_iff (ports : Fin 4 → ℤ) (a : ℕ) :
    (∃ x : Fin 9 → ℕ, naturalValue ports a x = 0) ↔ HasZero ports a := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x 0 + 1, x 1 + 1, by omega, by omega, varsOfTuple x,
      by dsimp [varsOfTuple]; omega, by dsimp [varsOfTuple]; omega,
      by dsimp [varsOfTuple]; omega, by dsimp [varsOfTuple]; omega, x 8, hx⟩
  · rintro ⟨b, g, hb, hg, v, hh, hs, hw, hi, n, hn⟩
    let x : Fin 9 → ℕ := ![b - 1, g - 1, v.h - 1, v.s - 1, v.w - 1, v.phi, v.i - 1, v.j, n]
    have hb' : b - 1 + 1 = b := by omega
    have hg' : g - 1 + 1 = g := by omega
    have hv : varsOfTuple x = v := by
      cases v with
      | mk h s w phi i j =>
        change 0 < h at hh
        change 0 < s at hs
        change 0 < w at hw
        change 0 < i at hi
        change NewVars.mk (h - 1 + 1) (s - 1 + 1) (w - 1 + 1) phi (i - 1 + 1) j =
          NewVars.mk h s w phi i j
        congr 1 <;> omega
    refine ⟨x, ?_⟩
    change value ports a (b - 1 + 1) (g - 1 + 1) (varsOfTuple x) n = 0
    rwa [hb', hg', hv]

theorem sourceN_eq (a b : ℕ) :
    sourceN a b = NativeBaseBounds52.packedBase (sourceBase a b) :=
  NativeBaseBounds52.packedBase_eq _

theorem ratio_size_bounds (ports : Fin 4 → ℤ) {a b g : ℕ} (hb : 0 < b) :
    8 ≤ sourceN a b ∧ b ≤ sourceN a b ∧ 8 ≤ sourceRank ports a b g ∧
      b ≤ sourceRank ports a b g ∧ 0 < sourceCap a b := by
  have hH : 0 < (2 : ℕ) ^ a := by positivity
  obtain ⟨hB, hbB⟩ := NativeBaseBounds52.base_bounds hH hb
  obtain ⟨hN, hbN⟩ := NativeBaseBounds52.packedBase_bounds hB hbB.le
  change 8 ≤ NativeBaseBounds52.packedBase (sourceBase a b) at hN
  change b ≤ NativeBaseBounds52.packedBase (sourceBase a b) at hbN
  rw [← sourceN_eq a b] at hN hbN
  have hNR : sourceN a b ≤ sourceRank ports a b g :=
    centralCode_ge_base (by omega)
  have hB0 : 0 < sourceBase a b := by
    change 0 < NativeBaseBounds52.base (2 ^ a) b
    omega
  exact ⟨hN, hbN, hN.trans hNR, hbN.trans hNR,
    NativeBaseBounds52.cap_pos hB0 hb⟩

theorem sourceBase_power {a b k : ℕ} (hb : b = 2 ^ k) :
    sourceBase a b = 2 ^ (a + 12 + 2 * k) := by
  rw [sourceBase, hb, NativeBaseBounds52.base_power]

theorem base_scale {a b k : ℕ} (hb : b = 2 ^ k) :
    (2 : ℤ) ^ (a + 12 + 2 * k) = 4096 * (2 : ℤ) ^ a * (b : ℤ) ^ 2 := by
  have he := sourceBase_power (a := a) hb
  unfold sourceBase NativeBaseBounds52.base at he
  exact_mod_cast he.symm

/-- Every zero of the supplied nine-coordinate arithmetic equation recovers
a zero of the literal positive source system. -/
theorem source_of_zero (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a)
    (hz : HasZero ports a) :
    ∃ x : Fin 31 → ℕ, ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0 := by
  obtain ⟨b, g, hb, _, v, hh, hs, hw, hi, n, hz⟩ := hz
  obtain ⟨hN, hbN, hR, hbR, hcap⟩ := ratio_size_bounds ports (g := g) (a := a) hb
  obtain ⟨hdvd, ⟨k, hbpow⟩, hgcap⟩ :=
    finalizer_sound v hR hN hbR hb hbN hcap hh hs hw hi ⟨n, hz⟩
  have hweak := NativeBaseBounds52.weak_cap_of_ratio hgcap
  have ht : 1 ≤ a + 12 + 2 * k := by omega
  have hB := sourceBase_power (a := a) hbpow
  have hweak' : g < 4 * b * (2 ^ (a + 12 + 2 * k)) ^ 174 := by
    simpa only [sourceCap, hB] using hweak
  have hdvd' : NativeQuadraticSource52.N (2 ^ (a + 12 + 2 * k)) ^ 2 ∣
      (2 * NativeQuadraticSource52.rank ports (2 ^ (a + 12 + 2 * k)) b g).choose
        (NativeQuadraticSource52.rank ports (2 ^ (a + 12 + 2 * k)) b g) := by
    simpa only [sourceN, sourceRank, hB] using hdvd
  obtain ⟨x, _, _, hx⟩ :=
    (NativeQuadraticSource52.source_contract ports (by positivity) hc hbpow ht
      (base_scale hbpow) hweak').mp hdvd'
  exact ⟨x, hx⟩

/-- A source zero supplies a cofinal power-of-two base and all nine
coordinates of the arithmetic equation. -/
theorem zero_of_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a)
    (x : Fin 31 → ℕ)
    (hx : ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0) : HasZero ports a := by
  let k := NativeBaseBounds52.cofinalExponent 0 x
  let b := 2 ^ k
  let B := sourceBase a b
  let g := NativeQuadraticSource52.code B x
  obtain ⟨_, hxb, hb⟩ := NativeBaseBounds52.cofinalBound_spec 0 x
  change (∀ i, x i < b) at hxb
  change 0 < b at hb
  obtain ⟨hB, hbB⟩ := NativeBaseBounds52.base_bounds (by positivity : 0 < (2 : ℕ) ^ a) hb
  have hB' : 1 < B := by change 1 < NativeBaseBounds52.base (2 ^ a) b; omega
  have hbB' : b ≤ B := hbB.le
  obtain ⟨hg, hgcode⟩ := NativeSparseBounds52.source_zero_code_bounds hB' hb hbB' ports x hxb hx
  change 0 < g at hg
  change g < b * B ^ 174 at hgcode
  have hgcap : 32 * g < sourceCap a b := NativeBaseBounds52.strong_cap_of_code hgcode
  have hweak : g < 4 * b * B ^ 174 := by nlinarith only [hgcode]
  have hBpow : B = 2 ^ (a + 12 + 2 * k) := sourceBase_power rfl
  have ht : 1 ≤ a + 12 + 2 * k := by omega
  have hweak' : g < 4 * b * (2 ^ (a + 12 + 2 * k)) ^ 174 :=
    (congrArg (fun z : ℕ => g < 4 * b * z ^ 174) hBpow).mp hweak
  have hcontract := NativeQuadraticSource52.source_contract ports (by positivity) hc
    (show b = 2 ^ k from rfl) ht (base_scale (show b = 2 ^ k from rfl)) hweak'
  have hdvd : sourceN a b ^ 2 ∣
      (2 * sourceRank ports a b g).choose (sourceRank ports a b g) := by
    have hcode : g = NativeQuadraticSource52.code (2 ^ (a + 12 + 2 * k)) x :=
      congrArg (fun z => NativeQuadraticSource52.code z x) hBpow
    have hd := hcontract.mpr ⟨x, hxb, hcode, hx⟩
    exact (congrArg (fun z : ℕ => NativeQuadraticSource52.N z ^ 2 ∣
      (2 * NativeQuadraticSource52.rank ports z b g).choose
        (NativeQuadraticSource52.rank ports z b g)) hBpow).mpr hd
  obtain ⟨hN, hbN, hR, hbR, _⟩ := ratio_size_bounds ports (g := g) (a := a) hb
  obtain ⟨v, hh, hs, hw, hi, n, hn⟩ :=
    finalizer_complete hR hN hbR hb hbN hgcap hdvd ⟨k, rfl⟩
  exact ⟨b, g, hb, hg, v, hh, hs, hw, hi, n, hn⟩

theorem hasZero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a) :
    HasZero ports a ↔
      ∃ x : Fin 31 → ℕ, ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0 :=
  ⟨source_of_zero ports a hc, fun ⟨x, hx⟩ => zero_of_source ports a hc x hx⟩

theorem natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a) :
    (∃ x : Fin 9 → ℕ, naturalValue ports a x = 0) ↔
      ∃ x : Fin 31 → ℕ, ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0 :=
  (exists_naturalValue_zero_iff ports a).trans (hasZero_iff_source ports a hc)

/-- The published coefficient sizes discharge the entire arithmetic-height
premise. Authentic native-port calibration remains a separate obligation. -/
theorem natural_zero_iff_source_published (ports : Fin 4 → ℤ)
    (hbeta : 0 ≤ ports 0 ∧ ports 0 < 2 ^ 590069)
    (htransport : 0 ≤ ports 1 ∧ ports 1 < 2 ^ 592884)
    (hMC : 0 ≤ ports 2 ∧ ports 2 < 2 ^ 590069)
    (hMF : 0 ≤ ports 3 ∧ ports 3 < 2 * 2 ^ 590069) :
    (∃ x : Fin 9 → ℕ, naturalValue ports 1182955 x = 0) ↔
      ∃ x : Fin 31 → ℕ, ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0 :=
  natural_zero_iff_source ports 1182955 (fun k p _ =>
    (NativeCoefficientBounds.weighted_rowCoefficient_lt_published ports
      hbeta htransport hMC hMF k p).le)

end DiophantineConsistency.NativeNineSource52

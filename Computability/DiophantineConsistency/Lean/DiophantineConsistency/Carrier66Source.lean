import DiophantineConsistency.Carrier66
import DiophantineConsistency.NativeSourceWindow

/-!
# The canonical parent restores the literal 31-coordinate source

This is a forward map from the actual canonical Carrier66 factors. All source
coordinates, their positivity, and all twenty-two residuals are derived. The
four fixed ports are unchanged, including the already shifted source MF.
The final window theorem uses only the explicit finite coefficient interface;
no tableau, halting, or consistency calibration is assumed.
-/

namespace DiophantineConsistency.Carrier66Source

variable {R : Type*} [CommRing R]

/-- The current auxiliary gap, not the old source coordinate numbered eight. -/
def auxGap (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  (Carrier66.core p v).c * v 7 - (Carrier66.core p v).rank

def strongError (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  (v 4) ^ 2 - (Carrier66.core p v).delta * (v 6) ^ 2 * (Carrier66.core p v).c ^ 4 - 1

/-- All thirty-one old-z source coordinates, with no additional unknown. -/
def source (p : Fin 4 → R) (v : Fin 15 → R) (j : Fin 31) : R :=
  let b := Carrier66.core p v
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | 5 => v 5
  | 6 => v 6 * b.delta
  | 7 => v 4 * auxGap p v
  | 8 => v 7 + b.delta * (v 6) ^ 2 * b.c ^ 3 * auxGap p v - 1
  | 9 => v 8
  | 10 => v 9
  | 11 => v 10
  | 12 => v 11
  | 13 => v 12
  | 14 => v 13
  | 15 => v 14
  | 16 => b.q ^ 3
  | 17 => b.E
  | 18 => b.ell + b.k
  | 19 => b.c
  | 20 => b.a
  | 21 => b.X
  | 22 => b.D
  | 23 => b.c ^ 2
  | 24 => b.q ^ 2 - 1
  | 25 => (v 4) ^ 2
  | 26 => b.V
  | 27 => (v 13) ^ 2 - b.V ^ 2
  | 28 => b.S
  | 29 => b.S ^ 2
  | _ => b.delta

/-- The complete residual ledger before imposing canonical factor values. -/
def residual (p : Fin 4 → R) (v : Fin 15 → R) (j : Fin 22) : R :=
  let b := Carrier66.core p v
  let e := strongError p v
  match j.val with
  | 7 => b.P - 1
  | 11 => b.Q - 1
  | 12 => Carrier66.index p v - 1 + e * auxGap p v
  | 13 => -e * auxGap p v
  | 14 => b.W - 1
  | 20 => -b.delta * e
  | 21 => b.U - 1
  | _ => 0

/-- The source's rank differs from the displayed rank by exactly the strong residual. -/
theorem rank_identity (p : Fin 4 → R) (v : Fin 15 → R) :
    (Carrier66.core p v).c * source p v 8 - source p v 26 -
      (Carrier66.core p v).rank = -strongError p v * auxGap p v := by
  let b := Carrier66.core p v
  change b.c * (v 7 + b.delta * (v 6)^2 * b.c^3 * (b.c*v 7-b.rank)-1) -
    ((v 4)^2*(b.c*v 7-b.rank)-b.c) - b.rank =
    -((v 4)^2-b.delta*(v 6)^2*b.c^4-1)*(b.c*v 7-b.rank)
  ring

/-- This verifies every literal source row, rather than a replacement system. -/
theorem row_formula (p : Fin 4 → R) (v : Fin 15 → R) (j : Fin 22) :
    SplitCertificate59.sourceRows p (source p v) j = residual p v j := by
  let b := Carrier66.core p v
  have hq : b.q = p 0 * v 0 + 1 := rfl
  have hX : b.X = v 9 * b.q := rfl
  have hY : b.Y = v 8 * b.q^3 := rfl
  have hE : b.E = b.X*b.Y := rfl
  have hk : b.k = v 11+v 12 := rfl
  have hell : b.ell = b.E*b.k*b.Y := rfl
  have hc : b.c = b.k*b.Y+v 11 := rfl
  have ha : b.a = b.E+b.Y := rfl
  have hH : b.H = 4*b.a+3 := rfl
  have hd : b.delta = b.a^2+b.H := rfl
  have hD : b.D = b.X+b.a*b.c+v 14*b.H := rfl
  have hR : b.rank = ((b.q-1)*(b.q-v 1)+v 2)*(b.q^2-1)+
      (p 2+b.q*p 3)*v 0 := Carrier65.rank_shape p (Carrier66.drop v 1)
  fin_cases j
  · change b.q^2-1+(-2*p 0)*v 0+(-(p 0^2))*(v 0)^2 = 0
    rw [hq]; ring
  · change -1+(-1)*(b.q^2-1)+b.q^3+(-p 0)*v 0+
      (-p 0)*(v 0*(b.q^2-1)) = 0
    rw [hq]; ring
  · change b.X+(-1)*v 9+(-p 0)*(v 0*v 9) = 0
    rw [hX,hq]; ring
  · change b.a+(-1)*b.E+(-1)*(v 8*b.q^3) = 0
    rw [ha,hY]; ring
  · change (-1)*(b.a*b.X)+b.E+b.E*b.X = 0
    rw [ha,hE]; ring
  · change b.c+(-1)*(v 12*b.a)+v 12*b.E+(-1)*v 11+
      (-1)*(v 11*b.a)+v 11*b.E = 0
    rw [hc,ha,hk]; ring
  · change b.ell+b.k+(-1)*(b.E*b.c)+(-1)*v 12+(-1)*v 11+v 11*b.E = 0
    rw [hell,hc,hk]; ring
  · change -1+(-1)*(b.ell+b.k)^2+v 12*(b.ell+b.k)+v 11*(b.ell+b.k)+(v 10)^2 =
      ((v 10)^2-b.ell*(b.ell+b.k))-1
    rw [hk]; ring
  · change b.D+(-1)*b.X+(-1)*(b.c*b.a)+(-3)*v 14+(-4)*(v 14*b.a) = 0
    rw [hD,hH]; ring
  · change -3+b.delta+(-4)*b.a+(-1)*b.a^2 = 0
    rw [hd,hH]; ring
  · change b.c^2+(-1)*b.c^2 = 0
    ring
  · change -1+(-1)*(b.c^2*b.delta)+b.D^2 = (b.D^2-b.delta*b.c^2)-1
    ring
  · change -1+b.V+v 12+v 11+(-1)*(source p v 8*b.c)+(-1)*(v 5*b.E) =
      (b.k-v 5*b.E-b.rank)-1+strongError p v*auxGap p v
    have hr := rank_identity p v
    change b.c*source p v 8-b.V-b.rank = -strongError p v*auxGap p v at hr
    rw [hk]
    linear_combination -hr
  · change 1+(-1)*b.V+(b.q^2-1)+(-1)*b.q^3+source p v 8*b.c+
      (-1)*(v 2*(b.q^2-1))+(-1)*v 1+(-1)*(v 1*(b.q^2-1))+v 1*b.q^3+
      (-p 3+-p 2+2*p 0)*v 0+p 0*(v 0*(b.q^2-1))+(-p 0)*(v 0*b.q^3)+
      (-p 0)*(v 0*v 1)+(-(p 0*p 3)+p 0^2)*(v 0)^2 =
      -strongError p v*auxGap p v
    have hr := rank_identity p v
    change b.c*source p v 8-b.V-b.rank = -strongError p v*auxGap p v at hr
    rw [hR] at hr
    rw [hq] at hr ⊢
    linear_combination hr
  · change p 1+v 9+(-p 1)*v 2+(-1)*(v 2*v 9)+(-1+-p 1)*v 1+
      (-1)*(v 1*v 9)+(p 0+p 0*p 1)*v 0+p 0*(v 0*v 9)+(-p 0)*(v 0*v 3) =
      ((p 1+v 9)*(b.q-v 1-v 2)+(b.q-v 1)-v 3*(p 0*v 0))-1
    rw [hq]; ring
  · change (v 4)^2+(-1)*(v 4)^2 = 0
    ring
  · change (v 4)^2*auxGap p v-b.c+b.c+(-1)*(v 4*(v 4*auxGap p v)) = 0
    ring
  · change (v 13)^2-b.V^2+b.V^2+(-1)*(v 13)^2 = 0
    ring
  · change v 6*b.delta*b.c^2+(-1)*(v 6*b.delta*b.c^2) = 0
    ring
  · change b.S^2+(-1)*b.S^2 = 0
    ring
  · change b.delta+(v 6*b.delta*b.c^2)^2+(-1)*((v 4)^2*b.delta) =
      -b.delta*((v 4)^2-b.delta*(v 6)^2*b.c^4-1)
    ring
  · change -1+(-1)*(((v 13)^2-b.V^2)*b.S^2)+(v 13)^2 =
      (b.S^2*(b.V^2-(v 13)^2)+(v 13)^2)-1
    ring

/-- The canonical scaled strong factor yields the unscaled norm; delta is nonzero. -/
theorem canonical_strong_error (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    strongError p v = 0 := by
  have hd := Carrier65.delta_pos p (Carrier66.drop v 1) hb
    (Carrier66.drop_pos v 1 hv (by norm_num))
  change 0 < (Carrier66.core p v).delta at hd
  have hid : (Carrier66.core p v).delta * strongError p v =
      (Carrier66.core p v).Z - (Carrier66.core p v).delta := by
    let b := Carrier66.core p v
    change b.delta*((v 4)^2-b.delta*(v 6)^2*b.c^4-1) =
      b.delta*(v 4)^2-(v 6*b.delta*b.c^2)^2-b.delta
    ring
  rw [hc.2.2.2.2.2.1, sub_self] at hid
  exact (mul_eq_zero.mp hid).resolve_left (ne_of_gt hd)

/-- All twenty-two equations follow from the actual canonical factors. -/
theorem canonical_rows (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    ∀ j, SplitCertificate59.sourceRows p (source p v) j = 0 := by
  have he := canonical_strong_error p v hb hv hc
  obtain ⟨hP,hQ,hU,hi,hW,hZ,hR⟩ := hc
  intro j
  rw [row_formula]
  fin_cases j <;> simp [residual, he, hP, hQ, hU, hi, hW]

/-- Every restored coordinate is positive, including the old auxiliary gap slots.
No source positivity or native-window conclusion is used to derive this. -/
theorem source_pos (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hcanon : Carrier66.Canonical p v) :
    ∀ j, 0 < source p v j := by
  let b := Carrier66.core p v
  have hp := Carrier66.drop_pos v 1 hv (by norm_num)
  have hq : 2 ≤ b.q := Carrier65.q_ge_two p (Carrier66.drop v 1) hb hp
  have hsc := Carrier65.scales_pos p (Carrier66.drop v 1) hb hp
  have hX : 0 < b.X := hsc.1
  have hY : 0 < b.Y := hsc.2.1
  have hE : 0 < b.E := hsc.2.2.1
  have ha : 0 < b.a := hsc.2.2.2
  have hd : 0 < b.delta := Carrier65.delta_pos p (Carrier66.drop v 1) hb hp
  have hi := hv 6
  have hT := hv 7
  have hs := hv 8
  have hf := hv 4
  have heta := hv 11
  have hzeta := hv 12
  have hgamma := hv 14
  have hk : 0 < b.k := add_pos heta hzeta
  have hc : 0 < b.c := by change 0 < b.k*b.Y+v 11; positivity
  have hell : 0 < b.ell := by change 0 < b.E*b.k*b.Y; positivity
  have hH : 0 < b.H := by change 0 < 4*b.a+3; positivity
  have hD : 0 < b.D := by change 0 < b.X+b.a*b.c+v 14*b.H; positivity
  have hY2 : 2 ≤ b.Y := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) hq 3
    have hmul := mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ v 8 from hs)
      (le_of_lt (pow_pos (show 0 < b.q by omega) 3))
    change 2 ≤ v 8*b.q^3
    norm_num at hpow
    nlinarith only [hpow,hmul]
  have hRlt : b.rank < b.k := by
    have hindex := hcanon.2.2.2.1
    change b.k-v 5*b.E-b.rank=1 at hindex
    have hprod := mul_pos (hv 5) hE
    linarith only [hindex,hprod]
  have hck : 2*b.k < b.c := by
    have hmul := mul_le_mul_of_nonneg_left hY2 hk.le
    change 2*b.k < b.k*b.Y+v 11
    nlinarith only [hmul,heta]
  have hRhalf : 2*b.rank < b.c := by linarith only [hRlt,hck]
  have hd0double : b.c < 2*auxGap p v := by
    have hct := mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ v 7 from hT) hc.le
    change b.c < 2*(b.c*v 7-b.rank)
    nlinarith only [hct,hRhalf]
  have hd0 : 0 < auxGap p v := by linarith only [hc,hd0double]
  have he := canonical_strong_error p v hb hv hcanon
  have hproduct : 0 < b.delta*(v 6)^2*b.c^4 := by positivity
  have hf2 : 1 < (v 4)^2 := by
    change (v 4)^2-b.delta*(v 6)^2*b.c^4-1=0 at he
    linarith only [he,hproduct]
  have hfge : 2 ≤ v 4 := by nlinarith only [hf,hf2]
  have hf4 : 4 ≤ (v 4)^2 := by nlinarith only [hfge]
  have hVc : b.c < b.V := by
    have hprod := mul_le_mul_of_nonneg_right hf4 hd0.le
    change b.c < (v 4)^2*auxGap p v-b.c
    nlinarith only [hprod,hd0double]
  have hV : 0 < b.V := lt_trans hc hVc
  have hc1 : 1 < b.c := by have := hk; omega
  have hV1 : 1 < b.V := lt_trans hc1 hVc
  have hS1 : 1 < b.S := by
    have hdi : 1 ≤ v 6*b.delta := mul_pos hi hd
    have hcc : 1 < b.c^2 := by nlinarith only [hc1]
    have hprod := mul_le_mul_of_nonneg_right hdi (sq_nonneg b.c)
    change 1 < v 6*b.delta*b.c^2
    nlinarith only [hprod,hcc]
  have hS : 0 < b.S := by omega
  have hg : 0 < (v 13)^2-b.V^2 := by
    have hu := hcanon.2.2.1
    have hid : (b.S^2-1)*((v 13)^2-b.V^2)=b.V^2-1 := by
      change b.S^2*(b.V^2-(v 13)^2)+(v 13)^2=1 at hu
      linear_combination -hu
    have hleft : 0 < b.S^2-1 := by nlinarith only [hS1]
    have hright : 0 < b.V^2-1 := by nlinarith only [hV1]
    have hmul : 0 < (b.S^2-1)*((v 13)^2-b.V^2) := by rw [hid]; exact hright
    exact (mul_pos_iff_of_pos_left hleft).mp hmul
  have h8 : 0 < v 7+b.delta*(v 6)^2*b.c^3*auxGap p v-1 := by
    have hp0 : 0 < b.delta*(v 6)^2*b.c^3*auxGap p v := by positivity
    omega
  have h24 : 0 < b.q^2-1 := by nlinarith only [hq]
  intro j
  fin_cases j
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · exact hv 4
  · exact hv 5
  · exact mul_pos hi hd
  · exact mul_pos hf hd0
  · exact h8
  · exact hv 8
  · exact hv 9
  · exact hv 10
  · exact hv 11
  · exact hv 12
  · exact hv 13
  · exact hv 14
  · exact pow_pos (show 0 < b.q by omega) 3
  · exact hE
  · exact add_pos hell hk
  · exact hc
  · exact ha
  · exact hX
  · exact hD
  · exact pow_pos hc 2
  · exact h24
  · exact pow_pos hf 2
  · exact hV
  · exact hg
  · exact hS
  · exact pow_pos hS 2
  · exact hd

/-- Natural coordinates obtained only after proving all integer coordinates positive. -/
def sourceNat (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (j : Fin 31) : ℕ :=
  (source p v j).toNat

theorem sourceNat_cast (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) (j : Fin 31) :
    (sourceNat p v j : ℤ) = source p v j :=
  Int.toNat_of_nonneg (source_pos p v hb hv hc j).le

theorem sourceNat_pos (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    ∀ j, 0 < sourceNat p v j := by
  intro j
  have h := source_pos p v hb hv hc j
  unfold sourceNat
  omega

theorem sourceNat_rows (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    ∀ j, SplitCertificate59.sourceRows p (fun k => (sourceNat p v k : ℤ)) j = 0 := by
  have hcast : (fun k => (sourceNat p v k : ℤ)) = source p v :=
    funext (sourceNat_cast p v hb hv hc)
  rw [hcast]
  exact canonical_rows p v hb hv hc

/-- The old source rank is exactly the rank of the current parent. -/
theorem nativeRank_eq (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    NativePellBootstrap.nativeRank (sourceNat p v) = (Carrier66.core p v).rank := by
  unfold NativePellBootstrap.nativeRank
  rw [sourceNat_cast p v hb hv hc, sourceNat_cast p v hb hv hc,
    sourceNat_cast p v hb hv hc]
  have hr := rank_identity p v
  rw [canonical_strong_error p v hb hv hc, neg_zero, zero_mul] at hr
  change (Carrier66.core p v).c*source p v 8-source p v 26 = _
  exact sub_eq_zero.mp hr

/-- The old source base is exactly the current q, including its natural cast. -/
theorem sourceQ_eq (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    NativeBinaryScale.sourceQ p (sourceNat p v) = (Carrier66.core p v).q.toNat := by
  have hq := Carrier65.q_ge_two p (Carrier66.drop v 1) hb
    (Carrier66.drop_pos v 1 hv (by norm_num))
  change 2 ≤ (Carrier66.core p v).q at hq
  apply Int.ofNat.inj
  change (NativeBinaryScale.sourceQ p (sourceNat p v) : ℤ) =
    ((Carrier66.core p v).q.toNat : ℤ)
  rw [NativeBinaryScale.sourceQ_cast p hb.le, sourceNat_cast p v hb hv hc,
    Int.toNat_of_nonneg (by omega : 0 ≤ (Carrier66.core p v).q)]
  change 1+v 0*p 0 = p 0*v 0+1
  ring

/-- Natural subtraction in the old source gap equals the current integer gap. -/
theorem gap_eq (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    NativeSourceMask.gap p (sourceNat p v) = (Carrier66.core p v).C.toNat := by
  unfold NativeSourceMask.gap
  rw [sourceQ_eq p v hb hv hc]
  change (Carrier66.core p v).q.toNat-(v 1).toNat-(v 2).toNat =
    ((Carrier66.core p v).q-v 1-v 2).toNat
  have hF := hv 1
  have hA := hv 2
  omega

/-- The full native arithmetic window follows from the canonical parent and
only the explicit finite mask interface. Every displayed scalar is the current
parent's scalar. No old-layout or tableau-calibration hypothesis is present. -/
theorem canonical_window (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (v : Fin 15 → ℤ)
    (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    ∃ N, 0 < N ∧ (Carrier66.core p v).q.toNat = (2^d)^N ∧
      (v 0).toNat = NativeMaskPopulation.repunit d N ∧
      0 < (Carrier66.core p v).C.toNat ∧
      (Carrier66.core p v).C.toNat+(v 1).toNat+(v 2).toNat = (Carrier66.core p v).q.toNat ∧
      ((Carrier66.core p v).C.toNat-1) &&& (MC*(v 0).toNat+1) = 0 ∧
      (v 1).toNat &&& (MF*(v 0).toNat-1) = 0 ∧
      Jones1982.σ 2 (Carrier66.core p v).rank.toNat = 3*(d*N)+2 ∧
      (v 9).toNat = 2^((Carrier66.core p v).rank.toNat-d*N) ∧
      ((p 1).toNat+(v 9).toNat)*(Carrier66.core p v).C.toNat =
        (v 1).toNat+((v 3).toNat-1)*((Carrier66.core p v).q.toNat-1) := by
  have hb : 0 < p 0 := by have := hi.beta_ge_fifteen; omega
  have hw := NativeSourceWindow.source_native_window p hi (sourceNat p v)
    (sourceNat_pos p v hb hv hc) (sourceNat_rows p v hb hv hc)
  rw [sourceQ_eq p v hb hv hc, gap_eq p v hb hv hc,
    nativeRank_eq p v hb hv hc] at hw
  exact hw

/-- Every positive actual Carrier65 zero restores a positive literal source
solution; the recovered parent is used only through the proved canonical map. -/
theorem positive_carrier_zero_source (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0 < v j) (hz : Carrier65.value p v = 0) :
    ∃ x : Fin 31 → ℕ, (∀ j, 0 < x j) ∧
      (∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) ∧
      (x 0 : ℤ) = v 0 ∧ (x 1 : ℤ) = v 1 ∧ (x 2 : ℤ) = v 2 ∧
      (x 3 : ℤ) = v 3 ∧ (x 10 : ℤ) = v 8 ∧
      NativePellBootstrap.nativeRank x = (Carrier65.core p v).rank := by
  have hb : 0 < p 0 := by have := hp.beta_min; omega
  obtain ⟨h,hh,hpos,hcanon⟩ := Carrier66.positive_zero_restores_canonical p hp v hv hz
  let u := Carrier66.restore p v h
  refine ⟨sourceNat p u,sourceNat_pos p u hb hpos hcanon,
    sourceNat_rows p u hb hpos hcanon,?_,?_,?_,?_,?_,?_⟩
  · exact sourceNat_cast p u hb hpos hcanon 0
  · exact sourceNat_cast p u hb hpos hcanon 1
  · exact sourceNat_cast p u hb hpos hcanon 2
  · exact sourceNat_cast p u hb hpos hcanon 3
  · exact sourceNat_cast p u hb hpos hcanon 10
  · exact nativeRank_eq p u hb hpos hcanon

end DiophantineConsistency.Carrier66Source

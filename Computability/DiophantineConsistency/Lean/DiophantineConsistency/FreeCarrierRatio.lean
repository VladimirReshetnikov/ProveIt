import DiophantineConsistency.NativeNineFinalizer52

/-!
# A free positive carrier for the numerical nine-variable ratio

The source parameters remain arbitrary. The only scale identity for the
normalized margin is the explicit `cap = 32*t`; no source or compiler
interpretation is assumed.
-/

namespace DiophantineConsistency.FreeCarrierRatio

open Jones1982

set_option maxRecDepth 12000
set_option maxHeartbeats 300000

/-- The absorbed CRT index `j` is nonnegative. A positive input uses `j+1`. -/
structure FreeVars where
  h : ℕ
  s : ℕ
  w : ℕ
  C : ℕ
  i : ℕ
  j : ℕ
  deriving DecidableEq, Repr

namespace FreeVars

/-- Before recovering the margin, the integer carrier offset may be negative. -/
def base (v : FreeVars) (R N b g cap : ℕ) : Nine.Vars :=
  ⟨R,N,b,g,cap,v.h,v.s,v.w,(v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w,v.i,0⟩

@[simp] theorem base_C (v : FreeVars) (R N b g cap : ℕ) :
    (v.base R N b g cap).C = (v.C : ℤ) := by
  simp only [base, Nine.Vars.C, Nine.Vars.B', Nine.Vars.W]
  ring

def H (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  RatioReparameterization.newH u.B' u.C u.F v.j

def I (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  (u.Gp^2-1)*(v.H R N b g cap)^2+1

def k (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  (v.i:ℤ)*u.J*u.C

def V0 (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  u.P*u.K

def V1 (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  v.k R N b g cap*(8*u.D^2-4*u.D-1)*u.Gp*v.H R N b g cap

def oldMargin (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  (u.K^2-4*(u.C-u.K*u.Y)^2)*(cap:ℤ)-8*(g:ℤ)*u.K^2

/-- For the selected architecture `t=b*B^W` and `cap=32*t`. -/
def margin (v : FreeVars) (R N b g cap t : ℕ) : ℤ :=
  let u := v.base R N b g cap
  u.K^2*(4*(t:ℤ)-(g:ℤ))-16*(t:ℤ)*(u.C-u.K*u.Y)^2

theorem margin_scale (v : FreeVars) (R N b g cap t : ℕ) (hcap : cap=32*t) :
    8*v.margin R N b g cap t = v.oldMargin R N b g cap := by
  unfold margin oldMargin
  have hc : (cap:ℤ)=32*(t:ℤ) := by exact_mod_cast hcap
  rw [hc]
  ring

/-- The positive final coordinate is written `n=nu+1` for the checked finalizer. -/
def Qstar (v : FreeVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  u.J*(u.W^2+1)+u.Q

def finalValue (v : FreeVars) (R N b g cap t n : ℕ) : ℤ :=
  let u := v.base R N b g cap
  NearSquareFinalizer.norm
    (u.J*((n:ℤ)+u.W^2)+u.Q-u.J*v.margin R N b g cap t*
      (v.V0 R N b g cap+v.V1 R N b g cap))
    (u.J*v.margin R N b g cap t) ((u.P^2-1)*u.K^2+1) 8
    (u.D*u.F*v.I R N b g cap)

theorem finalValue_succ (v : FreeVars) (R N b g cap t nu : ℕ) :
    v.finalValue R N b g cap t (nu+1) =
      let u := v.base R N b g cap
      MarginFinalizer.value ((u.P^2-1)*u.K^2+1) (u.D*u.F*v.I R N b g cap)
        (v.V0 R N b g cap) (v.V1 R N b g cap) u.J
          (v.Qstar R N b g cap) (v.margin R N b g cap t) nu := by
  simp only [finalValue, Qstar, MarginFinalizer.value, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- The explicit nonnegative old carrier parameter, used only after recovery. -/
def phi (v : FreeVars) (R b : ℕ) : ℕ :=
  ((v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w).toNat

def toRatio (v : FreeVars) (R b : ℕ) : NativeNineRatio52.NewVars :=
  ⟨v.h,v.s,v.w,v.phi R b,v.i,v.j⟩

end FreeVars

/-- Elementary bounds hold while the free carrier is as small as one. -/
structure Bounds (u : Nine.Vars) (H k : ℤ) : Prop where
  Y : 64 ≤ u.Y
  M : 0 < u.M
  U : 0 < u.U
  P : 0 < u.P
  PW : u.W < u.P
  PA : u.P < u.A^2
  K : 2 ≤ u.K
  KRP : u.R+u.P ≤ u.K
  A : 2 ≤ u.A
  AW : u.W < u.A
  C : 1 ≤ u.C
  J : 3 ≤ u.J
  W : 0 < u.W
  D : 0 < u.D
  E : 1 ≤ u.E
  F : 0 < u.F
  H : 1 ≤ H
  k : 3 ≤ k

theorem register_bounds {R N b g cap : ℕ} (v : FreeVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hb : 0 < b) (hbN : b ≤ N)
    (hh : 0 < v.h) (hs : 0 < v.s) (hw : 0 < v.w)
    (hC : 0 < v.C) (hi : 0 < v.i) :
    Bounds (v.base R N b g cap) (v.H R N b g cap) (v.k R N b g cap) := by
  let u := v.base R N b g cap
  have hRZ : 8 ≤ (R:ℤ) := by exact_mod_cast hR
  have hNZ : 8 ≤ (N:ℤ) := by exact_mod_cast hN
  have hbZ : 0 < (b:ℤ) := by exact_mod_cast hb
  have hbNZ : (b:ℤ) ≤ N := by exact_mod_cast hbN
  have hhZ : 1 ≤ (v.h:ℤ) := by exact_mod_cast hh
  have hsZ : 1 ≤ (v.s:ℤ) := by exact_mod_cast hs
  have hwZ : 0 < (v.w:ℤ) := by exact_mod_cast hw
  have hiZ : 1 ≤ (v.i:ℤ) := by exact_mod_cast hi
  have hC1 : 1 ≤ u.C := by dsimp [u]; rw [v.base_C]; exact_mod_cast hC
  have hY : 64 ≤ u.Y := by
    change 64 ≤ (N:ℤ)^2*v.s
    nlinarith only [mul_nonneg (sq_nonneg (N:ℤ)) (show 0 ≤ (v.s:ℤ)-1 by omega),hNZ]
  have hM : 0 < u.M := by change 0 < (R:ℤ)*u.Y; positivity
  have hU : 0 < u.U := by
    change 0 < (N:ℤ)^2*(v.w:ℤ)
    exact mul_pos (sq_pos_of_pos (by omega)) hwZ
  have hP : 0 < u.P := by change 0 < 2*u.M^2*u.U; positivity
  have hA : 2 ≤ u.A := by
    change 2 ≤ (Nine.Vars.ofNat R N b g cap v.h v.s v.w 0 v.i 0).A
    rw [Nine.cA]
    exact_mod_cast (Nine.sizes_nat hR hN hs hw).2
  have hKRP : u.R+u.P ≤ u.K := by
    change (R:ℤ)+u.P ≤ (R:ℤ)+1+(v.h:ℤ)*(u.P-1)
    nlinarith only [mul_nonneg (show 0 ≤ (v.h:ℤ)-1 by omega) (show 0 ≤ u.P-1 by omega)]
  have hK : 2 ≤ u.K := by
    have hRbase : u.R=(R:ℤ) := rfl
    rw [hRbase] at hKRP
    omega
  have hW : 0 < u.W := by change 0 < (b:ℤ)*v.w; exact mul_pos hbZ hwZ
  have hWU : u.W ≤ u.U := by
    change (b:ℤ)*v.w ≤ (N:ℤ)^2*v.w
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hbNZ,hNZ]) (le_of_lt hwZ)
  have hPU : u.U < u.P := by
    change u.U < 2*u.M^2*u.U
    nlinarith only [mul_nonneg (show 0 ≤ u.M^2-1 by nlinarith only [hM]) (le_of_lt hU),hU]
  have hAW : u.W < u.A := by
    change u.W < u.M*(u.U+1)
    nlinarith only [mul_nonneg (show 0 ≤ u.M-1 by omega) (show 0 ≤ u.U+1 by omega),hWU]
  have hJ : 3 ≤ u.J := by change 3 ≤ 4*u.A-5; omega
  have hD : 0 < u.D := by
    change 0 < (u.A^2-1)*u.C^2+1
    nlinarith only [mul_nonneg (show 0 ≤ u.A^2-1 by nlinarith only [hA]) (sq_nonneg u.C)]
  have hE : 1 ≤ u.E := by
    change 1 ≤ (v.i:ℤ)*u.J*u.D*u.C^2
    have he0 : 0 < (v.i:ℤ)*u.J*u.D*u.C^2 := by positivity
    omega
  have hF : 0 < u.F := by
    change 0 < (u.A^2-1)*u.E^2+1
    nlinarith only [mul_nonneg (show 0 ≤ u.A^2-1 by nlinarith only [hA]) (sq_nonneg u.E)]
  have hB : 0 < u.B' := by change 0 < 2*(R:ℤ)+1; omega
  have hH : 1 ≤ v.H R N b g cap := by
    change 1 ≤ u.C+u.F*(u.B'+(v.j:ℤ)*u.C)
    have hterm : 0 < u.B'+(v.j:ℤ)*u.C := by positivity
    nlinarith only [mul_pos hF hterm,hC1]
  have hk : 3 ≤ v.k R N b g cap := by
    change 3 ≤ (v.i:ℤ)*u.J*u.C
    have hIJ : u.J ≤ (v.i:ℤ)*u.J := by nlinarith only [mul_nonneg (show 0 ≤ (v.i:ℤ)-1 by omega) (show 0 ≤ u.J by omega)]
    have hIJC : (v.i:ℤ)*u.J ≤ (v.i:ℤ)*u.J*u.C := by
      nlinarith only [mul_nonneg (show 0 ≤ (v.i:ℤ)*u.J by positivity) (show 0 ≤ u.C-1 by omega)]
    omega
  exact ⟨hY,hM,hU,hP,hWU.trans_lt hPU,MarginSeparation.ratio_P_lt_A_sq hM,
    hK,hKRP,hA,hAW,hC1,hJ,hW,hD,hE,hF,hH,hk⟩

/-- The margin recovers the former carrier range before a natural phi is used. -/
theorem carrier_range_of_margin_pos {R N b g cap t : ℕ} (v : FreeVars)
    (hc : Bounds (v.base R N b g cap) (v.H R N b g cap) (v.k R N b g cap))
    (hcap : 0 < cap) (hscale : cap=32*t) (hm : 0 < v.margin R N b g cap t) :
    let u := v.base R N b g cap
    u.B'+u.W < u.C := by
  let u := v.base R N b g cap
  have hK : 2 ≤ u.K := hc.K
  have hY : 64 ≤ u.Y := hc.Y
  have hPW : u.W < u.P := hc.PW
  have hW : 0 < u.W := hc.W
  have hcapZ : 0 < (cap:ℤ) := by exact_mod_cast hcap
  have hmo : 0 < v.oldMargin R N b g cap := by
    rw [← v.margin_scale R N b g cap t hscale]
    positivity
  have hgap : 0 < u.K^2-4*(u.C-u.K*u.Y)^2 := by
    by_contra hh
    have hhead := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) (le_of_lt hcapZ)
    have htail : 0 ≤ 8*(g:ℤ)*u.K^2 := by positivity
    change 0 < (u.K^2-4*(u.C-u.K*u.Y)^2)*(cap:ℤ)-8*(g:ℤ)*u.K^2 at hmo
    linarith
  have hC2 : 2*u.K < u.C := by
    by_contra hh
    have hKY : 3*u.K ≤ u.K*u.Y := by
      nlinarith only [mul_nonneg (show 0 ≤ u.K by omega)
        (show 0 ≤ u.Y-3 by omega)]
    have hneg : u.K ≤ -(u.C-u.K*u.Y) := by omega
    have hsq := mul_self_le_mul_self (show 0 ≤ u.K by omega) hneg
    nlinarith only [hsq,hgap,sq_nonneg u.K]
  have hRP : u.R+u.P ≤ u.K := hc.KRP
  change 2*(R:ℤ)+1+u.W < u.C
  change (R:ℤ)+u.P ≤ u.K at hRP
  omega

namespace FreeVars

theorem phi_nonneg_of_range {R N b g cap : ℕ} (v : FreeVars)
    (h : (v.base R N b g cap).B'+(v.base R N b g cap).W < (v.base R N b g cap).C) :
    0 ≤ (v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w := by
  rw [v.base_C] at h
  change 2*(R:ℤ)+1+(b:ℤ)*v.w < (v.C:ℤ) at h
  omega

/-- The reconstructed natural carrier has exactly the supplied integer registers. -/
theorem toRatio_base {R N b g cap : ℕ} (v : FreeVars)
    (hphi : 0 ≤ (v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w) :
    (v.toRatio R b).base R N b g cap = v.base R N b g cap := by
  unfold toRatio NativeNineRatio52.NewVars.base NativeNineRatio52.NewVars.old
    Nine.Vars.ofNat base phi
  congr 1
  exact Int.toNat_of_nonneg hphi

theorem toRatio_H {R N b g cap : ℕ} (v : FreeVars)
    (hphi : 0 ≤ (v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w) :
    (v.toRatio R b).Hnew R N b g cap = v.H R N b g cap := by
  unfold NativeNineRatio52.NewVars.Hnew H
  rw [v.toRatio_base hphi]
  rfl

theorem toRatio_I {R N b g cap : ℕ} (v : FreeVars)
    (hphi : 0 ≤ (v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w) :
    (v.toRatio R b).Inew R N b g cap = v.I R N b g cap := by
  unfold NativeNineRatio52.NewVars.Inew I
  rw [v.toRatio_base hphi, v.toRatio_H hphi]

theorem toRatio_margin {R N b g cap : ℕ} (v : FreeVars)
    (hphi : 0 ≤ (v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w) :
    (v.toRatio R b).margin R N b g cap = v.oldMargin R N b g cap := by
  unfold NativeNineRatio52.NewVars.margin oldMargin
  rw [v.toRatio_base hphi]
  change (v.base R N b g cap).K^2*(cap:ℤ)-
    4*((v.base R N b g cap).C-(v.base R N b g cap).K*(v.base R N b g cap).Y)^2*(cap:ℤ)-
    8*(g:ℤ)*(v.base R N b g cap).K^2 = _
  ring

end FreeVars

/-- The shifted numerator fits the strict second majorant even for free C. -/
theorem shifted_Q_bounds {A C D G H k W J Q : ℤ}
    (hA : 2 ≤ A) (hC : 1 ≤ C) (hD : A^2 ≤ D) (hCD : C^2 < D)
    (hG : A ≤ G) (hH : 1 ≤ H) (hk : 3 ≤ k) (hW : 0 < W) (hWA : W < A)
    (hJ : J=4*A-5) (hQ : Q=3*W*C-2*(W^2-1)) :
    0 < J*(W^2+1)+Q ∧
      J*(W^2+1)+Q < k*(8*D^2-4*D-1)*G*H := by
  have hD1 : 1 ≤ D := by nlinarith only [hA,hD]
  have hW2 : W^2+1 ≤ D := by nlinarith only [hW,hWA,hD]
  have hWC : W*C+1 ≤ D := by nlinarith only [sq_nonneg (W-C),hW2,hCD]
  have hnum : J*(W^2+1)+Q = (4*A-7)*W^2+3*W*C+4*A-3 := by rw [hJ,hQ]; ring
  have hpos : 0 < J*(W^2+1)+Q := by
    rw [hnum]
    nlinarith only [mul_nonneg (show 0 ≤ 4*A-7 by omega) (sq_nonneg W),
      mul_pos hW (show 0 < C by omega),hA]
  have htop : J*(W^2+1)+Q ≤ (4*A-4)*D+1 := by
    rw [hnum]
    nlinarith only [mul_nonneg (show 0 ≤ 4*A-7 by omega)
      (show 0 ≤ D-W^2-1 by omega),hWC]
  have hfac : 0 ≤ 8*D^2-4*D-1 := by nlinarith only [hD1,sq_nonneg (D-1)]
  have hgap : (4*A-4)*D+1 < 3*(8*D^2-4*D-1)*A := by
    nlinarith only [mul_nonneg (show 0 ≤ A by omega)
      (mul_nonneg (show 0 ≤ D-1 by omega) (show 0 ≤ 24*D+8 by omega)),hA,hD1]
  have hlift : 3*(8*D^2-4*D-1)*A ≤ k*(8*D^2-4*D-1)*G*H := by
    calc
      _ ≤ k*(8*D^2-4*D-1)*G := mul_le_mul
        (mul_le_mul_of_nonneg_right hk hfac) hG (by omega) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (by omega) hfac) (by omega)) hH
  exact ⟨hpos,htop.trans_lt (hgap.trans_le hlift)⟩

namespace FreeVars

def Conditions (v : FreeVars) (R N b g cap t : ℕ) : Prop :=
  let u := v.base R N b g cap
  IsSquare ((u.P^2-1)*u.K^2+1) ∧ IsSquare (u.D*u.F*v.I R N b g cap) ∧
    u.J ∣ u.Q ∧ 0 < v.margin R N b g cap t

theorem Qstar_dvd_iff (v : FreeVars) (R N b g cap : ℕ) :
    (v.base R N b g cap).J ∣ v.Qstar R N b g cap ↔
      (v.base R N b g cap).J ∣ (v.base R N b g cap).Q := by
  unfold Qstar
  exact dvd_add_right (dvd_mul_right _ _)

end FreeVars

/-- The actual shifted finalizer has precisely the four ratio conditions. -/
theorem exists_finalValue_zero_iff {R N b g cap t : ℕ} (v : FreeVars)
    (hc : Bounds (v.base R N b g cap) (v.H R N b g cap) (v.k R N b g cap))
    (hcap : 0 < cap) (hscale : cap=32*t) :
    (∃ n : ℕ, 0<n ∧ v.finalValue R N b g cap t n=0) ↔ v.Conditions R N b g cap t := by
  let u := v.base R N b g cap
  have hA : 2 ≤ u.A := hc.A
  have hC : 1 ≤ u.C := hc.C
  have hE : 1 ≤ u.E := hc.E
  have hH : 1 ≤ v.H R N b g cap := hc.H
  have hk : 3 ≤ v.k R N b g cap := hc.k
  obtain ⟨hCD,hAF,hAI⟩ := MarginSeparation.pell_register_bounds (D:=u.D) (F:=u.F) (G:=u.Gp) (I:=v.I R N b g cap) hA hC hE hH
    (by rfl) (by rfl) (by rfl) (by rfl : v.I R N b g cap=(u.Gp^2-1)*(v.H R N b g cap)^2+1)
  have hAD : u.A^2 ≤ u.D := by
    change u.A^2 ≤ (u.A^2-1)*u.C^2+1
    nlinarith only [mul_nonneg (show 0 ≤ u.A^2-1 by nlinarith only [hA])
      (show 0 ≤ u.C^2-1 by nlinarith only [hC])]
  have hD : 0 < u.D := hc.D
  have hF : 0 < u.F := hc.F
  have hAG : u.A ≤ u.Gp := by
    have hCDD : u.D ≤ u.C*u.D := by nlinarith only [mul_nonneg (show 0 ≤ u.C-1 by omega) (le_of_lt hD)]
    change u.A ≤ u.A+u.F*(u.C*u.D+1-u.A)
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hF) (by nlinarith only [hAD,hCDD,hA]))
  have hGp : 0 < u.Gp := by omega
  have hI : 0 < v.I R N b g cap := by nlinarith only [hAI,hA]
  have hb0 : 0 < u.D*u.F*v.I R N b g cap := by positivity
  have hEeq : u.E=v.k R N b g cap*u.D*u.C := by
    change (v.i:ℤ)*u.J*u.D*u.C^2=((v.i:ℤ)*u.J*u.C)*u.D*u.C
    ring
  have hDF := NearSquareFinalizer.pell_product_identity u.A u.C u.D u.E u.F
    (v.k R N b g cap) rfl hEeq rfl
  obtain ⟨hV1,_,hbV⟩ := NearSquareFinalizer.full_majorant_bounds (I:=v.I R N b g cap)
    (show 0 < v.k R N b g cap by omega) (show 9 ≤ (v.k R N b g cap)^2 by nlinarith only [hk])
    (show 1 ≤ u.D by omega) hF hGp hH hDF (by rfl)
  have hP : 0 < u.P := hc.P
  have hK : 2 ≤ u.K := hc.K
  obtain ⟨ha0,hV0,haV⟩ := MarginSeparation.first_majorant hP hK
  obtain ⟨hQstar,hQstarV⟩ := shifted_Q_bounds (J:=u.J) (Q:=u.Q) (W:=u.W) hA hC hAD hCD hAG hH hk hc.W hc.AW rfl rfl
  have hJ : 0 < u.J := by have h : 3 ≤ u.J := hc.J; omega
  have hsep : 0 < v.margin R N b g cap t → (u.P^2-1)*u.K^2+1 < 64*(u.D*u.F*v.I R N b g cap) := by
    intro hm
    have hY : 64 ≤ u.Y := hc.Y
    have hKC : u.K < u.C := by
      have hmold : 0 < v.oldMargin R N b g cap := by rw [← v.margin_scale R N b g cap t hscale]; positivity
      exact MarginSeparation.coordinate_gt_of_margin_pos (C:=u.C) (K:=u.K) (Y:=u.Y) (by omega) (by omega)
        (by exact_mod_cast hcap) (Int.natCast_nonneg g) hmold
    have hsmall := MarginSeparation.radicand_lt_of_coordinate_gt hP hK (by omega : 0<u.A) hKC
      hc.PA hCD hAF hAI
    linarith only [hsmall,hb0]
  have hf := MarginFinalizer.exists_value_zero_iff (le_of_lt ha0) (le_of_lt hb0) hV0 hV1 haV
    (by simpa only [mul_assoc] using hbV) hJ hQstar hQstarV hsep
  rw [dvd_add_right (dvd_mul_right u.J (u.W^2+1))] at hf
  change (∃ n : ℕ, 0<n ∧ v.finalValue R N b g cap t n=0) ↔
    IsSquare ((u.P^2-1)*u.K^2+1) ∧ IsSquare (u.D*u.F*v.I R N b g cap) ∧ u.J ∣ u.Q ∧
      0 < v.margin R N b g cap t
  rw [← hf]
  constructor
  · rintro ⟨n,hn,hz⟩
    obtain ⟨nu,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    exact ⟨nu, by simpa only [v.finalValue_succ, FreeVars.V0, FreeVars.V1, FreeVars.Qstar, u] using hz⟩
  · rintro ⟨nu,hz⟩
    exact ⟨nu+1,by omega,by simpa only [v.finalValue_succ, FreeVars.V0, FreeVars.V1, FreeVars.Qstar, u] using hz⟩

namespace FreeVars

/-- Transport of the four conditions after the margin has recovered phi. -/
theorem conditions_toRatio {R N b g cap t : ℕ} (v : FreeVars)
    (hphi : 0 ≤ (v.C:ℤ)-(2*(R:ℤ)+1)-(b:ℤ)*v.w)
    (hscale : cap=32*t) (hc : v.Conditions R N b g cap t) :
    (v.toRatio R b).Conditions R N b g cap := by
  obtain ⟨ha,hb,hd,hm⟩ := hc
  unfold NativeNineRatio52.NewVars.Conditions
  rw [v.toRatio_base hphi, v.toRatio_I hphi, v.toRatio_margin hphi]
  refine ⟨ha,hb,hd,?_⟩
  rw [← v.margin_scale R N b g cap t hscale]
  positivity

/-- Retain the actual carrier of a completed old numerical construction. -/
def ofRatio (v : NativeNineRatio52.NewVars) (R b : ℕ) : FreeVars :=
  ⟨v.h,v.s,v.w,2*R+1+b*v.w+v.phi,v.i,v.j⟩

theorem base_ofRatio (v : NativeNineRatio52.NewVars) (R N b g cap : ℕ) :
    (ofRatio v R b).base R N b g cap = v.base R N b g cap := by
  unfold ofRatio base NativeNineRatio52.NewVars.base NativeNineRatio52.NewVars.old Nine.Vars.ofNat
  congr 1
  push_cast
  ring

theorem H_ofRatio (v : NativeNineRatio52.NewVars) (R N b g cap : ℕ) :
    (ofRatio v R b).H R N b g cap = v.Hnew R N b g cap := by
  unfold H NativeNineRatio52.NewVars.Hnew
  rw [base_ofRatio]
  rfl

theorem I_ofRatio (v : NativeNineRatio52.NewVars) (R N b g cap : ℕ) :
    (ofRatio v R b).I R N b g cap = v.Inew R N b g cap := by
  unfold I NativeNineRatio52.NewVars.Inew
  rw [base_ofRatio,H_ofRatio]

theorem oldMargin_ofRatio (v : NativeNineRatio52.NewVars) (R N b g cap : ℕ) :
    (ofRatio v R b).oldMargin R N b g cap = v.margin R N b g cap := by
  unfold oldMargin NativeNineRatio52.NewVars.margin
  rw [base_ofRatio]
  change ((v.base R N b g cap).K^2-4*((v.base R N b g cap).C-
    (v.base R N b g cap).K*(v.base R N b g cap).Y)^2)*(cap:ℤ)-
    8*(g:ℤ)*(v.base R N b g cap).K^2 =
    (v.base R N b g cap).K^2*(cap:ℤ)-4*((v.base R N b g cap).C-
    (v.base R N b g cap).K*(v.base R N b g cap).Y)^2*(cap:ℤ)-8*(g:ℤ)*(v.base R N b g cap).K^2
  ring

theorem conditions_ofRatio {R N b g cap t : ℕ} (v : NativeNineRatio52.NewVars)
    (hscale : cap=32*t) (hc : v.Conditions R N b g cap) :
    (ofRatio v R b).Conditions R N b g cap t := by
  obtain ⟨ha,hb,hd,hm⟩ := hc
  unfold Conditions
  rw [base_ofRatio,I_ofRatio]
  refine ⟨ha,hb,hd,?_⟩
  have he := (ofRatio v R b).margin_scale R N b g cap t hscale
  rw [oldMargin_ofRatio] at he
  linarith only [he,hm]

end FreeVars

/-- A free-carrier zero yields exactly the existing numerical Jones conclusion. -/
theorem ratio_sound {R N b g cap t : ℕ} (v : FreeVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b≤R) (hb : 0<b) (hbN : b≤N)
    (hcap : 0<cap) (hscale : cap=32*t)
    (hh : 0<v.h) (hs : 0<v.s) (hw : 0<v.w) (hC : 0<v.C) (hi : 0<v.i)
    (hz : ∃ n : ℕ, 0<n ∧ v.finalValue R N b g cap t n=0) :
    N^2 ∣ (2*R).choose R ∧ (∃ k,b=2^k) ∧ 8*g<cap := by
  have hbounds := register_bounds (g:=g) (cap:=cap) v hR hN hb hbN hh hs hw hC hi
  have hc := (exists_finalValue_zero_iff v hbounds hcap hscale).mp hz
  have hrange := carrier_range_of_margin_pos v hbounds hcap hscale hc.2.2.2
  have hphi := v.phi_nonneg_of_range hrange
  exact NativeNineRatio52.ratio_sound_new (v.toRatio R b) hR hN hbR hb hbN hcap
    hh hs hw hi (v.conditions_toRatio hphi hscale hc)

/-- Existing numerical completeness produces the free carrier and a positive
shifted final coordinate, without restricting the nonnegative CRT index. -/
theorem ratio_complete {R N b g cap t : ℕ}
    (hR : 8≤R) (hN : 8≤N) (hbR : b≤R) (hb : 0<b) (hbN : b≤N)
    (hscale : cap=32*t) (hgcap : 32*g<cap)
    (hdvd : N^2 ∣ (2*R).choose R) (hpow : ∃ k,b=2^k) :
    ∃ v : FreeVars, 0<v.h ∧ 0<v.s ∧ 0<v.w ∧ 0<v.C ∧ 0<v.i ∧
      ∃ n : ℕ, 0<n ∧ v.finalValue R N b g cap t n=0 := by
  obtain ⟨u,hh,hs,hw,hi,hc⟩ := NativeNineRatio52.ratio_complete_new hR hN hbR hb hbN hgcap hdvd hpow
  let v := FreeVars.ofRatio u R b
  have hC : 0<v.C := by change 0<2*R+1+b*u.w+u.phi; omega
  have hbounds := register_bounds (g:=g) (cap:=cap) v hR hN hb hbN hh hs hw hC hi
  refine ⟨v,hh,hs,hw,hC,hi,?_⟩
  exact (exists_finalValue_zero_iff v hbounds (by omega) hscale).mpr (FreeVars.conditions_ofRatio u hscale hc)

/-- Primitive hypotheses suffice for the full positive-final-witness equivalence. -/
theorem exists_finalValue_zero_iff_conditions {R N b g cap t : ℕ} (v : FreeVars)
    (hR : 8≤R) (hN : 8≤N) (hb : 0<b) (hbN : b≤N)
    (hcap : 0<cap) (hscale : cap=32*t)
    (hh : 0<v.h) (hs : 0<v.s) (hw : 0<v.w) (hC : 0<v.C) (hi : 0<v.i) :
    (∃ n : ℕ, 0<n ∧ v.finalValue R N b g cap t n=0) ↔ v.Conditions R N b g cap t :=
  exists_finalValue_zero_iff v (register_bounds v hR hN hb hbN hh hs hw hC hi) hcap hscale

/-- The integer data is exactly the shifted two-square norm of the proposal. -/
theorem finalValue_eq (v : FreeVars) (R N b g cap t n : ℕ) :
    let u := v.base R N b g cap
    let omega := u.J*v.margin R N b g cap t
    let theta := u.J*((n:ℤ)+u.W^2)+u.Q-omega*(v.V0 R N b g cap+v.V1 R N b g cap)
    v.finalValue R N b g cap t n =
      (theta^2-omega^2*(((u.P^2-1)*u.K^2+1)+64*(u.D*u.F*v.I R N b g cap)))^2-
        256*omega^4*((u.P^2-1)*u.K^2+1)*(u.D*u.F*v.I R N b g cap) := by
  dsimp [FreeVars.finalValue,NearSquareFinalizer.norm]
  ring

end DiophantineConsistency.FreeCarrierRatio

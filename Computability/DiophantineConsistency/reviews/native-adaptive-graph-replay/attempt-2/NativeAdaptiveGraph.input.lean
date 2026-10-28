import DiophantineConsistency.NativeAdaptiveSourceRestoration
import DiophantineConsistency.NativeAdaptiveUnitFactors

/-! The literal unrestricted-J thirteen-input graph, in its delivered gate order.
The fixed ports are beta,K,MC,MF_source; the fourth port is already shifted.
Its signed zero condition supplies the four actual carrier equations. The
positive-source endpoint derives, rather than assumes, every restored index.
This file makes no degree, operation optimality, converse or consistency claim. -/
set_option autoImplicit false
set_option Ela(b).async false
namespace DiophantineConsistency.NativeAdaptiveGraph

structure Core (A : Type*) where
  qm : A
  q : A
  q3 : A
  C : A
  E : A
  k : A
  c : A
  a : A
  H : A
  delta : A
  ell : A
  U : A
  Bt : A
  rank : A
  V : A
  y : A
  I : A
  Z : A
  M : A
  W : A
  Dstar : A
  A0 : A
  A1 : A
  Fs : A
  Fa : A
  out : A

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Every paid gate below follows the inert p13_free_J.json, with no coefficient shift. -/
def core (ports : Fin 4 → A) (x : Fin 13 → A) : Core A :=
  -- BEGIN INPUT ALIASES
  let J := x 0
  let F := x 1
  let alpha := x 2
  let f := x 3
  let i := x 4
  let T := x 5
  let X := x 6
  let Y := x 7
  let r := x 8
  let eta := x 9
  let zeta := x 10
  let u := x 11
  let gamma := x 12
  let beta := ports 0
  let K0 := ports 1
  let MC := ports 2
  let MF := ports 3
  -- END INPUT ALIASES
  -- BEGIN LITERAL GRAPH
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let a := E + Y
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let g19 := a * c
  let b0 := X + g19
  let ell := E * kY
  let g22 := k * qm
  let W := 1 + g22
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let g32 := M * g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let g35 := W * q3
  let g36 := Bt * g35
  let Z := g34 - g36
  let g38 := Z * Z
  let g39 := M * M
  let g40 := ell * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
  let A0 := g38 - g42
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - R
  let r0 := g52 - 1
  let g54 := U * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := U * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := U * U
  let g63 := Delta * c2
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := f2 - 1
  let Q := Delta * rho
  let I := c2 * i
  let g71 := I * I
  let g72 := g71 - Q
  let Fs := 1 + g72
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let F0 := 1 + A0
  let F1 := 1 + A1
  let g86 := F0 * F1
  let g87 := Fa * g86
  let g88 := Fs * g87
  let P13 := g88 - 1
  -- END LITERAL GRAPH
  { qm:=qm, q:=q, q3:=q3, C:=C, E:=E, k:=k, c:=c, a:=a, H:=H, delta:=Delta, ell:=ell, U:=U, Bt:=Bt, rank:=R, V:=V, y:=g78, I:=I, Z:=Z, M:=M, W:=W, Dstar:=Dstar, A0:=A0, A1:=A1, Fs:=Fs, Fa:=Fa, out:=P13 }

def value (ports : Fin 4 → A) (x : Fin 13 → A) : A := (core ports x).out

theorem value_map (phi : A →+* B) (ports : Fin 4 → A) (x : Fin 13 → A) :
    phi (value ports x) = value (fun j => phi (ports j)) (fun j => phi (x j)) := by
  simp only [value, core, map_add, map_mul, map_sub, map_one, map_ofNat]

noncomputable def polynomial (ports : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (ports j)) MvPolynomial.X

theorem eval_polynomial (ports : Fin 4 → ℤ) (x : Fin 13 → ℤ) :
    MvPolynomial.eval x (polynomial ports) = value ports x := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval x) (fun j => MvPolynomial.C (ports j)) MvPolynomial.X

section Shapes
variable (ports : Fin 4 → ℤ) (x : Fin 13 → ℤ)
local notation "b" => core ports x

theorem q_eq : (b).q=ports 0*x 0+1 := by change 1+x 0*ports 0=_;ring
theorem q_sub_one : (b).q-1=(b).qm := by change (1+(b).qm)-1=(b).qm;ring
theorem q3_eq : (b).q3=(b).q^3 := by change (b).q*((b).q*(b).q)=(b).q^3;ring
theorem k_eq : (b).k=x 9+x 10 := rfl
theorem c_eq : (b).c=(b).k*x 7+x 9 := by change x 9+x 7*(b).k=_;ring
theorem a_eq : (b).a=x 7*(x 6+1) := by change x 6*x 7+x 7=_;ring
theorem H_eq : (b).H=4*(b).a+3 := by change 3+4*(b).a=_;ring
theorem delta_eq : (b).delta=((b).a+2)^2-1 := by change (3+4*(b).a)+(b).a*(b).a=_;ring
theorem ell_eq : (b).ell=x 6*(b).k*(x 7)^2 := by change (x 6*x 7)*(x 7*(b).k)=_;ring
theorem U_eq : (b).U=(b).q^2*x 7 := by change x 7*((b).q*(b).q)=_;ring
theorem M_eq : (b).M=(b).q^3*((b).q-1) := by
  change (b).q3*(b).qm=_
  rw [q3_eq,←q_sub_one]
theorem W_eq : (b).W=((b).q-1)*(b).k+1 := by
  change 1+(b).k*(b).qm=_
  rw [←q_sub_one];ring

theorem Bt_eq : (b).Bt=((b).q*ports 1+x 6)*((b).q-x 1-x 2)-(b).q*x 1 := by
  change ((b).q-x 1-x 2)*(x 6+ports 1*(b).q)-x 1*(b).q=_
  ring

theorem rank_eq : (b).rank=NativeAdaptiveMainBootstrap.target (b).q (x 1) (x 2)
    (x 0) (ports 2) (ports 3) := by
  change (x 2+((b).q-x 1)*(b).qm)*((b).q*(b).q-1)+x 0*(ports 2+ports 3*(b).q)=_
  rw [←q_sub_one]
  unfold NativeAdaptiveMainBootstrap.target
  ring

theorem firstZ_eq : (b).Z=NativeAdaptiveCarrierBootstrap.firstZ (b).q (b).ell (b).k
    (x 8) (x 7) (b).Bt := by
  change (b).M*((b).ell+(b).k+x 8)+x 7*(b).qm-(b).Bt*((b).W*(b).q3)=_
  rw [M_eq,W_eq,q3_eq,←q_sub_one]
  unfold NativeAdaptiveCarrierBootstrap.firstZ
  ring

theorem A0_eq : (b).A0=NativeAdaptiveCarrierBootstrap.firstA0 (b).q (b).ell (b).k
    (x 8) (x 7) (b).Bt := by
  change (b).Z*(b).Z-((b).M*(b).M)*(1+(b).ell*((b).ell+(b).k))=_
  rw [firstZ_eq,M_eq]
  unfold NativeAdaptiveCarrierBootstrap.firstA0
  ring

theorem Dstar_eq : (b).Dstar=NativeAdaptiveMainBootstrap.mainDstar (b).q (x 6) (x 7)
    (b).k (x 9) (x 12) ((b).k-(b).rank-1) := by
  change (b).U*(x 6+(b).a*(b).c)+(b).H*((b).U*x 12+(x 6*x 7)*(b).q-((b).k-(b).rank-1))=_
  rw [U_eq,H_eq,a_eq,c_eq]
  unfold NativeAdaptiveMainBootstrap.mainDstar
  ring

theorem A1_eq : (b).A1=NativeAdaptiveMainBootstrap.mainA1 (b).q (x 6) (x 7)
    (b).k (x 9) (x 12) ((b).k-(b).rank-1) := by
  change (b).Dstar*(b).Dstar-((b).U*(b).U)*(1+(b).delta*((b).c*(b).c))=_
  rw [Dstar_eq,U_eq,delta_eq,a_eq,c_eq]
  unfold NativeAdaptiveMainBootstrap.mainA1
  ring

theorem V_eq : (b).V=NativeAdaptiveStrongIndex.auxiliaryValue (b).c (x 3) (x 5) (b).rank := by
  change (x 3*x 3)*(x 5*(b).c-(b).rank)-(b).c=_
  unfold NativeAdaptiveStrongIndex.auxiliaryValue
  ring

theorem Fs_eq : (b).Fs=NativeAdaptiveStrongIndex.strongFactor (b).a (b).c (x 3) (x 4) := by
  change 1+(((b).c*(b).c*x 4)*((b).c*(b).c*x 4)-(b).delta*(x 3*x 3-1))=_
  rw [delta_eq]
  unfold NativeAdaptiveStrongIndex.strongFactor
  ring

theorem Fa_eq : (b).Fa=NativeAdaptiveStrongIndex.auxiliaryFactor (b).a (b).c
    (x 3) (x 5) (b).rank (x 11) := by
  change ((b).V+x 11)*((b).V+x 11)-((b).delta*(x 3*x 3-1))*
    (((b).V+x 11)*((b).V+x 11)-(b).V*(b).V)=_
  rw [delta_eq,V_eq]
  unfold NativeAdaptiveStrongIndex.auxiliaryFactor
  ring
end Shapes

section Signed
variable (ports : Fin 4 → ℤ) (x : Fin 13 → ℤ)
local notation "b" => core ports x
open NativeAdaptiveUnitFactors

/-- No positivity is used to exclude hidden negative unit factors. -/
theorem value_zero_iff_factors : value ports x=0 ↔
    (b).A0=0 ∧ (b).A1=0 ∧ (b).Fs=1 ∧ (b).Fa=1 := by
  have hfirst : 1+(b).A0=firstFactor (b).q (b).Z (1+(b).ell*((b).ell+(b).k)) := by
    change 1+((b).Z*(b).Z-((b).M*(b).M)*(1+(b).ell*((b).ell+(b).k)))=_
    rw [M_eq]
    unfold firstFactor
    ring
  have hmain : 1+(b).A1=mainFactor (b).U (b).a (b).c (b).Dstar := by
    change 1+((b).Dstar*(b).Dstar-((b).U*(b).U)*(1+(b).delta*((b).c*(b).c)))=_
    rw [delta_eq]
    unfold mainFactor
    ring
  have hstrong : (b).Fs=strongFactor (b).a (x 3) (b).I := by
    change 1+((b).I*(b).I-(b).delta*(x 3*x 3-1))=_
    rw [delta_eq]
    unfold strongFactor
    ring
  have haux : (b).Fa=auxFactor (b).a (x 3) (b).V (b).y := by
    change (b).y*(b).y-((b).delta*(x 3*x 3-1))*((b).y*(b).y-(b).V*(b).V)=_
    rw [delta_eq]
    unfold auxFactor
    ring
  have tail : value ports x=(1+(b).A0)*(1+(b).A1)*(b).Fa*(b).Fs-1 := by
    change (b).Fs*((b).Fa*((1+(b).A0)*(1+(b).A1)))-1=_
    ring
  rw [tail,sub_eq_zero,hfirst,hmain,haux,hstrong,product_one_iff,
    ←hfirst,←hmain,←haux,←hstrong]
  constructor
  · rintro ⟨h0,h1,ha,hs⟩
    exact ⟨by omega,by omega,hs,ha⟩
  · rintro ⟨h0,h1,hs,ha⟩
    exact ⟨by omega,by omega,ha,hs⟩

/-- The four hypotheses consumed by actual source restoration are literal cuts. -/
theorem value_zero_iff_cuts : value ports x=0 ↔
    NativeAdaptiveCarrierBootstrap.firstA0 (b).q (x 6*(b).k*(x 7)^2) (b).k
      (x 8) (x 7) (b).Bt=0 ∧
    NativeAdaptiveMainBootstrap.mainA1 (b).q (x 6) (x 7) (b).k (x 9) (x 12)
      ((b).k-(b).rank-1)=0 ∧
    NativeAdaptiveStrongIndex.strongFactor (x 7*(x 6+1)) ((b).k*x 7+x 9) (x 3) (x 4)=1 ∧
    NativeAdaptiveStrongIndex.auxiliaryFactor (x 7*(x 6+1)) ((b).k*x 7+x 9)
      (x 3) (x 5) (b).rank (x 11)=1 := by
  rw [value_zero_iff_factors,A0_eq,A1_eq,Fs_eq,Fa_eq,ell_eq,a_eq,c_eq]
end Signed

/-- Every positive zero restores the actual31 positive source coordinates and
all22 source rows. No source, index, rank or power conclusion is assumed. -/
theorem positive_zero_source (ports : Fin 4 → ℤ)
    (hp : NativePellBootstrap.PortBox ports) {d : ℕ}
    (hd : 4≤d) (hbeta : ports 0=(2:ℤ)^d-1)
    (x : Fin 13 → ℤ) (hx : ∀ j, 0<x j) (hz : value ports x=0) :
    let b := core ports x
    ∃ s : Fin 31 → ℕ, (∀ j, 0<s j) ∧
      (∀ j, SplitCertificate59.sourceRows ports (fun k => (s k:ℤ)) j=0) ∧
      (s 0:ℤ)=x 0 ∧ (s 1:ℤ)=x 1 ∧ (s 2:ℤ)=x 2 ∧
      (s 4:ℤ)=x 3 ∧ (s 6:ℤ)=x 4 ∧ (s 12:ℤ)=x 9 ∧ (s 13:ℤ)=x 10 ∧
      (s 21:ℤ)=x 6 ∧ (s 26:ℤ)=(b).V ∧ (s 14:ℤ)=(b).V+x 11 ∧
      NativePellBootstrap.nativeRank s=(b).rank := by
  obtain ⟨h0,h1,hs,ha⟩ := (value_zero_iff_cuts ports x).mp hz
  have out := NativeAdaptiveSourceRestoration.adaptive_positive_source ports hp hd hbeta
    (hx 0) (hx 1) (hx 2) (hx 6) (hx 7) (hx 9) (hx 10) (hx 12) (hx 8)
    (hx 3) (hx 4) (hx 5) (hx 11) (k_eq ports x) (q_eq ports x)
    (rank_eq ports x) (Bt_eq ports x) h0 h1 hs ha
  simpa only [←c_eq ports x,←V_eq ports x] using out

end DiophantineConsistency.NativeAdaptiveGraph

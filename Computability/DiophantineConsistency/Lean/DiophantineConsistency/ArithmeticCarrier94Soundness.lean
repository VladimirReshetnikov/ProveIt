import DiophantineConsistency.ArithmeticCarrier94Indices
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticHalfBinomial2011
import DiophantineConsistency.ArithmeticWindowInterface
import DiophantineConsistency.ArithmeticCellWindow

/-! # Soundness of the 14-positive 67/94 equation, from its five equations

`OrdinaryEquations` is the maintained `ArithmeticCarrierSoundness2011.Equations`
with the ordinary strong norm `(i c²)² + Delta = Delta f²` and auxiliary
parameter `I = i c²`. The maintained power, population and window clients
use the strong norm only through `maintained_first_indices`, whose conclusion
`ArithmeticCarrier94Indices.ordinary_first_indices` reproduces exactly. The
proofs below are therefore verbatim copies of
`ArithmeticPellPowerRecovery.maintained_power`,
`ArithmeticCarrierRadix2011.power_of_equations` and `radix_of_power`,
`ArithmeticHalfBinomial2011.population_of_equations` and
`ArithmeticWindowInterface.window_of_equations` (with its two private helpers),
changing only the strong hypothesis and that one call. Each copy keeps its
source file's `open`s in its own section. `ordinary_halts`: in every model of
`𝗜𝚺₁`, positive coordinates satisfying the five equations make the decimal215
machine halt. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrier94Soundness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

/-- The five equations of a positive 67/94 zero: the maintained ones with the
ordinary strong norm `(i c²)² + Delta = Delta f²` and auxiliary parameter `I = i c²`. -/
def OrdinaryEquations (beta K MC MF : V) (v : Fin 14 → V) : Prop :=
  let J:=v 0; let F:=v 1; let alpha:=v 2; let z:=v 3
  let f:=v 4; let i:=v 5; let T:=v 6; let s:=v 7; let w:=v 8
  let N:=v 9; let eta:=v 10; let zeta:=v 11; let y:=v 12; let gamma:=v 13
  let q:=beta*J+1; let X:=w*q; let Y:=s*q^3; let E:=X*Y
  let k:=eta+zeta; let c:=k*Y+eta; let a:=E+Y
  let delta:=(a+1)*(a+3); let d:=X+a*c+gamma*(4*a+3)
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let tau:=E*N+k-R; let I:=i*c*c
  let u:=(f*f*c*T-(f*f*R+c))+((f*f*R+c)-f*f*c*T)
  (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 ∧
  tau*tau=1+(E*Y)*(E*Y+1)*k*k ∧ d*d=1+delta*c*c ∧
  (i*c*c)*(i*c*c)+delta=delta*f*f ∧ I*I*u*u+y*y=1+I*I*y*y

end

section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstIndex ArithmeticPellHalfIndex
open ArithmeticPellPowerRecovery

theorem ordinary_power (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)
    (hbeta : 15≤beta) (hMC : MC<beta) (hMF : MF<2*beta)
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha) (hz : 0<z)
    (hf : 0<f) (hi : 0< i) (hT : 0<T) (hs : 0<s) (hw : 0<w)
    (hN : 0<N) (heta : 0<eta) (hzeta : 0<zeta) (hy : 0<y) (hgamma : 0<gamma) :
    let q:=beta*J+1
    let X:=w*q
    let Y:=s*q^3
    let E:=X*Y
    let k:=eta+zeta
    let c:=k*Y+eta
    let a:=E+Y
    let d:=X+a*c+gamma*(4*a+3)
    let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
    let tau:=E*N+k-R
    let I:=i*c*c
    let u:=absdiff (f*f*c*T) (f*f*R+c)
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    tau*tau=1+(E*Y)*(E*Y+1)*k*k →
    d*d=1+delta a*c*c →
    (i*c*c)*(i*c*c)+delta a=delta a*f*f →
    I*I*u*u+y*y=1+I*I*y*y →
    X=Exp.exp R ∧ Exponential R X ∧ Exp.exp R<Y := by
  dsimp only
  intro ht hn hm hf' hu
  let q:=beta*J+1
  let X:=w*q
  let Y:=s*q^3
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let k:=eta+zeta
  let c:=k*Y+eta
  let a:=X*Y+Y
  let d:=X+a*c+gamma*(4*a+3)
  have hb : 0<beta := lt_of_lt_of_le (by simp : (0:V)<15) hbeta
  obtain ⟨n,h,hn5,_,hnR,_,hk,hd,hc,_,_,_,_⟩ :=
    ArithmeticCarrier94Indices.ordinary_first_indices beta K MC MF J F alpha z f i T s w N eta zeta y gamma
      hb hMC hMF hJ hF halpha hz hf hi hT hs hw hN heta hzeta hy hgamma ht hn hm hf' hu
  change k=2*ycoord n (2*(X*Y*Y-1)+1) at hk
  change d=xcoord R a at hd
  change c=ycoord R a at hc
  change 2*n=R+1 at hnR
  have hq16 : (16:V)≤q := calc
    16=15+1 := by ring
    _≤beta+1 := add_le_add_left hbeta 1
    _≤beta*J+1 := add_le_add_left (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hJ)) 1
  have hX : (16:V)≤X := le_trans hq16 (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hw))
  have hq1 : 1≤q := le_trans (by simp : (1:V)≤16) hq16
  have hY : 1≤Y := by
    dsimp [Y]
    have hq3 : 1≤q^3 := by simpa only [show q^3=q*q*q by ring] using one_le_mul (one_le_mul hq1 hq1) hq1
    exact one_le_mul (pos_iff_one_le.mp hs) hq3
  let r:=n-1
  have hn1 : 1≤n := le_trans (by simp : (1:V)≤5) hn5
  have hrn : r+1=n := tsub_add_cancel_of_le hn1
  have hr : (2:V)≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrn,show (2:V)+1=3 by ring]
    exact le_trans (by simpa only [show (3:V)+2=5 by ring] using (show (3:V)≤3+2 by simp)) hn5
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      R+1=2*n := hnR.symm
      _=(2*r+1)+1 := by rw [←hrn]; ring
  have ha : a=Y*(X+1) := by dsimp [a]; ring
  have hbound : Exp.exp R<Y := by
    rw [hR]
    apply power_bound X Y r k c eta zeta hX hY hr rfl rfl hzeta
    · simpa only [ha,hR] using hc
    · simpa only [hrn] using hk
  have hp : X=Exp.exp R := power_of_coordinates X Y R c d gamma hbound
    (by simpa only [ha] using hc) (by simpa only [ha] using hd)
    (by rw [←ha])
  exact ⟨hp,by change Exponential R X; rw [hp]; exact exponential_exp R,hbound⟩

end

section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

theorem power_of_ordinary (v : Fin 14 → V) (hv : ∀j,0<v j)
    (he : OrdinaryEquations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v) :
    X v=Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v)<Y v := by
  obtain ⟨hb,hl,hh⟩:=current_bounds (V:=V)
  obtain ⟨ht,hn,hm,hf,hu⟩:=he
  exact ordinary_power
    (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) hb hl hh
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
    (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu


theorem radix_of_power (v : Fin 14 → V) (hJ : 0<v 0)
    (hp : X v=Exp.exp (rank v)) : Radix v := by
  have he : Exp.exp (rank v)=v 8*((Exp.exp (CurrentMasks2011.width:V)-1)*v 0+1) := by
    simpa only [X, q, current_beta_exp (V:=V)] using hp.symm
  obtain ⟨_,L,hL,hq,hbound,hw⟩:=ArithmeticRadixAlignment.factor_alignment
    (CurrentMasks2011.width:V) (v 0) (rank v) (v 8) (current_width (V:=V)).2 hJ he
  have hq' : q v=Exp.exp ((CurrentMasks2011.width:V)*L) := by
    simpa only [q,current_beta_exp (V:=V)] using hq
  exact ⟨L,hL,hq',hbound,hw,by rw [hq']; exact exponential_exp _,
    by rw [hw]; exact exponential_exp _⟩

end

section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticBinaryPopulation ArithmeticHalfBinomial
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticHalfBinomial2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

theorem population_of_ordinary (v : Fin 14 → V) (hv : ∀j,0<v j)
    (he : OrdinaryEquations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hp : X v=Exp.exp (rank v)) (h : V) (hq : q v=Exp.exp h) :
    3*h+2≤population (rank v) := by
  obtain ⟨hb,hl,hh⟩ := current_bounds (V:=V)
  have hb0 : (0:V)<(CurrentMasks2011.beta:V) := lt_of_lt_of_le (by simp) hb
  obtain ⟨ht,hn,hm,hf,hu⟩ := he
  obtain ⟨n,_,hn5,_,hnR,_,hk,_,hc,_,_,_,_⟩ :=
    ArithmeticCarrier94Indices.ordinary_first_indices
    (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) hb0 hl hh
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
    (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu
  change v 10+v 11=2*ycoord n (2*(X v*Y v*Y v-1)+1) at hk
  change (v 10+v 11)*Y v+v 10=ycoord (rank v) (X v*Y v+Y v) at hc
  change 2*n=rank v+1 at hnR
  obtain ⟨r,hrn,hr4,hR⟩ := half_index_of_ge_five n (rank v) hn5 hnR
  have hXe : X v=Exp.exp (2*r+1) := by rw [hp,hR]
  have hY : 1≤Y v := by
    unfold Y
    have hq1 : 1≤q v := by unfold q; exact le_add_of_nonneg_left (by simp)
    exact one_le_mul (pos_iff_one_le.mp (hv 7)) (by
      simpa only [show (q v)^3=q v*q v*q v by ring] using one_le_mul (one_le_mul hq1 hq1) hq1)
  have hck : ycoord (2*r+1) (Y v*(X v+1))=2*ycoord (r+1) (2*(X v*Y v*Y v-1)+1)*Y v+v 10 := by
    rw [show Y v*(X v+1)=X v*Y v+Y v by ring,←hR,←hc,hrn,←hk]
  obtain ⟨w,hw⟩ := half_binomial (X v) (Y v) r (v 10) (v 11) hr4 hXe hY hck
    (by rw [hrn,←hk]) (hv 10) (hv 11)
  have hYq : Exp.exp (3*h)∣Y v := by
    refine ⟨v 7,?_⟩
    unfold Y
    rw [hq,show 3*h=h+h+h by ring,exp_add,exp_add]
    ring
  have h3 := three_h_lt_rank v hv h hq
  rw [hR] at h3 ⊢
  exact population_lower (X v) (Y v) r w h hXe hw hYq h3

end

section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticWindowInterface
open ArithmeticWindowCarry ArithmeticCyclicWord ArithmeticMaskConstants ArithmeticWindowBits
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

private theorem raw_eq {N W C : V} (hn : 0 < 2011*N) (hC : C < Exp.exp (47*(2011*N)))
    {k : V} (hk : k < 2011*N) :
    raw 47 (coeff W) (word N W C) k = rawDigit N W C k := by
  have hd : ∀ e : V, dig 47 (rot 47 (2011*N) C (e % (2011*N))) k = dig 47 C (cyc (2011*N) k e) :=
    fun e => by rw [dig_rot 47 _ C _ k (mod_lt e hn) hk hC, cyc_mod _ _ _ hn]
  unfold raw rawDigit
  rw [Fintype.sum_option, add_comm]
  simp only [coeff, word, shift, hd]

private theorem mass_bound (W : V) :
    (∑ i, coeff W i) + 1 ≤ (57+1) * (Exp.exp (47:V) - 1) := by
  rw [Fintype.sum_option]
  simp only [coeff]
  rw [kernel_mass]
  have h47 : W % 47 ≤ 46 := lt_succ_iff_le.mp (by
    simpa only [show (46 : V) + 1 = 47 by norm_num] using mod_lt W (show (0 : V) < 47 by norm_num))
  have hE46 : Exp.exp (46:V) = ((2^46:ℕ):V) := by
    have := cast_exp (V:=V) 46
    rwa [Nat.cast_ofNat] at this
  have hE47 : Exp.exp (47:V) = ((2^47:ℕ):V) := by
    have := cast_exp (V:=V) 47
    rwa [Nat.cast_ofNat] at this
  have hφ : Exp.exp (W % 47) ≤ ((2^46:ℕ):V) := by
    rw [← hE46]; exact exp_monotone_le.mpr h47
  have hcast : ((58 * (2^47 - 1) : ℕ) : V) = (57+1) * (((2^47:ℕ):V) - 1) := by
    have h1 : ((2^47 - 1 : ℕ) : V) + 1 = ((2^47 : ℕ) : V) := by
      have := Nat.sub_add_cancel (Nat.one_le_two_pow (n := 47))
      exact_mod_cast this
    rw [← h1, add_tsub_cancel_right, Nat.cast_mul]
    norm_num
  have hnat : ((2^46 + 7659829036801887 + 1 : ℕ) : V) ≤ ((58 * (2^47 - 1) : ℕ) : V) :=
    Nat.cast_le.mpr (by norm_num)
  rw [hE47]
  calc Exp.exp (W % 47) + 7659829036801887 + 1
      ≤ ((2^46:ℕ):V) + 7659829036801887 + 1 :=
        (add_le_add_iff_right 1).mpr ((add_le_add_iff_right _).mpr hφ)
    _ = ((2^46 + 7659829036801887 + 1 : ℕ) : V) := by push_cast; ring
    _ ≤ _ := hnat
    _ = _ := hcast

/-- **The internal arithmetic window**, from the five internal equations and the radix,
given the population lower bound of the rank as a hypothesis. -/
theorem window_of_ordinary (u : Fin 14 → V) (hu : ∀ j, 0 < u j)
    (he : OrdinaryEquations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) u)
    (hr : Radix u)
    (hσ : ∀ N : V, q u = Exp.exp (94517*N) → 3*(94517*N) + 2 ≤ population (rank u)) :
    ∃ N : V, q u = Exp.exp (94517*N) ∧
      Window N (rank u - 94517*N) (q u - u 1 - u 2) (u 1) := by
  obtain ⟨L, hL, hq, -, hw8, -, -⟩ := hr
  obtain ⟨ht, -, -, -, -⟩ := he
  obtain ⟨hb, hl, hh⟩ := current_bounds (V:=V)
  have hwid : (CurrentMasks2011.width:V) = 94517 := (current_width (V:=V)).1
  rw [hwid] at hq hw8
  refine ⟨L, hq, ?_⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = rank u - 94517*L := ⟨_, rfl⟩
  rw [← hWdef] at hw8 ⊢
  have ht' : ((CurrentKernel2011.K:V) + u 8) * q u + q u = ((CurrentKernel2011.K:V) + u 8) * (u 1 + u 2) + u 1 + u 3 * (q u - 1) + 1 := ht
  have hβ1 : 1 ≤ (CurrentMasks2011.beta:V) := le_trans (by norm_num) hb
  have hq2 : 2 ≤ q u := by
    show 2 ≤ (CurrentMasks2011.beta:V) * u 0 + 1
    have := one_le_mul_of_one_le_of_one_le hβ1 (pos_iff_one_le.mp (hu 0))
    calc (2:V) = 1 + 1 := by norm_num
      _ ≤ _ := (add_le_add_iff_right 1).mpr this
  have hgap := (ArithmeticPellFirstIndex.scalar_window (q u) (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
      ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (u 0) (u 1) (u 2) (u 3) (u 8) (u 7) (lt_of_lt_of_le (by norm_num) hb) (hu 0) (hu 1)
      (hu 2) (hu 3) (hu 8) (hu 7) hl hh rfl ht').1
  have hlt : u 1 + u 2 < q u := tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
  have hfour := ArithmeticSaturation.four_block (q u) (CurrentMasks2011.beta:V) (u 0) (u 1) (u 2)
    (CurrentMasks2011.lowPort:V) (CurrentMasks2011.highPort:V) rfl hgap (one_le_mul_of_one_le_of_one_le
      (pos_iff_one_le.mp highPort_pos)
      (pos_iff_one_le.mp (hu 0)))
  obtain ⟨C, hCdef⟩ : ∃ C, C = q u - u 1 - u 2 := ⟨_, rfl⟩
  rw [← hCdef]
  rw [← hCdef] at hgap hfour
  have hsum : u 1 + u 2 + C = q u := by
    rw [hCdef, tsub_tsub]; exact add_tsub_cancel_of_le (le_of_lt hlt)
  have hC1 : 1 ≤ C := pos_iff_one_le.mp hgap
  have hn : (0:V) < 2011*L := mul_pos (by norm_num) hL
  have hqP : q u = Exp.exp (47*(2011*L)) := by rw [hq]; congr 1; ring
  have hM : (0:V) < Exp.exp (47*(2011*L)) - 1 := by
    rw [← hqP]; exact tsub_pos_of_lt (lt_of_lt_of_le one_lt_two hq2)
  have hCq : C < q u :=
    lt_of_lt_of_le (lt_add_of_pos_left C (add_pos (hu 1) (hu 2))) (le_of_eq hsum)
  have hCP : C < Exp.exp (47*(2011*L)) := by rw [← hqP]; exact hCq
  have hFM : u 1 < q u - 1 := by
    apply lt_iff_succ_le.mpr
    apply le_tsub_of_add_le_right
    calc u 1 + 1 + 1 ≤ u 1 + u 2 + C :=
          add_le_add ((add_le_add_iff_left _).mpr (pos_iff_one_le.mp (hu 2))) hC1
      _ = q u := hsum
  -- the repunit
  have hβ : (CurrentMasks2011.beta:V) = Exp.exp (47*2011) - 1 := by
    rw [current_beta_exp, hwid]; norm_num
  have hJ : u 0 = rep (47*2011) L := by
    apply eq_rep_of_identity (by norm_num)
    rw [← hβ]
    calc (CurrentMasks2011.beta:V) * u 0 + 1 = q u := rfl
      _ = Exp.exp (47*2011*L) := by rw [hq]; congr 1; norm_num
  -- the four-block rank and saturation
  have hrank : rank u = C - 1 + ((CurrentMasks2011.lowPort:V) * u 0 + 1) + Exp.exp (94517*L) * (u 1 + ((CurrentMasks2011.highPort:V) * u 0 - 1)) +
      Exp.exp (94517*L) ^ 2 * (Exp.exp (94517*L) - 1 - (C - 1)) +
        Exp.exp (94517*L) ^ 3 * (Exp.exp (94517*L) - 1 - u 1) := by
    rw [← hq, ← hfour, rank, Nat.cast_add]
  have hMH : population ((CurrentMasks2011.lowPort:V) * u 0 + 1) + population ((CurrentMasks2011.highPort:V) * u 0 - 1) ≤ 94517*L + 2 := by
    rw [hJ, ArithmeticMaskPopulation.repeated_mask_population (47*2011) L (CurrentMasks2011.lowPort:V) (CurrentMasks2011.highPort:V) (by norm_num) hL
      lowPort_lt_exp highPort_lt_exp lowPort_even highPort_mod_eight
      (by rw [ports_population]; norm_num)]
    norm_num
  obtain ⟨hncC, hncF⟩ := ArithmeticSaturation.saturation (94517*L) (C - 1) (u 1)
    ((CurrentMasks2011.lowPort:V) * u 0 + 1) ((CurrentMasks2011.highPort:V) * u 0 - 1) (rank u)
    (lt_of_le_of_lt tsub_le_self (by rw [← hq]; exact hCq))
    (by rw [← hq]; exact lt_of_lt_of_le hFM tsub_le_self)
    hrank hMH (hσ L hq)
  rw [hJ] at hncC hncF
  -- the two mask tests
  have low := low_mask_decode 47 2011 L C (CurrentMasks2011.lowPort:V) inS (by norm_num) (by norm_num) hL lowPort_lt_exp
    lowPort_digit_in lowPort_digit_out inS_zero hC1 hncC
  have hmask := high_mask_digits 47 2011 L (u 1) (CurrentMasks2011.highPort:V) (by norm_num) hL highPort_lt_exp
    (by rw [highPort_digit_zero]; norm_num) hncF
  -- transport and the cyclic word identity
  obtain ⟨z, hz⟩ : ∃ z, u 3 = z + 1 :=
    ⟨u 3 - 1, (tsub_add_cancel_of_le (pos_iff_one_le.mp (hu 3))).symm⟩
  have hQ : q u - 1 + 1 = q u := tsub_add_cancel_of_le (le_trans (by norm_num) hq2)
  have htrans : ((CurrentKernel2011.K:V) + u 8) * C = u 1 + z * (q u - 1) := by
    have h1 : ((CurrentKernel2011.K:V) + u 8) * (u 1 + u 2) + (((CurrentKernel2011.K:V) + u 8) * C + (q u - 1) + 1) =
        ((CurrentKernel2011.K:V) + u 8) * (u 1 + u 2) + (u 1 + z * (q u - 1) + (q u - 1) + 1) := by
      calc _ = ((CurrentKernel2011.K:V) + u 8) * (u 1 + u 2 + C) + (q u - 1 + 1) := by ring
        _ = ((CurrentKernel2011.K:V) + u 8) * q u + q u := by rw [hsum, hQ]
        _ = ((CurrentKernel2011.K:V) + u 8) * (u 1 + u 2) + u 1 + u 3 * (q u - 1) + 1 := ht'
        _ = _ := by rw [hz]; ring
    exact add_right_cancel (add_right_cancel (add_left_cancel h1))
  have hKsum : (CurrentKernel2011.K:V) + u 8 = ∑ i, coeff W i * Exp.exp (47 * shift W i) := by
    rw [Fintype.sum_option, kernel_sum, hw8]
    simp only [coeff, shift]
    have hW : Exp.exp W = Exp.exp (W % 47) * Exp.exp (47 * (W / 47)) := by
      conv_lhs => rw [← div_add_mod W 47]
      rw [exp_add, mul_comm]
    rw [hW, add_comm]
  have hcongr : (∑ i, coeff W i * word L W C i) % (Exp.exp (47*(2011*L)) - 1) =
      u 1 % (Exp.exp (47*(2011*L)) - 1) := by
    have h := kernel_rotation_congr 47 (2011*L) C (coeff W) (shift W) hn hM
    rw [← hKsum, htrans, hqP, mod_add_mul _ _ hM] at h
    exact h.symm
  have hin : CarryInput 47 (2011*L) (u 1) 57 (coeff W) (word L W C) :=
    { n_pos := hn
      M_pos := hM
      word_lt := fun i => rot_lt 47 _ C _ (le_of_lt (mod_lt _ hn)) hCP
      boolean := fun i => rot_boolean 47 _ C _ (mod_lt _ hn) hCP low.boolean
      F_lt := by rw [← hqP]; exact hFM
      congr := hcongr
      mass := mass_bound W }
  have hcar := end_around_carry hin
  refine ⟨hL, low.boolean, low.origin, low.support, fun k hk => (hcar k hk).1,
    fun k hk => (hcar k hk).2.1, fun k hk => ?_, fun k hk => ?_, hmask.1, hmask.2⟩
  · have h := (hcar k hk).2.2.2
    rw [raw_eq hn hCP hk] at h
    exact h
  · have h := (hcar k hk).2.2.1
    rw [raw_eq hn hCP hk] at h
    exact h

end

section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCarrierRadix2011 ArithmeticWindowInterface

/-- **Positive coordinates satisfying the five 67/94 equations make the machine halt.** -/
theorem ordinary_halts (u : Fin 14 → V) (hu : ∀ j, 0 < u j)
    (he : OrdinaryEquations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) u) :
    ∃ t : V, first (ArithmeticMachineRun215.run t) = 0 := by
  have hp := power_of_ordinary u hu he
  have hr := radix_of_power u (hu 0) hp.1
  obtain ⟨N, -, hw⟩ := window_of_ordinary u hu he hr
    (fun N hqN => population_of_ordinary u hu he hp.1 _ hqN)
  obtain ⟨t, -, ht⟩ := ArithmeticCellWindow.window_halts hw
  exact ⟨t, ht⟩

end

end DiophantineConsistency.ArithmeticCarrier94Soundness

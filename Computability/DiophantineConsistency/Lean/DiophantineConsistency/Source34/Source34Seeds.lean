import DiophantineConsistency.Source34.Source34Rank
import DiophantineConsistency.Source34.Source34ConstructedRank
import DiophantineConsistency.Mixed121.Mixed121Seeds
import DiophantineConsistency.Compact44.CompactGenericStride
import DiophantineConsistency.Compact44.CompactFirstSeed
import DiophantineConsistency.Compact44.CompactAuxPositiveCoordinates
import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed
import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionSeed2011

/-! # The canonical halt data at the source34 ports

`Mixed121Seeds` at the source34 tuple, with the theorem names kept. The seed
lemmas (`ArithmeticOuterSeed`, `ArithmeticPellAuxiliarySeed`,
`CompactFirstSeed`, `CompactAuxPositiveCoordinates`, the γ correction) are
generic in `d = 121·8801`, and so are `Mixed121Seeds.AuxData`,
`PositiveAuxData` and `auxiliary_positive`, which are used directly.
Everything that mentions the rank or the masks is re-declared at
`Source34ConstructedRank.rank` and `Source34ConstructedRank.low`/`high`, and the
halt packing comes from `Source34Rank.halt_chosen_rank_no_high`.

`halt_first_gamma`: an internal halt of machine 215 at time `T` gives the
calibrated packing of the halt word at the source34 ports
(`PackingInput 1064921 (Source34Kernel.paramKernel ρ) MC MF_native`), the rank
residue `R ≡ d·w (mod d·N)`, a positive transport quotient `z` with
`(K + 2^(R−dN))·C = F + z·(q − 1)`, and all the Pell seeds (outer, auxiliary,
first carrier, γ). These are the canonical halt data from which the source34
converse assembles its witness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34Seeds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticPacking ArithmeticRepunit
  ArithmeticWindowDigits ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
  ArithmeticPellAuxiliarySeed ArithmeticAdaptiveConstructionCorrectionSeed2011
open CompactFirstSeed CompactAuxPositiveCoordinates
open Mixed121Kernel (rho)
open Source34Kernel Source34ConstructedRank Source34Rank Source34Word
open Mixed121Word (haltRow haltLength haltStride)
open Mixed121Column (perturb perturb_definable)
open Mixed121Rank (windowRank)
open Mixed121Seeds (AuxData PositiveAuxData auxiliary_positive)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho Source34Ports.lowNat Source34Ports.highNat
  Source34Ports.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## From `CompactRankResidueJoin` -/

theorem properties {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K low high N s X) :
    population (rank K N s X) = 3*(1064921*N)+2 ∧
      rank K N s X % 4 = 3 ∧ 2*(1064921*N) < rank K N s X := by
  exact rank_properties h (Source34ConstructedRank.packing_origin_mod_four h)
    Source34PulseBit.low_mod_four

theorem rank_eq_window (K N s : V) (X : V → V) [𝚺₁-Function₁ X] :
    rank K N s X = windowRank K N s
      ((low+Exp.exp (1064921*N)*(high+(Exp.exp (1064921:V)-1)))*rep 1064921 N) X := by
  rfl


/-! ## From `CompactPositiveTransport` -/

/-- Calibration remains explicit: the chosen power must have the packing
    rotation residue. The rank lower bound makes the shifted quotient positive. -/
theorem positive_shifted_transport {K N s R : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K low high N s X)
    (hbig : 2*(1064921*N)<R)
    (hmod : Exp.exp (R-1064921*N) % (Exp.exp (1064921*N)-1) =
      Exp.exp (1064921*s) % (Exp.exp (1064921*N)-1)) :
    let u := (1064921:V)*N
    let q := Exp.exp u
    let w := Exp.exp (R-u)
    let C := Cw 1064921 N X
    let F := Fw 1064921 K N s X
    ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ (K+w)*C=F+z*(q-1) := by
  let u : V := 1064921*N
  let q := Exp.exp u
  let w := Exp.exp (R-u)
  let C := Cw 1064921 N X
  let F := Fw 1064921 K N s X
  have huR : u≤R := le_of_lt (lt_of_le_of_lt
    (show u≤2*u by simpa only [two_mul] using le_add_of_nonneg_right (Arithmetic.zero_le u)) hbig)
  have hsub : u+(R-u)=R := add_tsub_cancel_of_le huR
  have hlt : u<R-u := by
    apply lt_of_add_lt_add_left (a := u)
    rw [hsub]
    simpa only [two_mul] using hbig
  have hqw : q*w=Exp.exp R := by
    dsimp only [q,w]
    rw [←exp_add,hsub]
  have hwq : q<w := exp_monotone.mpr hlt
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (one_le_exp _)
  have hC : 0<C := C_pos h
  have hF : F<q := lt_of_lt_of_le (F_lt_M h) tsub_le_self
  have hWle : w≤(K+w)*C := le_trans (le_add_of_nonneg_left (Arithmetic.zero_le K))
    (le_mul_of_one_le_right (Arithmetic.zero_le (K+w)) (pos_iff_one_le.mp hC))
  have hCF : F<(K+w)*C := lt_of_lt_of_le (lt_trans hF hwq) hWle
  have htr := packing_transport h w hmod
  let z := (K+w)*C/(q-1)
  have heq : (K+w)*C+q=(z+1)*(q-1)+1+F := calc
    _=((K+w)*C+(q-F))+F := by rw [add_assoc,tsub_add_cancel_of_le (le_of_lt hF)]
    _=(z+1)*(q-1)+1+F := by
      rw [htr]
      rfl
  have heq' : (K+w)*C+q=(F+z*(q-1))+q := calc
    _=(z+1)*(q-1)+1+F := heq
    _=(F+z*(q-1))+((q-1)+1) := by ring
    _=(F+z*(q-1))+q := by rw [hq1]
  have hshift : (K+w)*C=F+z*(q-1) := add_right_cancel heq'
  have hz : 0<z := by
    rcases zero_or_succ z with hz | ⟨t,ht⟩
    · rw [hz] at hshift
      simp at hshift
      exact False.elim ((ne_of_gt hCF) hshift)
    · rw [ht]
      exact lt_of_le_of_lt (Arithmetic.zero_le t) (lt_add_one t)
  exact ⟨z,hz,hqw,hshift⟩


/-! ## From `CompactCalibratedTransport` -/

theorem calibrated_transport {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K low high N s X) (hs0 : 0<s) (hsN : s<N)
    (hcal : rank K N s X % (1064921*N) = (1064921*s) % (1064921*N)) :
    let R := rank K N s X
    let q := Exp.exp ((1064921:V)*N)
    let w := Exp.exp (R-1064921*N)
    let C := Cw 1064921 N X
    let F := Fw 1064921 K N s X
    ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ (K+w)*C=F+z*(q-1) := by
  have hbig := (properties h).2.2
  have hstride := CompactGenericStride.stride (1064921:V) N s (rank K N s X)
    (by norm_num) hs0 hsN hcal hbig
  exact positive_shifted_transport h hbig hstride.2.2.2.2


/-! ## From `CompactFirstTransportSeed` -/

theorem first_from_transport {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K low high N s X)
    (sY n eta zeta gamma w z : V) (hsY : 0<sY) (hz : 0<z)
    (hseed : SeedRelations (1064921*N) (rank K N s X) sY n eta zeta gamma)
    (hqW : Exp.exp (1064921*N)*w=Exp.exp (rank K N s X))
    (htransport : (K+w)*Cw 1064921 N X = Fw 1064921 K N s X+
      z*(Exp.exp (1064921*N)-1)) :
    let q := Exp.exp ((1064921:V)*N)
    let R := rank K N s X
    let Y := sY*q^3
    let E := Exp.exp R*Y
    let k := eta+zeta
    let ell := E*Y*k
    let tau := E*n+k-R
    let C := Cw 1064921 N X
    let F := Fw 1064921 K N s X
    (q*K+Exp.exp R)*C = q*F+(q-1)*(q*z) ∧
    ∃ r : V, 0<r ∧
      (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
      (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*(q*z)) := by
  let u : V := 1064921*N
  let q := Exp.exp u
  have hu2 : (2:V)≤u := le_trans (by norm_num : (2:V)≤1064921)
    (le_mul_of_one_le_right (by norm_num) (pos_iff_one_le.mp (N_pos h)))
  have he2 : Exp.exp (2:V)=4 := by
    rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
    norm_num
  have hq4 : (4:V)≤q := by
    dsimp only [q]
    simpa only [he2] using (exp_monotone_le.mpr hu2)
  have hq : (2:V)≤q-1 := by
    apply le_tsub_of_add_le_left
    exact le_trans (by norm_num : (1:V)+2≤4) hq4
  have hb : (1:V)≤q*z := one_le_mul (one_le_exp _) (pos_iff_one_le.mp hz)
  have hphase := (properties h).2.1
  have hfirst := positive_first_of_seed u (rank K N s X) sY n eta zeta gamma (q*z)
    hsY hphase hq hb hseed
  constructor
  · calc
      (q*K+Exp.exp (rank K N s X))*Cw 1064921 N X = q*((K+w)*Cw 1064921 N X) := by rw [←hqW]; ring
      _=q*Fw 1064921 K N s X+(q-1)*(q*z) := by rw [htransport]; ring
  · obtain ⟨r,hr,_,heq⟩ := hfirst
    exact ⟨r,hr,by simpa only [q,u,mul_assoc,mul_comm,mul_left_comm] using heq⟩


/-! ## From `CompactOuterPellSeed` -/

/-- The rank forced by a compact packing supplies both complete seed families. -/
theorem seeds {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K low high N s X) :
    let u := (1064921:V)*N
    let R := rank K N s X
    ∃ sY n eta zeta gamma : V,
      0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      SeedRelations u R sY n eta zeta gamma ∧
      sY*Exp.exp u^3 ≤ power (Exp.exp R+1) R ∧
      (let Y := sY*Exp.exp u^3
      let a := Exp.exp R*Y+Y
      let c := ycoord R a
      ∃ f i T w y : V, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < w ∧ 0 < y ∧
        f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
        f*f=1+delta a*(i*c*c)*(i*c*c) ∧
        let I := delta a*i*c*c
        y=ycoord R (I-2) ∧ xcoord R (I-2)=I*w ∧
        w=oddQuotient ((R-1)/2) (I-2) ∧
        (w+c)%(f*f)=0 ∧ (w+R)%c=0 ∧
        f*f*c*T=w+c+f*f*R ∧ w=absdiff (f*f*c*T) (f*f*R+c) ∧
        I*I*w*w+y*y=1+I*I*y*y) := by
  obtain ⟨hpop,hphase,_⟩ := properties h
  have hu : (0:V)<1064921*N := mul_pos (by norm_num) (N_pos h)
  have hodd : ∃ r, rank K N s X=2*r+1 :=
    ⟨(rank K N s X-1)/2, (phase_indices (rank K N s X) hphase).2.1⟩
  obtain ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hz,hg,hseed,hsize⟩ :=
    outer_seed_with_size (1064921*N) (rank K N s X) hu hodd hpop
  refine ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hz,hg,hseed,hsize,?_⟩
  exact auxiliary_seed
    (Exp.exp (rank K N s X)*(sY*Exp.exp (1064921*N)^3)+sY*Exp.exp (1064921*N)^3)
    (rank K N s X) hphase


/-! ## From `CompactPositiveGammaSeed` -/

theorem positive_gamma {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (hpack : PackingInput 1064921 K low high N s X)
    (sY n eta zeta gammaOld w : V)
    (hsY : 0<sY) (hgammaOld : 0<gammaOld)
    (hseed : SeedRelations (1064921*N) (rank K N s X) sY n eta zeta gammaOld)
    (hXq : Exp.exp (rank K N s X) = Exp.exp (1064921*N)*w) :
    ∃ t gamma : V, 0<gamma ∧
      eta+zeta=rank K N s X+1+
        ((sY*(Exp.exp (1064921*N))^3)*(Exp.exp (1064921*N))^2)*t ∧
      gamma+w=gammaOld+t := by
  exact positive_correction_of_seed (1064921*N) (rank K N s X) sY n eta zeta gammaOld w
    hsY hgammaOld (properties hpack).2.1 hXq hseed


/-! ## From `CompactHaltPellSeed` -/

/-- The precise simultaneous seed conclusion, with the rank tied to `X`. -/
def SeedBundle (K N s : V) (X : V → V) [𝚺₁-Function₁ X] : Prop :=
  let u := (1064921:V)*N
  let R := rank K N s X
  ∃ sY n eta zeta gamma : V,
    0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
    SeedRelations u R sY n eta zeta gamma ∧
    sY*Exp.exp u^3 ≤ power (Exp.exp R+1) R ∧
    (let Y := sY*Exp.exp u^3
    let a := Exp.exp R*Y+Y
    let c := ycoord R a
    ∃ f i T w y : V, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < w ∧ 0 < y ∧
      f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
      f*f=1+delta a*(i*c*c)*(i*c*c) ∧
      let I := delta a*i*c*c
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*w ∧
      w=oddQuotient ((R-1)/2) (I-2) ∧
      (w+c)%(f*f)=0 ∧ (w+R)%c=0 ∧
      f*f*c*T=w+c+f*f*R ∧ w=absdiff (f*f*c*T) (f*f*R+c) ∧
      I*I*w*w+y*y=1+I*I*y*y)

/-- A model halt constructs one definable pulsed packing whose exact rank is
calibrated and which supplies both seed families. -/
theorem halt_calibrated_seeds (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V) ((Source34Ports.highNat : ℕ) : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        rank (paramKernel rho : V) (haltLength T) (haltStride T) X % (1064921*haltLength T) =
          (1064921*haltStride T) % (1064921*haltLength T) ∧
        SeedBundle (paramKernel rho : V) (haltLength T) (haltStride T) X) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  let N := haltLength T
  let s := haltStride T
  let c : V := (low+Exp.exp (1064921*N)*(high+(Exp.exp (1064921:V)-1)))*rep 1064921 N
  obtain ⟨δ,hd,hb,hs,hpack,hcal⟩ := halt_chosen_rank_no_high T c hT
  have hword := halt_packed_word T (fun _ => 0) hT
  letI : 𝚺₁-Function₁ (haltRow T) := hword.1
  letI : 𝚺₁-Function₁ (baseCell (haltRow T)) := baseCell_definable (haltRow T)
  letI : 𝚺₁-Function₁ δ := hd
  have hx : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := inferInstance
  refine ⟨δ,hd,hb,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  have hp : PackingInput 1064921 (paramKernel rho : V) low high N s
      (perturb (baseCell (haltRow T)) δ) := hpack
  have hr := rank_eq_window (paramKernel rho : V) N s (perturb (baseCell (haltRow T)) δ)
  constructor
  · simpa only [N,s,c] using hr ▸ hcal
  · exact seeds hp


/-! ## From `CompactHaltPellTransport` -/

theorem halt_pell_positive_transport (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V) ((Source34Ports.highNat : ℕ) : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        rank (paramKernel rho : V) (haltLength T) (haltStride T) X % (1064921*haltLength T) =
          (1064921*haltStride T) % (1064921*haltLength T) ∧
        SeedBundle (paramKernel rho : V) (haltLength T) (haltStride T) X ∧
        let R := rank (paramKernel rho : V) (haltLength T) (haltStride T) X
        let q := Exp.exp (1064921*haltLength T)
        let w := Exp.exp (R-1064921*haltLength T)
        let C := Cw 1064921 (haltLength T) X
        let F := Fw 1064921 (paramKernel rho : V) (haltLength T) (haltStride T) X
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ ((paramKernel rho : V)+w)*C=F+z*(q-1)) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_calibrated_seeds T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,hseed⟩ := hresult
  have hp : PackingInput 1064921 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := hpack
  have hs0 : 0<haltStride T := power_pos _ _ (by norm_num)
  have hsN : haltStride T<haltLength T := (Mixed121Word.geometry T).2
  exact ⟨hcal,hseed,calibrated_transport hp hs0 hsN hcal⟩


/-! ## From `CompactHaltFirstSeed` -/

def FirstData (K N s : V) (X : V → V) [𝚺₁-Function₁ X]
    (sY n eta zeta z : V) : Prop :=
  let q := Exp.exp ((1064921:V)*N)
  let R := rank K N s X
  let Y := sY*q^3
  let E := Exp.exp R*Y
  let k := eta+zeta
  let ell := E*Y*k
  let tau := E*n+k-R
  let C := Cw 1064921 N X
  let F := Fw 1064921 K N s X
  (q*K+Exp.exp R)*C = q*F+(q-1)*(q*z) ∧
  ∃ r : V, 0<r ∧
    (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
    (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*(q*z))

theorem halt_first_seed (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V) ((Source34Ports.highNat : ℕ) : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        let N := haltLength T
        let s := haltStride T
        let K : V := paramKernel rho
        let u := (1064921:V)*N
        let R := rank K N s X
        let q := Exp.exp u
        let w := Exp.exp (R-u)
        R%u=(1064921*s)%u ∧
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧
          (K+w)*Cw 1064921 N X=Fw 1064921 K N s X+z*(q-1) ∧
        ∃ sY n eta zeta gamma : V,
          0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
          SeedRelations u R sY n eta zeta gamma ∧
          sY*q^3 ≤ power (Exp.exp R+1) R ∧
          AuxData u R sY ∧ FirstData K N s X sY n eta zeta z) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_pell_positive_transport T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,hbundle,z,hz,hqw,htransport⟩ := hresult
  obtain ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,haux⟩ := hbundle
  have hp : PackingInput 1064921 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := hpack
  have hf := first_from_transport hp sY n eta zeta gamma _ z hsY hz hseed hqw htransport
  exact ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,haux,hf⟩


/-! ## From `CompactHaltFirstPositive` -/

theorem halt_first_positive (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V) ((Source34Ports.highNat : ℕ) : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        let N := haltLength T
        let s := haltStride T
        let K : V := paramKernel rho
        let u := (1064921:V)*N
        let R := rank K N s X
        let q := Exp.exp u
        let w := Exp.exp (R-u)
        R%u=(1064921*s)%u ∧
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧
          (K+w)*Cw 1064921 N X=Fw 1064921 K N s X+z*(q-1) ∧
        ∃ sY n eta zeta gamma : V,
          0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
          SeedRelations u R sY n eta zeta gamma ∧
          sY*q^3 ≤ power (Exp.exp R+1) R ∧
          PositiveAuxData u R sY ∧ FirstData K N s X sY n eta zeta z) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_first_seed T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,haux,hfirst⟩ := hresult
  have hp : PackingInput 1064921 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := hpack
  have hbig := (properties hp).2.2
  have hR : 0 < rank (paramKernel rho : V) (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := lt_of_le_of_lt (by simp) hbig
  have hauxp := auxiliary_positive (1064921*haltLength T)
    (rank (paramKernel rho : V) (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ)) sY hR haux
  exact ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxp,hfirst⟩


/-! ## From `CompactHaltFirstGamma` -/

def GammaData (K N s : V) (X : V → V) [𝚺₁-Function₁ X]
    (sY eta zeta gammaOld w : V) : Prop :=
  let q := Exp.exp ((1064921:V)*N)
  let R := rank K N s X
  ∃ t gamma : V, 0<gamma ∧
    eta+zeta=R+1+((sY*q^3)*q^2)*t ∧ gamma+w=gammaOld+t

theorem halt_first_gamma (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 1064921 (paramKernel rho : V) ((Source34Ports.lowNat : ℕ) : V) ((Source34Ports.highNat : ℕ) : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        let N := haltLength T
        let s := haltStride T
        let K : V := paramKernel rho
        let u := (1064921:V)*N
        let R := rank K N s X
        let q := Exp.exp u
        let w := Exp.exp (R-u)
        R%u=(1064921*s)%u ∧
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧
          (K+w)*Cw 1064921 N X=Fw 1064921 K N s X+z*(q-1) ∧
        ∃ sY n eta zeta gamma : V,
          0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
          SeedRelations u R sY n eta zeta gamma ∧
          sY*q^3 ≤ power (Exp.exp R+1) R ∧
          PositiveAuxData u R sY ∧ FirstData K N s X sY n eta zeta z ∧
          GammaData K N s X sY eta zeta gamma w) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_first_positive T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxp,hfirst⟩ := hresult
  have hp : PackingInput 1064921 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := hpack
  have hgamma := positive_gamma hp sY n eta zeta gamma _ hsY hg hseed hqw.symm
  exact ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxp,hfirst,hgamma⟩

end Source34Seeds

#print axioms Source34Seeds.properties
#print axioms Source34Seeds.calibrated_transport
#print axioms Source34Seeds.seeds
#print axioms Source34Seeds.halt_calibrated_seeds
#print axioms Source34Seeds.halt_first_positive
#print axioms Source34Seeds.halt_first_gamma

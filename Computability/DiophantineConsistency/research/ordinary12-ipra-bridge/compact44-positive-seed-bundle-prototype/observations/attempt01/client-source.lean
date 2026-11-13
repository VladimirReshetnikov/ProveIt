import CompactHaltPellSeed
import CompactAuxPositiveCoordinates
import CompactRankResidueJoin

/-! Keep the actual simultaneous outer and auxiliary seeds while deriving the
strictly positive ordinary-tail coordinates from those same witnesses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPositiveSeedBundle
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticPacking ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
open CompactConstructedRank CompactRankResidueJoin CompactHaltPellSeed CompactAuxPositiveCoordinates
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def PositiveSeedBundle (K N s : V) (X : V → V) [𝚺₁-Function₁ X] : Prop :=
  let u := (590069:V)*N
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
      I*I*w*w+y*y=1+I*I*y*y ∧
      0<f-1 ∧ (f-1)+1=f ∧ 0<delta a*i ∧ 0<delta a*i+w ∧
      delta a*(f*f-1) = (c*c*c*c)*(delta a*i)*(delta a*i))

theorem seed_bundle_positive {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (hpack : PackingInput 590069 K low high N s X)
    (hseed : SeedBundle K N s X) : PositiveSeedBundle K N s X := by
  have hbig := (properties hpack).2.2
  have hR : 0 < rank K N s X := lt_of_le_of_lt (by simp) hbig
  obtain ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hz,hg,hseed,hsize,
    f,i,T,w,y,hf,hi,hT,hw,hy,hfx,hyic,hfn,hydef,hux,hudef,
    huf,huc,hlit,habs,hnorm⟩ := hseed
  have hcoords := ordinary_coordinates _ (rank K N s X) _ f i w hR rfl hfx hi hw hfn
  exact ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hz,hg,hseed,hsize,
    f,i,T,w,y,hf,hi,hT,hw,hy,hfx,hyic,hfn,hydef,hux,hudef,
    huf,huc,hlit,habs,hnorm,hcoords⟩

#print axioms CompactPositiveSeedBundle.seed_bundle_positive
end CompactPositiveSeedBundle

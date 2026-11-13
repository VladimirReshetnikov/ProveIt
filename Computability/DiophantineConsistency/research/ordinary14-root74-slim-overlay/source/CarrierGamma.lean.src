import DiophantineConsistency.ArithmeticHalfBinomialSandwich

/-! Source-only proposal: gamma>w from the modified natural carrier and
existing internal Pell growth. No graph, endpoint or Lean run is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModifiedCarrierGammaDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellPowerRecovery ArithmeticHalfBinomialSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fact-level gamma>w from the exact Pell coordinates and a subtraction-free
carrier equality. The bounds X≤a and w≤a and R≥3 are explicit. -/
theorem gamma_gt_from_carrier (a X w R c d H gamma W : V)
    (hR : 3≤R) (hXa : X≤a) (hwa : w≤a) (hH : H=4*a+3)
    (hc : c=ycoord R a) (hd : d=xcoord R a)
    (hbal : d+H*W=X+a*c+H*gamma) : w<gamma := by
  have hp2 : power (2*a+3) (2:V)=(2*a+3)*(2*a+3) := by
    have h := power_succ (2*a+3) (1:V)
    simpa only [show (1:V)+1=2 by ring,power_one] using h
  have hcLarge : (2*a+3)*(2*a+3)≤c := calc
    (2*a+3)*(2*a+3)=power (2*a+3) (2:V) := hp2.symm
    _≤ycoord ((2:V)+1) a := power_le_ycoord a (2:V)
    _=ycoord 3 a := by congr 1; ring
    _≤ycoord R a := (ordinate_strictMono a).monotone hR
    _=c := hc.symm
  have hsum : X+H*w≤a+H*a := add_le_add hXa
    (mul_le_mul_of_nonneg_left hwa (Arithmetic.zero_le H))
  have hpoly : a+H*a<(2*a+3)*(2*a+3) := by
    rw [hH]
    have he : (2*a+3)*(2*a+3)=(a+(4*a+3)*a)+(8*a+9) := by ring
    rw [he]
    exact lt_add_of_pos_right _ (by simp)
  have hgap : X+H*w<c := lt_of_le_of_lt hsum (lt_of_lt_of_le hpoly hcLarge)
  have hdc : (a+1)*c<d := by
    have h := x_gt a R
    rw [←hc,←hd] at h
    exact h
  by_contra hn
  have hgamma : gamma≤w := le_of_not_gt hn
  have hmul : H*gamma≤H*w := mul_le_mul_of_nonneg_left hgamma (Arithmetic.zero_le H)
  have hupper : d+H*W≤X+a*c+H*w := by rw [hbal]; exact add_le_add_left hmul _
  have hupperlt : X+a*c+H*w<(a+1)*c := calc
    X+a*c+H*w=(X+H*w)+a*c := by ring
    _<c+a*c := add_lt_add_right hgap _
    _=(a+1)*c := by ring
  have hdle : d≤d+H*W := le_add_of_nonneg_right (Arithmetic.zero_le (H*W))
  exact (not_le_of_gt (lt_trans hupperlt hdc)) (le_trans hdle hupper)

/-- Graph-shaped corollary of the preceding fact. The carrier and first-index
relations, positive scale, Pell coordinates and R≥3 remain explicit premises. -/
theorem gamma_gt_from_modified_balance (U H d X Y a c gamma k R W q w : V)
    (hU : 0<U) (hY : 0<Y) (hq : 1≤q) (hX : X=q*w) (ha : a=X*Y+Y)
    (hH : H=4*a+3) (hR : 3≤R)
    (hc : c=ycoord R a) (hd : d=xcoord R a)
    (hk : k=R+1+U*W)
    (hbal : U*d+H*k=U*(X+a*c)+H*(U*gamma+R+1)) : w<gamma := by
  have hY1 : 1≤Y := pos_iff_one_le.mp hY
  have hXa : X≤a := calc
    X≤X*Y := le_mul_of_one_le_right (Arithmetic.zero_le X) hY1
    _≤X*Y+Y := le_add_of_nonneg_right (Arithmetic.zero_le Y)
    _=a := ha.symm
  have hwX : w≤X := by rw [hX]; exact le_mul_of_one_le_left (Arithmetic.zero_le w) hq
  have hwa : w≤a := le_trans hwX hXa
  have hl : U*d+H*k=U*(d+H*W)+H*(R+1) := by rw [hk]; ring
  have hr : U*(X+a*c)+H*(U*gamma+R+1)=U*(X+a*c+H*gamma)+H*(R+1) := by ring
  rw [hl,hr] at hbal
  have he : d+H*W=X+a*c+H*gamma :=
    mul_left_cancel₀ (ne_of_gt hU) (add_right_cancel hbal)
  exact gamma_gt_from_carrier a X w R c d H gamma W hR hXa hwa hH hc hd he

end DiophantineConsistency.ModifiedCarrierGammaDraft

#print axioms DiophantineConsistency.ModifiedCarrierGammaDraft.gamma_gt_from_carrier
#print axioms DiophantineConsistency.ModifiedCarrierGammaDraft.gamma_gt_from_modified_balance

import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProduct
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# A regular name for an internal finite product

A uniform row Cauchy budget determines a single query clock for the
whole primitive-recursive fold. The same finite estimate transfers
rowwise cofinal approximations to the product and its regular name.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductName

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProduct (sample radius amplification rowBoundsAt rowDistance sample_canonical
  sample_distance sample_bound)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product canonical_unique)
open GaussianRationalL1 (raw_den_positive raw_represents)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.Foundations.BoundedFormulas (subst_up_shift')

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBounds (f : PR 3) (N R x : PTm n) : Fm PTm n :=
  .all (rowBoundsAt f (var 0) (Syn.shift N) (Syn.shift R) (Syn.shift x))
def rowRegular (f : PR 3) (N L x : PTm n) : Fm PTm n :=
  .all (.all (rowDistance f f (var 1) (var 0) (Syn.shift (Syn.shift N))
    (Syn.shift (Syn.shift L)*(unit (var 1)+unit (var 0))) (unit (var 1)*unit (var 0))
    (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift x))))
def cofinalRows (f g : PR 3) (N C x y : PTm n) : Fm PTm n :=
  .all (rowDistance f g (var 0) (var 0) (Syn.shift N) (Syn.shift C) (unit (var 0)) (Syn.shift x) (Syn.shift y))

def modulus (N R L : PTm n) : PTm n := amplification R N*L
def rawData (N x : PTm n) : PTm n := pairT N x
def rawBody (f : PR 3) : PTm 2 := sample f (var 0) (fstT (var 1)) (sndT (var 1))
def rawF (f : PR 3) : PR 2 := PTm.toPR (rawBody f)
def nameF (f : PR 3) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (N R L x : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus N R L) (rawData N x)
def clock (N R L p : PTm n) : PTm n := GaussianFastValueCut.exponent (modulus N R L) p

ipra_subst rowBounds [Syn.subst_shift, Syn.shift_subst]

ipra_subst rowRegular [Syn.subst_shift, Syn.shift_subst]

ipra_subst cofinalRows [Syn.subst_shift, Syn.shift_subst]

ipra_subst modulus

ipra_subst rawData

ipra_subst data

ipra_subst clock

theorem bounds_at (f : PR 3) (p N R x : PTm n) (h : Γ ⊢[PRAAx] rowBounds f N R x) : Γ ⊢[PRAAx] rowBoundsAt f p N R x :=
  by simpa [rowBounds] using h.allE p

theorem regular_rows_at (f : PR 3) (p q N L x : PTm n) (h : Γ ⊢[PRAAx] rowRegular f N L x) :
    Γ ⊢[PRAAx] rowDistance f f p q N (L*(unit p+unit q)) (unit p*unit q) x x := by
  have atP : Γ ⊢[PRAAx] .all (rowDistance f f (Syn.shift p) (var 0) (Syn.shift N)
      (Syn.shift L*(unit (Syn.shift p)+unit (var 0))) (unit (Syn.shift p)*unit (var 0)) (Syn.shift x) (Syn.shift x)) := by
    simpa only [rowRegular,Fm.subst_all,GaussianNamedFiniteProduct.subst_rowDistance,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,
      Syn.up_succ,subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE p
  simpa only [GaussianNamedFiniteProduct.subst_rowDistance,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using atP.allE q

theorem cofinal_rows_at (f g : PR 3) (p N C x y : PTm n) (h : Γ ⊢[PRAAx] cofinalRows f g N C x y) :
    Γ ⊢[PRAAx] rowDistance f g p p N C (unit p) x y := by
  simpa [cofinalRows] using h.allE p

theorem raw_at (f : PR 3) (p N x : PTm n) : Γ ⊢[PRAAx] ap2 (rawF f) p (rawData N x) ≐ sample f p N x := by
  have first : Γ ⊢[PRAAx] ap2 (rawF f) p (rawData N x) ≐ sample f p (fstT (rawData N x)) (sndT (rawData N x)) := by
    simpa [rawF,rawBody,ap2] using toPR_eq (Γ := Γ) (rawBody f) ![p,rawData N x]
  have last := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![p,fstT (rawData N x),sndT (rawData N x)]) (σ' := ![p,N,x]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact snd_pair _ _)
  exact first.eqTrans (by simpa using last)

theorem clock_later (N R L p : PTm n) : Γ ⊢[PRAAx] le p (clock N R L p) := le_add_right _ _

theorem name_at (f : PR 3) (p N R L x : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data N R L x) ≐ sample f (clock N R L p) N x := by
  let q := clock N R L p
  let s := sample f q N x
  have read := raw_at (Γ := Γ) f q N x
  have e : Γ ⊢[PRAAx] GaussianFastValueCut.recode (ap2 (rawF f) q (rawData N x)) ≐ GaussianFastValueCut.recode s := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianFastValueCut.recode (var 0) : PTm 1)
      (σ := ![ap2 (rawF f) q (rawData N x)]) (σ' := ![s]) (fun i => by fin_cases i; exact read)
  have fixed : Γ ⊢[PRAAx] GaussianFastValueCut.recode s ≐ s :=
    canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical _) (sample_canonical f q N x)
      (raw_den_positive _) (GaussianFastValueCut.recode_represents _) (raw_represents _)
  exact (GaussianFastValueCut.name_at (rawF f) (modulus N R L) (rawData N x) p).eqTrans (e.eqTrans fixed)

theorem raw_regular (f : PR 3) (N R L x : PTm n) (hb : Γ ⊢[PRAAx] rowBounds f N R x)
    (hr : Γ ⊢[PRAAx] rowRegular f N L x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawF f) (modulus N R L) (rawData N x) := by
  refine .allI (.allI ?_)
  let lift := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let N' := lift N
  let R' := lift R
  let L' := lift L
  let X := lift x
  have b : Δ ⊢[PRAAx] rowBounds f N' R' X := by simpa [Δ,N',R',X,lift,Fm.shift,Syn.shift] using hb.shift.shift
  have r : Δ ⊢[PRAAx] rowRegular f N' L' X := by simpa [Δ,N',L',X,lift,Fm.shift,Syn.shift] using hr.shift.shift
  have d := sample_distance f f p q N' R' (L'*(unit p+unit q)) (unit p*unit q) X X
    (positive_product _ _ (unit_positive p) (unit_positive q)) (bounds_at f p N' R' X b) (bounds_at f q N' R' X b)
    (regular_rows_at f p q N' L' X r)
  have result : Δ ⊢[PRAAx] distanceBounded (ap2 (rawF f) p (rawData N' X)) (ap2 (rawF f) q (rawData N' X))
      (modulus N' R' L'*(unit p+unit q)) (unit p*unit q) :=
    distance_congr (raw_at f p N' X).eqSymm (raw_at f q N' X).eqSymm
      (by unfold modulus; ipra_ring) (.eqRefl _) d
  simpa [GaussianFastValueCut.regular,Δ,N',R',L',X,lift,p,q,Syn.shift] using result

theorem name_regular (f : PR 3) (N R L x : PTm n) (hb : Γ ⊢[PRAAx] rowBounds f N R x)
    (hr : Γ ⊢[PRAAx] rowRegular f N L x) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data N R L x) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular f N R L x hb hr)

theorem name_bound (f : PR 3) (p N R L x : PTm n) (hb : Γ ⊢[PRAAx] rowBounds f N R x) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data N R L x)) (radius R N) one :=
  bound_congr (name_at f p N R L x).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_bound f (clock N R L p) N R x (bounds_at f (clock N R L p) N R x hb))

theorem name_finite_distance (f g : PR 3) (p q N R L M E K x y : PTm n)
    (hk : Γ ⊢[PRAAx] le one K) (hf : Γ ⊢[PRAAx] rowBounds f N R x) (hg : Γ ⊢[PRAAx] rowBounds g N R y)
    (hd : Γ ⊢[PRAAx] rowDistance f g (clock N R L p) (clock N R M q) N E K x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data N R L x)) (ap2 (nameF g) q (data N R M y)) (amplification R N*E) K :=
  distance_congr (name_at f p N R L x).eqSymm (name_at g q N R M y).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_distance f g _ _ N R E K x y hk (bounds_at f _ N R x hf) (bounds_at g _ N R y hg) hd)

theorem cofinal_raw (f g : PR 3) (N R C x y : PTm n)
    (hf : Γ ⊢[PRAAx] rowBounds f N R x) (hg : Γ ⊢[PRAAx] rowBounds g N R y)
    (hd : Γ ⊢[PRAAx] cofinalRows f g N C x y) :
    Γ ⊢[PRAAx] GaussianValueNormalizerExtensionality.rawDiagonal (rawF f) (rawF g) (rawData N x) (rawData N y)
      (amplification R N*C) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let N' := Syn.shift N
  let R' := Syn.shift R
  let C' := Syn.shift C
  let X := Syn.shift x
  let Y := Syn.shift y
  have hf' : Δ ⊢[PRAAx] rowBounds f N' R' X := by simpa [Δ,N',R',X,Fm.shift,Syn.shift] using hf.shift
  have hg' : Δ ⊢[PRAAx] rowBounds g N' R' Y := by simpa [Δ,N',R',Y,Fm.shift,Syn.shift] using hg.shift
  have hd' : Δ ⊢[PRAAx] cofinalRows f g N' C' X Y := by simpa [Δ,N',C',X,Y,Fm.shift,Syn.shift] using hd.shift
  have d := sample_distance f g p p N' R' C' (unit p) X Y (unit_positive p)
    (bounds_at f p N' R' X hf') (bounds_at g p N' R' Y hg') (cofinal_rows_at f g p N' C' X Y hd')
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Δ,p,N',R',C',X,Y,Syn.shift] using
    distance_congr (raw_at f p N' X).eqSymm (raw_at g p N' Y).eqSymm (.eqRefl _) (.eqRefl _) d

theorem name_cross (f g : PR 3) (N R L M C x y : PTm n)
    (hf : Γ ⊢[PRAAx] rowBounds f N R x) (hg : Γ ⊢[PRAAx] rowBounds g N R y)
    (hF : Γ ⊢[PRAAx] rowRegular f N L x) (hG : Γ ⊢[PRAAx] rowRegular g N M y)
    (hd : Γ ⊢[PRAAx] cofinalRows f g N C x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data N R L x) (data N R M y) :=
  GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ _
    (raw_regular f N R L x hf hF) (raw_regular g N R M y hg hG) (cofinal_raw f g N R C x y hf hg hd)

theorem approximant_distance (f g : PR 3) (p N R L C x y : PTm n)
    (hf : Γ ⊢[PRAAx] rowBounds f N R x) (hF : Γ ⊢[PRAAx] rowRegular f N L x)
    (hg : Γ ⊢[PRAAx] rowBoundsAt g p N R y) (hd : Γ ⊢[PRAAx] rowDistance g f p p N C (unit p) y x) :
    Γ ⊢[PRAAx] distanceBounded (sample g p N y) (ap2 (nameF f) p (data N R L x))
      (amplification R N*C+(modulus N R L+one)) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have finite := sample_distance g f p p N R C (unit p) y x hp hg (bounds_at f p N R x hf) hd
  have normalize := GaussianNameRingLaws.normalized_to_sample (rawF f) (modulus N R L) (rawData N x) p
    (raw_regular f N R L x hf hF)
  have last := distance_congr (raw_at f p N x) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ hp normalize)
  exact distance_triangle_same _ _ _ _ _ _ hp finite last

theorem actual_finite_product_name_regular_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((rowBounds f (var 0) (var 1) (var 3) ⋏ rowRegular f (var 0) (var 2) (var 3)) ⟶
      pointCN (nameF f) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_finite_product_approximant_closed (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((rowBounds f (var 1) (var 2) (var 5) ⋏ rowRegular f (var 1) (var 3) (var 5)) ⟶
      (rowBoundsAt g (var 0) (var 1) (var 2) (var 6) ⋏ rowDistance g f (var 0) (var 0) (var 1) (var 4)
        (unit (var 0)) (var 6) (var 5)) ⟶
      distanceBounded (sample g (var 0) (var 1) (var 6)) (ap2 (nameF f) (var 0) (data (var 1) (var 2) (var 3) (var 5)))
        (amplification (var 2) (var 1)*var 4+(modulus (var 1) (var 2) (var 3)+one)) (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (approximant_distance f g _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductName

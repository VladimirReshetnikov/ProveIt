import IPRADerivations.Analysis.GaussianBarnesCanonicalHead

/-!
# Splitting the actual finite Barnes product

The raw product splits at an internal index by exact equality of each
shifted factor observation. The normalized names preserve that split.
A zero factor therefore forces the actual entire prefix sample to zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHead (source parameters body nameF data regular factor_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus product_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope multiply_sample_error normalized_to_sample)
open GaussianNamedFiniteProductFamily (rowF family_bounds family_regular)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalFiniteProduct (product_split product_index_congr product_congr_bounded offset_at)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left qmul_zero_right)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "factorData" => GaussianBarnesCanonicalFactor.data
local notation "rows" => rowF F body
local notation "rowBody" => GaussianRationalRectangularProduct.rowBody (GaussianNamedFiniteProduct.body rows)
local notation "rowRadius" => GaussianNamedFiniteProductFamily.radius F body

def raw (p z R B N r : PTm n) : PTm n :=
  GaussianNamedFiniteProduct.sample rows p r (parameters z R B N)

private theorem raw_row_at (p i z R B N : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody i (pairT p (parameters z R B N)) ≐
      ap2 F p (factorData z R B (succ (N+i))) := by
  have e : Γ ⊢[PRAAx] inst2 rowBody i (pairT p (parameters z R B N)) ≐
      ap3 rows p i (parameters z R B N) := by
    simpa [GaussianNamedFiniteProduct.body,inst3] using
      GaussianRationalRectangularProduct.row_at (Γ := Γ) (GaussianNamedFiniteProduct.body rows) p i (parameters z R B N)
  exact e.eqTrans (factor_at p i z R B N)

theorem raw_split (p z R B N r s : PTm n) : Γ ⊢[PRAAx]
    raw p z R B N (r+s) ≐ qmul (raw p z R B N r) (raw p z R B (N+r) s) := by
  let x := pairT p (parameters z R B N)
  let y := pairT p (parameters z R B (N+r))
  have equal : Γ ⊢[PRAAx] termsEqual (offB rowBody) rowBody s (pairT r x) y := by
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (sh s) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    let j := succ (sh N+(sh r+i))
    let k := succ ((sh N+sh r)+i)
    have ej : Δ ⊢[PRAAx] j ≐ k := congrSucc (by ipra_ring)
    have arg : Δ ⊢[PRAAx] factorData (sh z) (sh R) (sh B) j ≐ factorData (sh z) (sh R) (sh B) k := by
      simpa only [GaussianBarnesCanonicalFactor.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        Prf.eqCongr1 (factorData (Syn.shift (sh z)) (Syn.shift (sh R)) (Syn.shift (sh B)) (var 0)) ej
    have left := (offset_at (Γ := Δ) rowBody (sh r) i (pairT (sh p) (parameters (sh z) (sh R) (sh B) (sh N)))).eqTrans
      (raw_row_at (sh p) (sh r+i) (sh z) (sh R) (sh B) (sh N))
    have right := raw_row_at (Γ := Δ) (sh p) i (sh z) (sh R) (sh B) (sh N+sh r)
    simpa only [Syn.shift,sh,Δ,i,x,y,subst_pairT,GaussianBarnesCanonicalHead.subst_parameters,PTm.subst_add] using
      left.eqTrans ((congrAp2 F (.eqRefl (sh p)) arg).eqTrans right.eqSymm)
  exact (product_split rowBody r s x).eqTrans
    (qmul_congr (.eqRefl _) (product_congr_bounded _ _ _ _ _ equal))

private theorem raw_length_congr (p z R B N : PTm n) {r s : PTm n} (e : Γ ⊢[PRAAx] r ≐ s) :
    Γ ⊢[PRAAx] raw p z R B N r ≐ raw p z R B N s :=
  product_index_congr rowBody e (.eqRefl _)

theorem zero_at_factor (p z R B N r i : PTm n) (hi : Γ ⊢[PRAAx] lt i r)
    (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.base z B (succ (N+i)) ≐ qzero) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B N r) ≐ qzero := by
  let s := GaussianNamedFiniteProductName.clock r (rowRadius r (parameters z R B N)) one p
  let j := succ i
  let l := monus r j
  have size : Γ ⊢[PRAAx] r ≐ j+l := eq_add_of_le hi
  have a := (GaussianNamedFiniteProduct.sample_succ (Γ := Γ) rows s i (parameters z R B N)).eqTrans
    ((qmul_congr (.eqRefl _) ((factor_at s i z R B N).eqTrans
      (GaussianBarnesCanonicalFactor.zero_sample s z R B (succ (N+i)) (zero_lt_succ _) h))).eqTrans (qmul_zero_right _))
  have b := (raw_length_congr s z R B N size).eqTrans (raw_split s z R B N j l)
  exact (GaussianBarnesCanonicalHead.sample_at p z R B N r).eqTrans
    (b.eqTrans ((qmul_congr a (.eqRefl _)).eqTrans (qmul_zero_left _)))

private def rawCap (z R B N r : PTm n) : PTm n :=
  GaussianNamedFiniteProduct.radius (rowRadius r (parameters z R B N)) r

private def rawError (z R B N r : PTm n) : PTm n :=
  GaussianNamedFiniteProductName.modulus r (rowRadius r (parameters z R B N)) one+one

private theorem raw_bound (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (raw p z R B N r) (rawCap z R B N r) one :=
  GaussianNamedFiniteProduct.sample_bound rows p r _ _
    (GaussianNamedFiniteProductName.bounds_at _ _ _ _ _
      (family_bounds F body r _ (GaussianBarnesCanonicalHead.rows_regular z R B N r h)))

private theorem raw_error (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N r)) (raw p z R B N r) (rawError z R B N r) (unit p) := by
  let x := parameters z R B N
  let M := GaussianNamedFiniteProductName.modulus r (rowRadius r x) one
  let D := GaussianNamedFiniteProductName.rawData r x
  have reg := GaussianBarnesCanonicalHead.rows_regular z R B N r h
  have input := GaussianNamedFiniteProductName.raw_regular rows r (rowRadius r x) one x
    (family_bounds F body r x reg) (family_regular F body r x reg)
  exact distance_congr (.eqRefl _) (GaussianNamedFiniteProductName.raw_at rows p r x) (.eqRefl _) (.eqRefl _)
    (normalized_to_sample (GaussianNamedFiniteProductName.rawF rows) M D p input)

private def cost (z R B N r s : PTm n) : PTm n :=
  rawError z R B N (r+s)+
    (rawError z R B N r*rawCap z R B (N+r) s+
      GaussianBarnesCanonicalHead.cap R N r*rawError z R B (N+r) s)+
    (multiplyModulus nameF nameF (data z R B N r) (data z R B (N+r) s)+one)

@[simp] private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (z R B N r s : PTm n) :
    Syn.subst σ (cost z R B N r s) =
      cost (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ s) := by
  simp [cost,rawError,rawCap,GaussianNamedFiniteProductFamily.radius,one]

private theorem split_observation (p z R B N r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N (r+s)))
      (ap2 (multiplyF nameF nameF) p (multiplyData nameF nameF (data z R B N r) (data z R B (N+r) s)))
      (cost z R B N r s) (unit p) := by
  let x := data z R B N r
  let y := data z R B (N+r) s
  let u := raw p z R B N r
  let v := raw p z R B (N+r) s
  let hp := unit_positive (Γ := Γ) p
  have read := raw_split (Γ := Γ) p z R B N r s
  have first := distance_congr (.eqRefl _) read (.eqRefl _) (.eqRefl _) (raw_error p z R B N (r+s) h)
  have mid := product_distance u (ap2 nameF p x) v (ap2 nameF p y)
    (rawError z R B N r) (rawError z R B (N+r) s) (unit p)
    (rawCap z R B (N+r) s) (GaussianBarnesCanonicalHead.cap R N r) hp
    (distance_symmetric _ _ _ _ hp (raw_error p z R B N r h))
    (distance_symmetric _ _ _ _ hp (raw_error p z R B (N+r) s h))
    (raw_bound p z R B (N+r) s h) (GaussianBarnesCanonicalHead.sample_bound p z R B N r h)
  have last := distance_symmetric _ _ _ _ hp (multiply_sample_error nameF nameF x y p
    (regular z R B N r h) (regular z R B (N+r) s h))
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first mid) last

theorem split_cross (z R B N r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent nameF (multiplyF nameF nameF) (data z R B N (r+s))
      (multiplyData nameF nameF (data z R B N r) (data z R B (N+r) s)) := by
  refine equivalent_of_envelope _ _ _ _ (cost z R B N r s) (regular z R B N (r+s) h)
    (GaussianNameArithmetic.multiply_fast _ _ _ _ (regular z R B N r h) (regular z R B (N+r) s h)) (.allI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianBarnesCanonicalHead.subst_data,subst_cost,
    GaussianNameArithmetic.subst_multiplyData,PTm.subst_add,Syn.shift,sh,Δ] using
    split_observation (var 0) (sh z) (sh R) (sh B) (sh N) (sh r) (sh s) hs

theorem actual_original_Barnes_finite_split_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF (multiplyF nameF nameF)
        (data (var 0) (var 1) (var 2) (var 3) (var 4+var 5))
        (multiplyData nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))
          (data (var 0) (var 1) (var 2) (var 3+var 4) (var 5)))) :=
  closeUniv 6 (.impI (split_cross _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_Barnes_finite_zero_factor_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (lt (var 6) (var 5) ⟶
        (GaussianBarnesCanonicalFactor.base (var 1) (var 3) (succ (var 4+var 6)) ≐ qzero) ⟶
        ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ qzero) :=
  closeUniv 7 (.impI (.impI (zero_at_factor _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadSplit

import IPRADerivations.Analysis.Euler.CompactExhaustion.Tails.GaussianEulerCompactLowerTail
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerTailFiniteBudget

/-!
# Transferring right-endpoint bounds to the actual rooted lower grid

The original affine grid is grouped at its exact powered partition.
A magnitude bound on the powered right tags transfers to every sample
in its block using the original sampled modulus.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailRootedMajorant

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (quadrature sampledModulus sampleBody sampleData sample_body_at)
open GaussianEulerCompactLowerTail (literal_weight weightedPoint)
open GaussianEulerLowerTailLocalComparison (original_row_distance rowTime rightTime)
open GaussianEulerLowerTailPartition (offset panelWidth totalWidth cutData cutF offset_at root_right_guard uniform_panel_width grouped_original_quadrature)
open GaussianEulerLowerTailRootGrid (rootNumerator rootDenominator timeNumerator timeDenominator rootRatio)
open GaussianEulerLowerTailRowBound (stepScale right_width scale_local_budget)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianPartitionedFiniteSum (block blockBody block_at)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_index_congr sum_multiply)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)
open GaussianEulerCompactLowerTail renaming subst_rootDenominator → subst_rootDen, subst_rootNumerator → subst_rootNum, subst_timeDenominator → subst_timeDen, subst_timeNumerator → subst_timeNum

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "BlockNum" => GaussianEulerLowerBlockWeight.numerator
local notation "BlockDen" => GaussianEulerLowerBlockWeight.denominator
local notation "RowNum" => GaussianEulerLowerBlockWeight.rowNumerator
local notation "RowDen" => GaussianEulerLowerBlockWeight.rowDenominator

def gridData (s N p q k R x : PTm n) : PTm n :=
  let A := succ k
  let W := totalWidth N p q A
  sampleData s W (timeNumerator zero N p q A) W (timeDenominator N q A R) x

def panelData (s N p q k R x : PTm n) : PTm n :=
  pairT (weightedPoint N p q k R) (pairT (cutData N p q (succ k)) (gridData s N p q k R x))

def quadratureValue (F : PR 3) (s N p q k R x : PTm n) : PTm n :=
  let A := succ k
  let W := totalWidth N p q A
  quadrature F s W (timeNumerator zero N p q A) W (timeDenominator N q A R) x

def rightBounds (F : PR 3) (x s N p q k R J : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    bounded (ap3 F (Syn.shift s)
      (rightTime (var 0) (Syn.shift N) (Syn.shift p) (Syn.shift q) (succ (Syn.shift k)) (Syn.shift R)) (Syn.shift x))
      (Syn.shift J*(pw (rootDenominator (Syn.shift N) (Syn.shift q) (succ (Syn.shift k)) (Syn.shift R)) (Syn.shift k)*
        unit (Syn.shift s)+num 3*pw (rootNumerator (succ (var 0)) (Syn.shift N) (Syn.shift p) (Syn.shift q)) (Syn.shift k)))
      (pw (rootNumerator (succ (var 0)) (Syn.shift N) (Syn.shift p) (Syn.shift q)) (Syn.shift k)*unit (Syn.shift s)))

private theorem subst_rightTime {m : ℕ} (σ : Fin n → PTm m) (i N p q A R : PTm n) :
    Syn.subst σ (rightTime i N p q A R) =
      rightTime (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [rightTime,subst_timeNum,subst_timeDen]
attribute [local simp] subst_rootNum subst_rootDen subst_timeNum subst_timeDen subst_rightTime

ipra_subst rightBounds [Syn.subst_shift, Syn.shift_subst]

private theorem right_bound_at (F : PR 3) (x s N p q k R J i : PTm n)
    (h : Γ ⊢[PRAAx] rightBounds F x s N p q k R J) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (ap3 F s (rightTime i N p q (succ k) R) x)
      (J*(pw (rootDenominator N q (succ k) R) k*unit s+num 3*pw (rootNumerator (succ i) N p q) k))
      (pw (rootNumerator (succ i) N p q) k*unit s) := by
  exact .impE (by simpa [rightBounds] using h.allE i) hi

private theorem row_norm (F : PR 3) (x s N p q k R J L i j : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i N p q (succ k)))
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)))
    (hm : Γ ⊢[PRAAx] sampledModulus F (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L x)
    (hr : Γ ⊢[PRAAx] rightBounds F x s N p q k R J) : Γ ⊢[PRAAx]
    bounded (ap3 F s (rowTime i j N p q (succ k) R) x)
      ((J+one)*RowNum (rootDenominator N q (succ k) R) (pw (rootDenominator N q (succ k) R) k)
        (pw (rootNumerator (succ i) N p q) k) (stepScale p q k) L (unit s))
      (RowDen (rootDenominator N q (succ k) R) (pw (rootNumerator (succ i) N p q) k) (unit s)) := by
  let D := rootDenominator N q (succ k) R
  let U := pw D k
  let V := pw (rootNumerator (succ i) N p q) k
  let S := stepScale p q k
  let P := unit s
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _
    (root_right_guard i N p q (succ k) R hN hpq hi).andE₁
  have hP : Γ ⊢[PRAAx] le one P := unit_positive s
  have hDP := positive_product _ _ hD hP
  have hVP := positive_product _ _ hV hP
  have drift := scale_local_budget _ _ s N p q k R L hN
    (original_row_distance F i j N p q k R L x s s hN hpq hi hj hW hm)
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hDP hVP drift
    (right_bound_at F x s N p q k R J i hr hi)
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hDP hVP)
    (GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP) ?_ raw
  change Γ ⊢[PRAAx] le (((L*S*P+two*D)*(V*P)+(J*(U*P+num 3*V))*(D*P))*(V*D*P))
    (((J+one)*(U*D*P+L*S*V*P+num 3*V*D))*((D*P)*(V*P)))
  exact le_of_eq_add (d := (U*D*P+J*L*S*V*P+V*D)*(V*D*P*P)) (by unfold num two; ipra_ring)

private theorem scaled_block_bound (f : PTm 2) (w x M D U V S L P J : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerBlockWeight.source M D U V S P)
    (hw : Γ ⊢[PRAAx] bounded w one (D*U))
    (hr : Γ ⊢[PRAAx] summandsBounded f M x (J*RowNum D U V S L P) (RowDen D V P)) : Γ ⊢[PRAAx]
    bounded (qmul w (sum f M x)) (J*BlockNum D S L P) (BlockDen D P) := by
  have hD := h.andE₁
  have hU := h.andE₂.andE₁
  have hV := h.andE₂.andE₂.andE₁
  have hP := h.andE₂.andE₂.andE₂.andE₁
  have hDen := GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP
  have hW := positive_product _ _ hD hU
  have hOut : Γ ⊢[PRAAx] le one (BlockDen D P) := positive_product _ _ (positive_product _ _ hD hD) hP
  have raw := bounded_product _ _ _ _ _ _ hW hDen hw (uniform_sum_bound f M x _ _ hDen hr)
  have k := GaussianEulerLowerBlockWeight.width_numerator M D U V S L P
    h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hW hDen) hOut
    (le_congr (by unfold GaussianEulerLowerBlockWeight.denominator; ipra_ring) (by unfold GaussianEulerLowerBlockWeight.denominator GaussianEulerLowerBlockWeight.rowDenominator; ipra_ring)
      (mul_le_mul_right (J*BlockDen D P) k)) raw

private theorem panel_norm (F : PR 3) (x s N p q k R J L i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N)
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)))
    (hm : Γ ⊢[PRAAx] sampledModulus F (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L x)
    (hr : Γ ⊢[PRAAx] rightBounds F x s N p q k R J) : Γ ⊢[PRAAx]
    bounded (qmul (weightedPoint N p q k R)
      (block cutF (sampleBody F) i (cutData N p q (succ k)) (gridData s N p q k R x)))
      ((J+one)*BlockNum (rootDenominator N q (succ k) R) (stepScale p q k) L (unit s))
      (BlockDen (rootDenominator N q (succ k) R) (unit s)) := by
  let A := succ k
  let D := rootDenominator N q A R
  let U := pw D k
  let V := pw (rootNumerator (succ i) N p q) k
  let S := stepScale p q k
  let P := unit s
  let M := panelWidth i N p q A
  let W := totalWidth N p q A
  let d := cutData N p q A
  let y := gridData s N p q k R x
  let f := sampleBody F
  let v := pairT (offset i N p q A) y
  let w := weightedPoint N p q k R
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hU : Γ ⊢[PRAAx] le one U := GaussianPolynomialPerturbation.power_positive _ _ hD
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _
    (root_right_guard i N p q A R hN hpq hi).andE₁
  have hMU : Γ ⊢[PRAAx] le M (S*U) :=
    le_congr (.eqRefl _) (by dsimp only [S,U,D,A]; unfold stepScale; ipra_ring)
      (uniform_panel_width i N p q k R hN hpq hi)
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerBlockWeight.source M D U V S P :=
    .andI hD (.andI hU (.andI hV (.andI (unit_positive s) (.andI (right_width i N p q k) hMU))))
  have hRows : Γ ⊢[PRAAx] summandsBounded (offB f) M v ((J+one)*RowNum D U V S L P) (RowDen D V P) := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
    let j : PTm (n+1) := var 0
    have n' : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
    have ord : Δ ⊢[PRAAx] le (sh p) (sh q) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hpq.shift.wk
    have ii : Δ ⊢[PRAAx] lt (sh i) (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hi.shift.wk
    have jj : Δ ⊢[PRAAx] lt j (panelWidth (sh i) (sh N) (sh p) (sh q) (succ (sh k))) := by
      simpa [Δ,j,sh,M,A,panelWidth,offset,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (sh M))
    have w' : Δ ⊢[PRAAx] le one (totalWidth (sh N) (sh p) (sh q) (succ (sh k))) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,totalWidth,offset,one] using hW.shift.wk
    have m' : Δ ⊢[PRAAx] sampledModulus F (timeNumerator zero (sh N) (sh p) (sh q) (succ (sh k)))
        (totalWidth (sh N) (sh p) (sh q) (succ (sh k))) (timeDenominator (sh N) (sh q) (succ (sh k)) (sh R)) (sh L) (sh x) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,totalWidth,offset] using hm.shift.wk
    have r' : Δ ⊢[PRAAx] rightBounds F (sh x) (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh J) := by
      simpa only [Δ,sh,Fm.shift,Syn.shift,subst_rightBounds] using hr.shift.wk
    let u := offset (sh i) (sh N) (sh p) (sh q) (succ (sh k))
    let a := timeNumerator zero (sh N) (sh p) (sh q) (succ (sh k))
    let b := timeDenominator (sh N) (sh q) (succ (sh k)) (sh R)
    let C := totalWidth (sh N) (sh p) (sh q) (succ (sh k))
    have read := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) f u j (sampleData (sh s) C a C b (sh x))).eqTrans
      (sample_body_at F (u+j) (sh s) C a C b (sh x))
    have row := row_norm F (sh x) (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh J) (sh L) (sh i) j
      n' ord ii jj w' m' r'
    simpa [summandsBounded,Δ,sh,Syn.shift,j,v,y,gridData,A,M,U,V,D,S,P,stepScale,panelWidth,totalWidth,offset,u,a,b,C] using
      bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) row
  have read : Γ ⊢[PRAAx] block cutF f i d y ≐ sum (offB f) M v :=
    sum_index_congr _ (congrMonus (GaussianEulerLowerTailPartition.offset_at (succ i) N p q A)
      (GaussianEulerLowerTailPartition.offset_at i N p q A))
      (congrPairT (GaussianEulerLowerTailPartition.offset_at i N p q A) (.eqRefl y))
  exact bound_congr (qmul_congr (.eqRefl w) read).eqSymm (.eqRefl _) (.eqRefl _)
    (scaled_block_bound (offB f) w v M D U V S L P (J+one) hs (literal_weight N p q k R hN hW) hRows)

theorem original_root_grid_bound (F : PR 3) (x s N p q k R J L : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q)
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)))
    (hm : Γ ⊢[PRAAx] sampledModulus F (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L x)
    (hr : Γ ⊢[PRAAx] rightBounds F x s N p q k R J) : Γ ⊢[PRAAx]
    bounded (quadratureValue F s N p q k R x)
      ((J+one)*GaussianEulerLowerTailFiniteBudget.oldNumerator N (rootDenominator N q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerTailFiniteBudget.oldDenominator (rootDenominator N q (succ k) R) (unit s)) := by
  let A := succ k
  let f := blockBody cutF (sampleBody F)
  let g := multiplyBody f
  let d := panelData s N p q k R x
  let D := rootDenominator N q A R
  let U := (J+one)*BlockNum D (stepScale p q k) L (unit s)
  let V := BlockDen D (unit s)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ hD hD) (unit_positive s)
  have rows : Γ ⊢[PRAAx] summandsBounded g N d U V := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have n' : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
    have ord : Δ ⊢[PRAAx] le (sh p) (sh q) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hpq.shift.wk
    have w' : Δ ⊢[PRAAx] le one (totalWidth (sh N) (sh p) (sh q) (succ (sh k))) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,totalWidth,offset,one] using hW.shift.wk
    have m' : Δ ⊢[PRAAx] sampledModulus F (timeNumerator zero (sh N) (sh p) (sh q) (succ (sh k)))
        (totalWidth (sh N) (sh p) (sh q) (succ (sh k))) (timeDenominator (sh N) (sh q) (succ (sh k)) (sh R)) (sh L) (sh x) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,totalWidth,offset] using hm.shift.wk
    have r' : Δ ⊢[PRAAx] rightBounds F (sh x) (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh J) := by
      simpa only [Δ,sh,Fm.shift,Syn.shift,subst_rightBounds] using hr.shift.wk
    let e := cutData (sh N) (sh p) (sh q) (succ (sh k))
    let y := gridData (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh x)
    let w := weightedPoint (sh N) (sh p) (sh q) (sh k) (sh R)
    have read := (multiply_body_at (Γ := Δ) f w i (pairT e y)).eqTrans
      (qmul_congr (.eqRefl w) (block_at cutF (sampleBody F) i e y))
    have row := panel_norm F (sh x) (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh J) (sh L) i
      n' ord Prf.hyp0 w' m' r'
    simpa [Δ,i,sh,Syn.shift,d,panelData,gridData,stepScale,U,V,D,A,g,w,e,y,totalWidth,offset,one] using
      bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) row
  have read : Γ ⊢[PRAAx] quadratureValue F s N p q k R x ≐ sum g N d :=
    (grouped_original_quadrature F s N p q A R x).eqTrans
      (sum_multiply f (weightedPoint N p q k R) N (pairT (cutData N p q A) (gridData s N p q k R x))).eqSymm
  exact bound_congr read.eqSymm
    (by dsimp only [U,D,A]; unfold GaussianEulerLowerBlockWeight.numerator GaussianEulerLowerTailFiniteBudget.oldNumerator; ipra_ring)
    (.eqRefl _) (uniform_sum_bound g N d U V hV rows)

/-- The original right-tag budget converted to dyadic root coordinates. -/
theorem original_cofinal_bound (F : PR 3) (x s t N p q k R J L : PTm n)
    (hpq : Γ ⊢[PRAAx] le p q) (hN : Γ ⊢[PRAAx] le (unit t) N)
    (hS : Γ ⊢[PRAAx] le (unit t) (unit s))
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)))
    (hm : Γ ⊢[PRAAx] sampledModulus F (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L x)
    (hr : Γ ⊢[PRAAx] rightBounds F x s N p q k R J) : Γ ⊢[PRAAx]
    bounded (quadratureValue F s N p q k R x)
      ((J+one)*GaussianEulerLowerTailFiniteBudget.numerator t p q k R L)
      (GaussianEulerLowerTailFiniteBudget.denominator t p k R) := by
  let D := rootDenominator N q (succ k) R
  let S := stepScale p q k
  let H := unit (GaussianGammaIntegralCutoffs.height p (succ k) R)
  let U := unit s
  let V := unit t
  have hN₁ := le_trans (unit_positive t) hN
  have hND := GaussianEulerLowerTailFiniteBudget.root_denominator_ge (Γ := Γ) N q k R
  have hD := le_trans hN₁ hND
  have lead : Γ ⊢[PRAAx] le (N*S*H) (succ k*D) :=
    le_congr (by unfold S H stepScale GaussianEulerLowerTailFiniteBudget.scale; ipra_ring)
      (by unfold D rootDenominator; ipra_ring)
      (mul_le_mul_right N (GaussianEulerLowerTailFiniteBudget.leading_height_budget p q k R hpq))
  have mesh := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hND (le_trans hN hND)
  have obs := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hND hS
  have cmp := GaussianEulerLowerTailFiniteBudget.cleared_radius N D S L U (succ k) H V lead mesh obs
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hD hD) (unit_positive s))
    (positive_product _ _ (unit_positive _) (unit_positive t)) ?_
    (original_root_grid_bound F x s N p q k R J L hN₁ hpq hW hm hr)
  change Γ ⊢[PRAAx] le
    (((J+one)*GaussianEulerLowerTailFiniteBudget.oldNumerator N D S L U)*GaussianEulerLowerTailFiniteBudget.nativeDenominator H V)
    (((J+one)*GaussianEulerLowerTailFiniteBudget.nativeNumerator (succ k) H S L V)*GaussianEulerLowerTailFiniteBudget.oldDenominator D U)
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (J+one) cmp)

/-- Change from the original compact coordinates to the literally scaled
rooted coordinates, with the same spatial modulus. -/
theorem rooted_modulus (F : PR 3) (x N p q k R L : PTm n)
    (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] sampledModulus F one (GaussianGammaCompactCutoffGeometry.lowerWidth p q (succ k))
      (GaussianGammaIntegralCutoffs.etaDen q (succ k) R) L x) : Γ ⊢[PRAAx]
    sampledModulus F (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L x := by
  let A := succ k
  let K := pw N A
  let C := GaussianGammaCompactCutoffGeometry.lowerWidth p q A
  let E := GaussianGammaIntegralCutoffs.etaDen q A R
  let a' := timeNumerator zero N p q A
  let C' := totalWidth N p q A
  let E' := timeDenominator N q A R
  have hK : Γ ⊢[PRAAx] le one K := GaussianPolynomialPerturbation.power_positive _ _ hN
  have raw : Γ ⊢[PRAAx] sampledModulus F (K*one) (K*C) (K*E) L x :=
    GaussianCompactIntervalRescaling.rescaled_modulus F K one C E L x hK h
  have ea : Γ ⊢[PRAAx] K*one ≐ a' :=
    (by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K).eqTrans (GaussianEulerLowerTailRootGrid.time_first N p q A).eqSymm
  have ec : Γ ⊢[PRAAx] K*C ≐ C' :=
    (mul_comm K C).eqTrans (GaussianEulerLowerTailRootGrid.time_width N p q A).eqSymm
  have ee : Γ ⊢[PRAAx] K*E ≐ E' :=
    (mul_comm K E).eqTrans (GaussianEulerLowerTailRootGrid.time_denominator N q A R).eqSymm
  simpa only [GaussianCompactRiemannName.subst_sampledModulus,Syn.subst_var,Matrix.cons_val] using
    Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (sampledModulus F (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
      ![K*one,K*C,K*E,L,x] ![a',C',E',L,x]
      (fun i => by fin_cases i; exact ea; exact ec; exact ee; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [GaussianCompactRiemannName.subst_sampledModulus,Syn.subst_var,Matrix.cons_val] using raw)

theorem rooted_width_positive (N p q k : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] lt p q) :
    Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)) := by
  have hA : Γ ⊢[PRAAx] le one (succ k) := zero_lt_succ k
  exact le_congr (.eqRefl _) (GaussianEulerLowerTailRootGrid.time_width N p q (succ k)).eqSymm
    (positive_product _ _ (GaussianGammaCompactCutoffGeometry.lower_positive p q (succ k) hA hpq)
      (GaussianPolynomialPerturbation.power_positive _ _ hN))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailRootedMajorant

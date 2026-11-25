import IPRADerivations.Analysis.GaussianBinetSecondWeightedSinePrefix
import IPRADerivations.Analysis.GaussianBinetSecondWeightedSineSuffix

/-!
# The transposed positive-frequency prefix at the original geometric indices

Only the frozen decay numerator changes between geometric columns.
The original sine schedule, positive suffix and two quadrature weights
are shared. Bounds for the individual columns therefore add directly.
-/

set_option autoImplicit false
set_option maxHeartbeats 670000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineTransposedPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentSineUniform (clock cutoff count)
open GaussianBinetBoseFrozenMatrix (subst_frozenPiNumerator subst_piDenominator)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator)
open GaussianBinetSecondWeightedSineSuffix (window scaled_grid_error)
open GaussianBinetSecondWeightedSineTranspose (transposedBody transposedData transposedValue)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field4 field5 field0_at field1_at field2_at field4_at field5_at)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply sum_index_congr)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianStirlingConstant (piDenominator)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Weighted" => GaussianBinetSecondWeightedSinePrefix.value
local notation "weightedData" => GaussianBinetSecondWeightedSinePrefix.data
local notation "weightedBody" => GaussianBinetSecondWeightedSinePrefix.body
local notation "MatrixData" => GaussianBinetSecondWeightedSineMatrix.data

def data (q k M T X Y D sign R K cut : PTm n) : PTm n :=
  let p := clock q D R T K
  let L := cutoff q T K
  let N := count q D R T K
  pairT k (pairT (monus N cut) (pairT (weight (D*L) one N)
    (transposedData p M T zero (piDenominator k) X Y D sign R L N cut)))

private def replaceNumerator (H d : PTm n) : PTm n :=
  sampleData (field0 d) (field1 d) (field2 d) H (field4 d) (field5 d)

@[simp] private theorem subst_replaceNumerator {m : ℕ} (σ : Fin n → PTm m) (H d : PTm n) :
    Syn.subst σ (replaceNumerator H d) = replaceNumerator (Syn.subst σ H) (Syn.subst σ d) := by simp [replaceNumerator]

private def term (j d : PTm n) : PTm n :=
  let y := sndT d
  let z := sndT y
  let w := sndT z
  let x := sndT w
  let H := frozenPiNumerator (succ j) (fstT d)
  qmul (fstT z) (sum transposedBody (fstT y) (pairT (fstT w) (pairT (fstT x) (replaceNumerator H (sndT x)))))

@[simp] private theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (j d : PTm n) :
    Syn.subst σ (term j d) = term (Syn.subst σ j) (Syn.subst σ d) := by simp [term]

def body : PTm 2 := term (var 0) (var 1)
def transposedPrefix (q k I M T X Y D sign R K cut : PTm n) : PTm n :=
  sum body I (data q k M T X Y D sign R K cut)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (q k M T X Y D sign R K cut : PTm n) :
    Syn.subst σ (data q k M T X Y D sign R K cut) =
      data (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ T) (Syn.subst σ X) (Syn.subst σ Y)
        (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ K) (Syn.subst σ cut) := by simp [data,one]

@[simp] theorem subst_transposedPrefix {m : ℕ} (σ : Fin n → PTm m) (q k I M T X Y D sign R K cut : PTm n) :
    Syn.subst σ (transposedPrefix q k I M T X Y D sign R K cut) =
      transposedPrefix (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ I) (Syn.subst σ M) (Syn.subst σ T)
        (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ K)
        (Syn.subst σ cut) := by simp [transposedPrefix]

private theorem replace_at (H p M T J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] replaceNumerator H (MatrixData p M T zero J X Y D sign R L N cut) ≐
      MatrixData p M T H J X Y D sign R L N cut :=
  congrPairT (field0_at _ _ _ _ _ _) (congrPairT (field1_at _ _ _ _ _ _)
    (congrPairT (field2_at _ _ _ _ _ _) (congrPairT (.eqRefl H)
      (congrPairT (field4_at _ _ _ _ _ _) (field5_at _ _ _ _ _ _)))))

theorem row_at (j q k M T X Y D sign R K cut : PTm n) :
    let p := clock q D R T K
    let L := cutoff q T K
    let N := count q D R T K
    Γ ⊢[PRAAx] inst2 body j (data q k M T X Y D sign R K cut) ≐
      transposedValue p M T (frozenPiNumerator (succ j) k) (piDenominator k) X Y D sign R L N cut := by
  let p := clock q D R T K
  let L := cutoff q T K
  let N := count q D R T K
  let H := frozenPiNumerator (succ j) k
  let J := piDenominator k
  let C := monus N cut
  let W := weight (D*L) one N
  let V := qmul (fraction two one) (weight T one M)
  let B := MatrixData p M T zero J X Y D sign R L N cut
  let B' := MatrixData p M T H J X Y D sign R L N cut
  let d := data q k M T X Y D sign R K cut
  let y := sndT d
  let z := sndT y
  let w := sndT z
  let x := sndT w
  have ek : Γ ⊢[PRAAx] fstT d ≐ k := fst_pair _ _
  have ey : Γ ⊢[PRAAx] y ≐ pairT C (pairT W (pairT V (pairT M B))) := snd_pair _ _
  have ez : Γ ⊢[PRAAx] z ≐ pairT W (pairT V (pairT M B)) := (congrSnd ey).eqTrans (snd_pair _ _)
  have ew : Γ ⊢[PRAAx] w ≐ pairT V (pairT M B) := (congrSnd ez).eqTrans (snd_pair _ _)
  have ex : Γ ⊢[PRAAx] x ≐ pairT M B := (congrSnd ew).eqTrans (snd_pair _ _)
  have eh : Γ ⊢[PRAAx] frozenPiNumerator (succ j) (fstT d) ≐ H := by
    simpa only [H,subst_frozenPiNumerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (frozenPiNumerator (Syn.shift (succ j)) (var 0)) ek
  have eb : Γ ⊢[PRAAx] sndT x ≐ B := (congrSnd ex).eqTrans (snd_pair _ _)
  have matrix : Γ ⊢[PRAAx] replaceNumerator (frozenPiNumerator (succ j) (fstT d)) (sndT x) ≐ B' := by
    have mid : Γ ⊢[PRAAx] replaceNumerator (frozenPiNumerator (succ j) (fstT d)) (sndT x) ≐ replaceNumerator H B := by
      simpa only [subst_replaceNumerator,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
        Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (replaceNumerator (var 0) (var 1) : PTm 2)
          (σ := ![frozenPiNumerator (succ j) (fstT d),sndT x]) (σ' := ![H,B])
          (fun i => by fin_cases i; exact eh; exact eb)
    exact mid.eqTrans (replace_at H p M T J X Y D sign R L N cut)
  have read : inst2 body j d = term j d := by
    simp only [inst2,body,subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [read]
  exact qmul_congr ((congrFst ez).eqTrans (fst_pair _ _))
    (sum_index_congr transposedBody ((congrFst ey).eqTrans (fst_pair _ _))
      (congrPairT ((congrFst ew).eqTrans (fst_pair _ _)) (congrPairT ((congrFst ex).eqTrans (fst_pair _ _)) matrix)))

theorem prefix_error (q k I M T X Y D sign R K cut E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M)
    (hw : Γ ⊢[PRAAx] window q D R T K cut E) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction two one) (Weighted q k I M T X Y D sign R K))
      (transposedPrefix q k I M T X Y D sign R K cut) (I*(num 32*T*(T+one))) E := by
  let c : PTm n := fraction two one
  let g := multiplyBody weightedBody
  let x := weightedData q k M T X Y D sign R K
  let y := data q k M T X Y D sign R K cut
  let C := two*(T*GaussianBinetSecondWeightedSineSuffix.cost T)
  have rows : Γ ⊢[PRAAx] termsDistance g body I (pairT c x) y C E := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let j : PTm (n+1) := var 0
    let Δ := lt j (s I)::Γ.map Fm.shift
    let H := frozenPiNumerator (succ j) (s k)
    let J := piDenominator (s k)
    have z : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
      by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have ws : Δ ⊢[PRAAx] window (s q) (s D) (s R) (s T) (s K) (s cut) (s E) :=
      by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetSecondWeightedSineSuffix.subst_window] using hw.shift.wk
    have js : Δ ⊢[PRAAx] le one J := GaussianBinetKernelPi.denominator_positive (s k)
    have first := (multiply_body_at (Γ := Δ) weightedBody (fraction two one) j
      (weightedData (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign) (s R) (s K))).eqTrans
      (qmul_congr (.eqRefl _) (GaussianBinetSecondWeightedSinePrefix.column_at j
        (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign) (s R) (s K)))
    have next := row_at (Γ := Δ) j (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign) (s R) (s K) (s cut)
    have step := scaled_grid_error (s q) (s M) (s T) H J (s X) (s Y) (s D) (s sign) (s R) (s K) (s cut) (s E) z ms js ws
    simpa only [Δ,s,j,x,y,c,C,g,Syn.shift,subst_data,GaussianBinetSecondWeightedSinePrefix.subst_data,subst_pairT,
      GaussianPositiveRationalLogarithm.subst_fraction,GaussianBinetSecondWeightedSineSuffix.subst_cost,
      PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
      distance_congr first.eqSymm next.eqSymm (.eqRefl _) (.eqRefl _) step
  exact distance_congr (sum_multiply weightedBody c I x) (.eqRefl _)
    (by dsimp only [C,GaussianBinetSecondWeightedSineSuffix.cost]; ipra_ring) (.eqRefl _)
    (sum_distance g body I (pairT c x) y C E hw.andE₂.andE₁ rows)

theorem actual_second_Binet_transposed_prefix_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (let q := var 0
       let k := var 1
       let I := var 2
       let M := var 3
       let T := var 4
       let X := var 5
       let Y := var 6
       let D := var 7
       let sign := var 8
       let R := var 9
       let K := var 10
       let cut := var 11
       let E := var 12
       (source X Y D sign R ⋏ le one M) ⋏ window q D R T K cut E ⟶
         distanceBounded (qmul (fraction two one) (Weighted q k I M T X Y D sign R K))
           (transposedPrefix q k I M T X Y D sign R K cut) (I*(num 32*T*(T+one))) E) :=
  closeUniv 13 (.impI (prefix_error _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineTransposedPrefix

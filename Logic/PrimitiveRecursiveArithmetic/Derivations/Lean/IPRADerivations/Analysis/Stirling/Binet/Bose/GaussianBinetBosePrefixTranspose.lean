import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBosePrefixQuadrature
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFubini

/-!
# Exchange the finite Bose exponential count with the time mesh

The original positive-time quadrature reads a literal exponential
prefix at each tag. Distribute its original arctangent observation
through that sum, then transpose the finite Gaussian matrix. Each
entry retains the exact tag-dependent exponential observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixTranspose

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBosePrefixQuadrature (evaluatorF evaluatorTerm subst_evaluatorTerm)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5 grid sampleBody sampleData quadrature)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply termsEqual)
open GaussianRationalFubini (row rowBody row_entry row_sum_at rowFirst columnFirst)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "clock" => GaussianBinetBoseLiteralUniform.clock
local notation "Prefix" => GaussianBinetBoseLiteralPrefix.body
local notation "parameters" => GaussianBinetBoseLiteralPrefix.parameters

def tag (i d : PTm n) : PTm n := grid i (field1 d) (field2 d) (field3 d) (field4 d)
def prefixLength (d : PTm n) : PTm n := fstT (field5 d)

def decodedAngle (p x t : PTm n) : PTm n :=
  ap2 Atan p (atanData (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) (tagNumerator t) (sndT t))

def rowData (p N x t : PTm n) : PTm n :=
  let A := tagNumerator t
  let B := sndT t
  pairT (decodedAngle p x t) (parameters (clock p N A B) A B)

def term (i j d : PTm n) : PTm n :=
  inst2 (multiplyBody Prefix) j (rowData (field0 d) (prefixLength d) (sndT (field5 d)) (tag i d))
def matrix : PTm 3 := term (var 0) (var 1) (var 2)
def data (p M N X Y D sign A C E : PTm n) : PTm n := sampleData p M (E+A) C E (pairT N (fixedData X Y D sign))

@[simp] theorem subst_tag {m : ℕ} (σ : Fin n → PTm m) (i d : PTm n) :
    Syn.subst σ (tag i d) = tag (Syn.subst σ i) (Syn.subst σ d) := by simp [tag]
@[simp] theorem subst_prefixLength {m : ℕ} (σ : Fin n → PTm m) (d : PTm n) :
    Syn.subst σ (prefixLength d) = prefixLength (Syn.subst σ d) := by simp [prefixLength]
@[simp] theorem subst_decodedAngle {m : ℕ} (σ : Fin n → PTm m) (p x t : PTm n) :
    Syn.subst σ (decodedAngle p x t) = decodedAngle (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ t) := by
  simp [decodedAngle]
@[simp] theorem subst_rowData {m : ℕ} (σ : Fin n → PTm m) (p N x t : PTm n) :
    Syn.subst σ (rowData p N x t) = rowData (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ t) := by
  simp [rowData,GaussianBinetBoseLiteralUniform.clock]
@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (i j d : PTm n) :
    Syn.subst σ (term i j d) = term (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ d) := by simp [term]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p M N X Y D sign A C E : PTm n) :
    Syn.subst σ (data p M N X Y D sign A C E) = data (Syn.subst σ p) (Syn.subst σ M) (Syn.subst σ N)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) :=
  by simp [data]

theorem matrix_at (i j d : PTm n) : inst3 matrix i j d = term i j d := by
  simp only [matrix,inst3,subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]

private theorem row_samples (i N d : PTm n) : Γ ⊢[PRAAx]
    row matrix i N d ≐ sum (multiplyBody Prefix) N (rowData (field0 d) (prefixLength d) (sndT (field5 d)) (tag i d)) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have e := row_entry (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) matrix (Syn.shift i) (var 0) (Syn.shift d)
  rw [matrix_at] at e
  simpa only [termsEqual,Syn.shift,subst_pairT,subst_rowData,GaussianCompactRiemannName.subst_field0,
    GaussianCompactRiemannName.subst_field5,subst_prefixLength,subst_tag,subst_sndT,term] using e

private theorem actual_row_at (i d : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i d ≐ row matrix i (prefixLength d) d := by
  let t := tag i d
  let p := field0 d
  let N := prefixLength d
  let x := sndT (field5 d)
  let A := tagNumerator t
  let B := sndT t
  let c := ap2 Atan p (atanData (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) A B)
  have read : Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) i d ≐ evaluatorTerm p t (field5 d) := by
    simpa only [GaussianCompactRiemannName.sample_entry,evaluatorF,ap3,t,p,tag,subst_evaluatorTerm,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,field5 d]
  have expand := sum_multiply (Γ := Γ) Prefix c N (parameters (clock p N A B) A B)
  exact read.eqTrans (expand.eqSymm.eqTrans (row_samples i N d).eqSymm)

private theorem prefix_length_at (p M N X Y D sign A C E : PTm n) : Γ ⊢[PRAAx]
    prefixLength (data p M N X Y D sign A C E) ≐ N :=
  (congrFst (GaussianCompactRiemannName.field5_at p M (E+A) C E (pairT N (fixedData X Y D sign)))).eqTrans
    (fst_pair _ _)

theorem quadrature_transpose (p M N X Y D sign A C E : PTm n) : Γ ⊢[PRAAx]
    quadrature evaluatorF p M (E+A) C E (pairT N (fixedData X Y D sign)) ≐
      qmul (weight C E M) (columnFirst matrix M N (data p M N X Y D sign A C E)) := by
  let d := data p M N X Y D sign A C E
  have rows : Γ ⊢[PRAAx] termsEqual (sampleBody evaluatorF) (GaussianRationalFubini.rowSumBody matrix) M d (pairT N d) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
    let d' := data (s p) (s M) (s N) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E)
    have hN := prefix_length_at (Γ := Δ) (s p) (s M) (s N) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E)
    have exactRow := (actual_row_at (Γ := Δ) (var 0) d').eqTrans
      (GaussianRationalFiniteSum.sum_index_congr (rowBody matrix) hN (.eqRefl _))
    simpa only [termsEqual,d,s,Δ,d',Syn.shift,subst_data,subst_pairT] using
      exactRow.eqTrans (row_sum_at matrix (var 0) (s N) d').eqSymm
  have sums : Γ ⊢[PRAAx] sum (sampleBody evaluatorF) M d ≐ rowFirst matrix M N d :=
    GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows
  exact qmul_congr (.eqRefl _) (sums.eqTrans (GaussianRationalFubini.fubini matrix M N d))

private theorem rowData_congr {p q N H x y t u : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q) (hN : Γ ⊢[PRAAx] N ≐ H)
    (hx : Γ ⊢[PRAAx] x ≐ y) (ht : Γ ⊢[PRAAx] t ≐ u) : Γ ⊢[PRAAx] rowData p N x t ≐ rowData q H y u := by
  simpa only [subst_rowData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rowData (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,N,x,t]) (σ' := ![q,H,y,u]) (fun i => by fin_cases i; exact hp; exact hN; exact hx; exact ht)

private theorem val_4 {α : Type} (a b c d e f g : α) : ![a,b,c,d,e,f,g] (4 : Fin 7) = e := rfl
private theorem val_5 {α : Type} (a b c d e f g : α) : ![a,b,c,d,e,f,g] (5 : Fin 7) = f := rfl
private theorem val_6 {α : Type} (a b c d e f g : α) : ![a,b,c,d,e,f,g] (6 : Fin 7) = g := rfl

theorem decoded_angle_at (p t X Y D sign : PTm n) : Γ ⊢[PRAAx]
    decodedAngle p (fixedData X Y D sign) t ≐ ap2 Atan p (atanData X Y D sign (tagNumerator t) (sndT t)) := by
  let x := fixedData X Y D sign
  let a := tagNumerator t
  let b := sndT t
  have yz : Γ ⊢[PRAAx] sndT x ≐ pairT Y (pairT D sign) := snd_pair _ _
  have ds : Γ ⊢[PRAAx] sndT (sndT x) ≐ pairT D sign := (congrSnd yz).eqTrans (snd_pair _ _)
  have coords := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (ap2 Atan (var 0) (atanData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) : PTm 7)
    (σ := ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x)),a,b])
    (σ' := ![p,X,Y,D,sign,a,b]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst yz).eqTrans (fst_pair _ _)
      exact (congrFst ds).eqTrans (fst_pair _ _)
      exact (congrSnd ds).eqTrans (snd_pair _ _)
      exact (Prf.eqRefl a : Γ ⊢[PRAAx] a ≐ a)
      exact (Prf.eqRefl b : Γ ⊢[PRAAx] b ≐ b))
  simpa only [decodedAngle,a,b,subst_ap2,GaussianBinetArctangentQuadrature.subst_data,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,val_4,val_5,val_6,Matrix.head_cons,Matrix.tail_cons] using coords

/-- Exact angular and literal exponential observations in a transposed cell. -/
theorem cell_at (i j p M N X Y D sign A C E : PTm n) : Γ ⊢[PRAAx]
    term i j (data p M N X Y D sign A C E) ≐
      qmul (ap2 Atan p (atanData X Y D sign (tagNumerator (grid i M (E+A) C E)) (sndT (grid i M (E+A) C E))))
        (GaussianBinetBoseLiteralPrefix.term j (clock p N (tagNumerator (grid i M (E+A) C E)) (sndT (grid i M (E+A) C E)))
          (tagNumerator (grid i M (E+A) C E)) (sndT (grid i M (E+A) C E))) := by
  let d := data p M N X Y D sign A C E
  let x := fixedData X Y D sign
  let t := grid i M (E+A) C E
  let a := tagNumerator t
  let b := sndT t
  let c := ap2 Atan p (atanData X Y D sign a b)
  have hX : Γ ⊢[PRAAx] sndT (field5 d) ≐ x :=
    (congrSnd (GaussianCompactRiemannName.field5_at p M (E+A) C E (pairT N x))).eqTrans (snd_pair _ _)
  have ht : Γ ⊢[PRAAx] tag i d ≐ t := GaussianCompactRiemannName.grid_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _)
    (GaussianCompactRiemannName.field1_at p M (E+A) C E (pairT N x))
    (GaussianCompactRiemannName.field2_at p M (E+A) C E (pairT N x))
    (GaussianCompactRiemannName.field3_at p M (E+A) C E (pairT N x))
    (GaussianCompactRiemannName.field4_at p M (E+A) C E (pairT N x))
  have read := rowData_congr (GaussianCompactRiemannName.field0_at (Γ := Γ) p M (E+A) C E (pairT N x))
    (prefix_length_at p M N X Y D sign A C E) hX ht
  have rd : Γ ⊢[PRAAx] rowData p N x t ≐ pairT c (parameters (clock p N a b) a b) :=
    congrPairT (decoded_angle_at p t X Y D sign) (.eqRefl _)
  have terms : Γ ⊢[PRAAx] term i j d ≐ inst2 (multiplyBody Prefix) j (pairT c (parameters (clock p N a b) a b)) :=
    congrInst2 (multiplyBody Prefix) (.eqRefl j) (read.eqTrans rd)
  exact terms.eqTrans ((multiply_body_at Prefix c j (parameters (clock p N a b) a b)).eqTrans
    (qmul_congr (.eqRefl _) (GaussianBinetBoseLiteralPrefix.row_at j (clock p N a b) a b)))

end LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixTranspose

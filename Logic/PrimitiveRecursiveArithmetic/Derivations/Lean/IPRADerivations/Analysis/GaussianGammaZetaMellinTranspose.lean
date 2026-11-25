import IPRADerivations.Analysis.GaussianGammaZetaMellinStrip
import IPRADerivations.Analysis.GaussianRationalFubini

/-!
# Transpose the original finite Mellin strip sum

After exact finite interchange, each positive decay index carries an
Euler quadrature on the unchanged time mesh. Its integrand uses the
shared original power and the actual decay at the scaled time.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinTranspose

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5
  field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianGammaZetaMellinDecayPrefix
  (powerSample weightedValue weighted_sum_at weighted_term_at parameters)
open GaussianGammaZetaMellinIntegrand (factorClock)
open GaussianGammaZetaMellinStrip (data decayBody decayValue decay_row_at)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply termsEqual)
open GaussianRationalFubini (column columnBody column_entry columnSumBody column_sum_at rowBody row_entry rowSumBody row_sum_at)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cell (j i p z D M A C E : PTm n) : PTm n :=
  let a := A*M+C*i
  let b := E*M
  qmul (powerSample p z D a b) (GaussianGammaZetaMellinDecayPrefix.term j (factorClock p z D a b) a b)

def matrix : PTm 3 :=
  let d : PTm 3 := var 2
  cell (var 0) (var 1) (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
    (field1 d) (field2 d) (field3 d) (field4 d)

abbrev transposedBody : PTm 2 := multiplyBody (rowSumBody matrix)
def transposedData (p z D M N A C E : PTm n) : PTm n :=
  pairT (weight C E M) (pairT M (data p z D M N A C E))
def transposedValue (p z D M N A C E : PTm n) : PTm n :=
  sum transposedBody N (transposedData p z D M N A C E)

@[simp] theorem subst_cell {m : ℕ} (σ : Fin n → PTm m) (j i p z D M A C E : PTm n) :
    Syn.subst σ (cell j i p z D M A C E) = cell (Syn.subst σ j) (Syn.subst σ i) (Syn.subst σ p)
      (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by
  simp [cell,factorClock]

@[simp] theorem subst_transposedData {m : ℕ} (σ : Fin n → PTm m) (p z D M N A C E : PTm n) :
    Syn.subst σ (transposedData p z D M N A C E) =
      transposedData (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ N)
        (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [transposedData]

@[simp] theorem subst_transposedValue {m : ℕ} (σ : Fin n → PTm m) (p z D M N A C E : PTm n) :
    Syn.subst σ (transposedValue p z D M N A C E) =
      transposedValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ N)
        (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [transposedValue]

theorem cell_at (j i p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst3 matrix j i (data p z D M N A C E) ≐ cell j i p z D M A C E := by
  let d := data p z D M N A C E
  have raw : inst3 matrix j i d =
      cell j i (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
        (field1 d) (field2 d) (field3 d) (field4 d) := by simp [matrix,inst3]
  rw [raw]
  let code : PTm 9 := cell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
  let x : Fin 9 → PTm n := ![j,i,field0 d,fstT (sndT (field5 d)),sndT (sndT (field5 d)),field1 d,field2 d,field3 d,field4 d]
  let y : Fin 9 → PTm n := ![j,i,p,z,D,M,A,C,E]
  have hp : Γ ⊢[PRAAx] field5 d ≐ pairT N (pairT z D) := field5_at _ _ _ _ _ _
  have hd := (congrSnd hp).eqTrans (snd_pair N (pairT z D))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) code (σ := x) (σ' := y) (fun s => by
    fin_cases s
    · exact .eqRefl j
    · exact .eqRefl i
    · exact field0_at _ _ _ _ _ _
    · exact (congrFst hd).eqTrans (fst_pair _ _)
    · exact (congrSnd hd).eqTrans (snd_pair _ _)
    · exact field1_at _ _ _ _ _ _
    · exact field2_at _ _ _ _ _ _
    · exact field3_at _ _ _ _ _ _
    · exact field4_at _ _ _ _ _ _)
  have left : Syn.subst x code =
      cell j i (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
        (field1 d) (field2 d) (field3 d) (field4 d) := by
    dsimp only [code]
    rw [subst_cell]
    rfl
  have right : Syn.subst y code = cell j i p z D M A C E := by
    dsimp only [code]
    rw [subst_cell]
    rfl
  rw [left,right] at read
  exact read

private theorem column_at (i p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] column matrix i N (data p z D M N A C E) ≐ weightedValue p z D (A*M+C*i) (E*M) N := by
  let d := data p z D M N A C E
  let a := A*M+C*i
  let b := E*M
  let k := factorClock p z D a b
  let x := pairT (powerSample p z D a b) (parameters k a b)
  let G := multiplyBody GaussianGammaZetaMellinDecayPrefix.body
  have rows : Γ ⊢[PRAAx] termsEqual (columnBody matrix) G N (pairT i d) x := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    let d' := data (s p) (s z) (s D) (s M) (s N) (s A) (s C) (s E)
    have left := (column_entry (Γ := Δ) matrix (var 0) (s i) d').eqTrans
      (cell_at (var 0) (s i) (s p) (s z) (s D) (s M) (s N) (s A) (s C) (s E))
    have right := weighted_term_at (Γ := Δ) (var 0) (s p) (s z) (s D) (s A*s M+s C*s i) (s E*s M)
    simpa only [d,x,k,a,b,G,s,Δ,d',Syn.shift,GaussianGammaZetaMellinStrip.subst_data,subst_pairT,
      GaussianGammaZetaMellinDecayPrefix.subst_powerSample,GaussianGammaZetaMellinDecayPrefix.subst_parameters,
      factorClock,GaussianFastValueCut.subst_exponent,GaussianNameArithmetic.subst_multiplyModulus,
      GaussianEulerIntegrandName.subst_powerData,GaussianGammaZetaMellinIntegrand.subst_reciprocalData,
      PTm.subst_add,PTm.subst_mul] using left.eqTrans right.eqSymm
  have read := GaussianRationalFiniteSum.sum_congr_bounded (columnBody matrix) G N (pairT i d) x rows
  exact read.eqTrans (weighted_sum_at p z D a b N).eqSymm

theorem decay_index_cell (j i p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowBody matrix) i (pairT j (data p z D M N A C E)) ≐ cell j i p z D M A C E :=
  (row_entry matrix j i _).eqTrans (cell_at j i p z D M N A C E)

theorem decay_index_at (j p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst2 transposedBody j (transposedData p z D M N A C E) ≐
      qmul (weight C E M) (GaussianRationalFubini.row matrix j M (data p z D M N A C E)) :=
  (multiply_body_at (rowSumBody matrix) (weight C E M) j (pairT M (data p z D M N A C E))).eqTrans
    (qmul_congr (.eqRefl _) (row_sum_at matrix j M (data p z D M N A C E)))

theorem transpose (p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] decayValue p z D M N A C E ≐ transposedValue p z D M N A C E := by
  let d := data p z D M N A C E
  let w := weight C E M
  have cols : Γ ⊢[PRAAx] termsEqual (columnSumBody matrix) decayBody M (pairT N d) d := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    let d' := data (s p) (s z) (s D) (s M) (s N) (s A) (s C) (s E)
    have left := (column_sum_at (Γ := Δ) matrix (var 0) (s N) d').eqTrans
      (column_at (var 0) (s p) (s z) (s D) (s M) (s N) (s A) (s C) (s E))
    have right := decay_row_at (Γ := Δ) (var 0) (s p) (s z) (s D) (s M) (s N) (s A) (s C) (s E)
    simpa only [d,d',s,Δ,Syn.shift,subst_pairT,GaussianGammaZetaMellinStrip.subst_data] using
      left.eqTrans right.eqSymm
  have decay : Γ ⊢[PRAAx] GaussianRationalFubini.columnFirst matrix N M d ≐ sum decayBody M d :=
    GaussianRationalFiniteSum.sum_congr_bounded (columnSumBody matrix) decayBody M (pairT N d) d cols
  have order := (GaussianRationalFubini.fubini (Γ := Γ) matrix N M d).eqTrans decay
  exact (qmul_congr (.eqRefl w) order.eqSymm).eqTrans (sum_multiply (rowSumBody matrix) w N (pairT M d)).eqSymm

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinTranspose

import IPRADerivations.Analysis.Polynomials.CompanionMatrices.RationalPolynomialMonicNorm
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticTail
import IPRADerivations.Foundations.SequenceEquality
import IPRADerivations.Core.CongruenceTactic

/-!
# The original rational coefficient table of Y^m - f(X)

The original rational program computes the zero rows and the final row
with original rational negation. Embedding gives the literal Gaussian
tail table used in the existing cyclic-leading norm theorem. The
outer code equality is for these actual constructed sequences.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSuperellipticTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarOne)
open RationalPolynomialGaussianEmbedding (coefficients embed_congr coefficients_length)
open RationalPolynomialBuffersGaussianEmbedding (zeros scaled)
open RationalPolynomialDeterminantTermsGaussianEmbedding (entriesEqual entry_equal_at coefficients_congr)
open GaussianPolynomialMonicCompanion (rowShape)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (append appendBody append_left append_right_at append_length length entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open LeanProofs.IPRA.PTm (pred)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def negative (f : PTm n) : PTm n := scaled f (RationalArithmetic.negative scalarOne)
def zeroRows (m c : PTm n) : PTm n := sequence (var 1) (pred m) (zeros (succ c))
def tailRows (f m c : PTm n) : PTm n := append (zeroRows m c) (singleton (negative f))

@[simp] theorem subst_negative {l : ℕ} (σ : Fin n → PTm l) (f : PTm n) :
    Syn.subst σ (negative f) = negative (Syn.subst σ f) := by simp [negative]
@[simp] theorem subst_zeroRows {l : ℕ} (σ : Fin n → PTm l) (m c : PTm n) :
    Syn.subst σ (zeroRows m c) = zeroRows (Syn.subst σ m) (Syn.subst σ c) := by simp [zeroRows]
@[simp] theorem subst_tailRows {l : ℕ} (σ : Fin n → PTm l) (f m c : PTm n) :
    Syn.subst σ (tailRows f m c) = tailRows (Syn.subst σ f) (Syn.subst σ m) (Syn.subst σ c) := by simp [tailRows]

theorem zero_rows_length (m c : PTm n) : Γ ⊢[PRAAx] length (zeroRows m c) ≐ pred m := sequence_length _ _ _
theorem tail_length (f m c : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] length (tailRows f m c) ≐ m :=
  (append_length _ _).eqTrans ((congrAdd (zero_rows_length m c) (singleton_length _)).eqTrans
    ((succ_eq_add_one _).eqSymm.eqTrans (RationalIntegerNormalization.positive_form hm).eqSymm))

theorem upper_row (f m c r : PTm n) (hr : Γ ⊢[PRAAx] lt r (pred m)) :
    Γ ⊢[PRAAx] entry (tailRows f m c) r ≐ zeros (succ c) := by
  have src := append_left (b := singleton (negative f))
    (lt_congr (.eqRefl _) (zero_rows_length m c).eqSymm hr)
  have dst : Γ ⊢[PRAAx] entry (zeroRows m c) r ≐ zeros (succ c) := by
    simpa [zeroRows,inst2] using sequence_decode (var 1 : PTm 2) (x := zeros (succ c)) hr
  exact src.eqTrans dst

theorem last_row (f m c : PTm n) : Γ ⊢[PRAAx] entry (tailRows f m c) (pred m) ≐ negative f := by
  let Z := zeroRows m c
  let U := singleton (negative f)
  let r := pred m
  have len : Γ ⊢[PRAAx] length Z ≐ r := zero_rows_length _ _
  have hi : Γ ⊢[PRAAx] lt r (length Z+length U) :=
    lt_congr (.eqRefl _) ((succ_eq_add_one r).eqTrans (congrAdd len.eqSymm (singleton_length _).eqSymm)) (le_refl _)
  exact (append_right_at (le_congr len.eqSymm (.eqRefl _) (le_refl _)) hi).eqTrans
    ((entry_congr (.eqRefl _) ((congrMonus (.eqRefl _) len).eqTrans (monus_self r))).eqTrans (singleton_lookup _))

private theorem row_cases (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] lt r (pred m) ⋎ (r ≐ pred m) :=
  lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans
    (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form (lt_of_le_of_lt (zero_le r) hr)) hr))

theorem row_length (f m c r : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] length (entry (tailRows f m c) r) ≐ succ c := by
  refine .orE (row_cases m r hr) ?_ ?_
  · exact (congrFst (upper_row _ _ _ _ Prf.hyp0)).eqTrans (RationalPolynomialBuffersGaussianEmbedding.zeros_length _)
  · exact (congrFst ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (last_row _ _ _))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.scaled_length _ _).eqTrans hf.wk)

theorem tail_shape (f m c : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c) :
    Γ ⊢[PRAAx] rowShape (tailRows f m c) m c := by
  refine .allI (.impI ?_)
  have hf' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hf.shift
  simpa [Syn.shift] using row_length (Syn.shift f) (Syn.shift m) (Syn.shift c) (var 0) hf'.wk Prf.hyp0

private theorem sequence_width_congr (b : PTm 2) (x : PTm n) {N M : PTm n} (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] sequence b N x ≐ sequence b M x := by
  ipra_congr (sequence b (var 0) (var 1) : PTm 2) with [h, .eqRefl x]

/-- Only constructed sequences are compared by their protected entries. -/
private theorem sequence_layout_equal (A B N M x y : PTm n) (p q : PTm 2)
    (ha : Γ ⊢[PRAAx] A ≐ sequence p N x) (hb : Γ ⊢[PRAAx] B ≐ sequence q M y)
    (hn : Γ ⊢[PRAAx] N ≐ M) (he : Γ ⊢[PRAAx] entriesEqual A B N) : Γ ⊢[PRAAx] A ≐ B := by
  have H : Γ ⊢[PRAAx] agree p q N x y := by
    refine .allI (.impI ?_)
    let D := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have sa : D ⊢[PRAAx] Syn.shift A ≐ sequence p (Syn.shift N) (Syn.shift x) := by simpa [D,Fm.shift,Syn.shift] using ha.shift.wk
    have sb : D ⊢[PRAAx] Syn.shift B ≐ sequence q (Syn.shift M) (Syn.shift y) := by simpa [D,Fm.shift,Syn.shift] using hb.shift.wk
    have same : D ⊢[PRAAx] Syn.shift N ≐ Syn.shift M := by simpa [D,Fm.shift,Syn.shift] using hn.shift.wk
    have es : D ⊢[PRAAx] entriesEqual (Syn.shift A) (Syn.shift B) (Syn.shift N) := by simpa [D,Fm.shift,Syn.shift] using he.shift.wk
    have a := (entry_congr sa (.eqRefl (var 0))).eqTrans (sequence_decode p (x := Syn.shift x) Prf.hyp0)
    have b := (entry_congr sb (.eqRefl (var 0))).eqTrans (sequence_decode q (x := Syn.shift y) (lt_congr (.eqRefl _) same Prf.hyp0))
    exact a.eqSymm.eqTrans ((entry_equal_at _ _ _ _ es Prf.hyp0).eqTrans b)
  exact ha.eqTrans ((sequence_equal p q N x y H).eqTrans ((sequence_width_congr q y hn).eqTrans hb.eqSymm))

private theorem negative_embedded (f c s : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hs : Γ ⊢[PRAAx] lt s (succ c)) : Γ ⊢[PRAAx]
    embed (entry (negative f) s) ≐ entry (GaussianRationalGridCoefficientEquality.negativePolynomial (coefficients f (succ c))) s := by
  let G := coefficients f (succ c)
  have hi := lt_congr (.eqRefl _) hf.eqSymm hs
  have l := RationalPolynomialBuffersGaussianEmbedding.scaled_embedding f (RationalArithmetic.negative scalarOne) s hi
  have g := coefficients_congr (.eqRefl f) hf
  have sign : Γ ⊢[PRAAx] embed (RationalArithmetic.negative scalarOne) ≐ GaussianRationalMatrixFiniteSums.minusOne :=
    (RationalGaussianEmbedding.embed_negative scalarOne).eqTrans
    (RationalGaussianEmbedding.negative_congr RationalGaussianEmbedding.embed_one)
  have transported : Γ ⊢[PRAAx] GaussianRationalCoefficientScaling.scaled (coefficients f (length f))
      (embed (RationalArithmetic.negative scalarOne)) ≐ GaussianRationalGridCoefficientEquality.negativePolynomial G :=
    (GaussianRationalCoefficientScaling.program_at _ _).eqSymm.eqTrans
      ((congrAp2 GaussianRationalCoefficientScaling.scaledF g sign).eqTrans (GaussianRationalCoefficientScaling.program_at _ _))
  exact l.eqTrans (entry_congr transported (.eqRefl _))

theorem coefficient_embedding (f m c r s : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] lt s (succ c)) : Γ ⊢[PRAAx]
    embed (entry (entry (tailRows f m c) r) s) ≐ entry (entry
      (GaussianSuperellipticTail.tailRows (coefficients f (succ c)) m c) r) s := by
  let f' := coefficients f (succ c)
  refine .orE (row_cases m r hr) ?_ ?_
  · exact (embed_congr (entry_congr (upper_row f m c r Prf.hyp0) (.eqRefl _))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ _ hs.wk).eqTrans
        (entry_congr (GaussianSuperellipticTail.upper_row f' m c r Prf.hyp0).eqSymm (.eqRefl _)))
  · let Δ := (r ≐ pred m) :: Γ
    have orig : Δ ⊢[PRAAx] entry (tailRows f m c) r ≐ negative f :=
      (entry_congr (.eqRefl _) Prf.hyp0).eqTrans (last_row f m c)
    have dest : Δ ⊢[PRAAx] entry (GaussianSuperellipticTail.tailRows f' m c) r ≐
        GaussianRationalGridCoefficientEquality.negativePolynomial f' :=
      (entry_congr (.eqRefl _) Prf.hyp0).eqTrans
      (GaussianSuperellipticTail.last_row f' m c)
    exact (embed_congr (entry_congr orig (.eqRefl _))).eqTrans
      ((negative_embedded f c s hf.wk hs.wk).eqTrans (entry_congr dest.eqSymm (.eqRefl _)))

private theorem mapped_row_equal (f m c r : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] entry (RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c)) r ≐
      entry (GaussianSuperellipticTail.tailRows (coefficients f (succ c)) m c) r := by
  let M := RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c)
  let f' := coefficients f (succ c)
  let T := GaussianSuperellipticTail.tailRows f' m c
  let B := RationalRowSpanGaussianEmbedding.matrixBody
  let R := GaussianRationalFiberVandermonde.rowBody B
  let x := pairT r (tailRows f m c)
  have same : Γ ⊢[PRAAx] entriesEqual (entry M r) (entry T r) (succ c) := by
    refine .allI (.impI ?_)
    have fs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by
      simpa [Fm.shift,Syn.shift] using hf.shift
    have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hr.shift
    simpa [M,T,f',Syn.shift,GaussianPolynomialDeterminantTerms.cell] using
      (RationalRowSpanGaussianEmbedding.matrix_lookup (tailRows (Syn.shift f) (Syn.shift m) (Syn.shift c)) (Syn.shift m)
        (succ (Syn.shift c)) (Syn.shift r) (var 0) rs.wk Prf.hyp0).eqTrans
          (coefficient_embedding (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift r) (var 0) fs.wk rs.wk Prf.hyp0)
  have layout : Γ ⊢[PRAAx] entry M r ≐ sequence R (succ c) x :=
    GaussianRationalFiberVandermonde.table_row B m (succ c) (tailRows f m c) r hr
  refine .orE (row_cases m r hr) ?_ ?_
  · exact sequence_layout_equal (entry M r) (entry T r) (succ c) (succ c) x zero R GaussianRationalPolynomialBuffers.zerosBody
      layout.wk (GaussianSuperellipticTail.upper_row _ _ _ _ Prf.hyp0) (.eqRefl _) same.wk
  · have dest : (r ≐ pred m) :: Γ ⊢[PRAAx] entry T r ≐ GaussianRationalGridCoefficientEquality.negativePolynomial f' :=
      (entry_congr (.eqRefl T) Prf.hyp0).eqTrans (GaussianSuperellipticTail.last_row f' m c)
    exact sequence_layout_equal (entry M r) (entry T r) (succ c) (length f') x
      (pairT GaussianRationalMatrixFiniteSums.minusOne f') R GaussianRationalCoefficientScaling.scaleBody
      layout.wk dest (coefficients_length _ _).eqSymm same.wk

theorem table_embedding (f m c : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c) :
    Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c) ≐
      GaussianSuperellipticTail.tailRows (coefficients f (succ c)) m c := by
  let M := RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c)
  let f' := coefficients f (succ c)
  let T := GaussianSuperellipticTail.tailRows f' m c
  let Z := GaussianSuperellipticTail.zeroRows m c
  let V := singleton (GaussianRationalGridCoefficientEquality.negativePolynomial f')
  have same : Γ ⊢[PRAAx] entriesEqual M T m := by
    refine .allI (.impI ?_)
    have h' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by
      simpa [Fm.shift,Syn.shift] using hf.shift
    simpa [M,T,f',Syn.shift] using mapped_row_equal (Syn.shift f) (Syn.shift m) (Syn.shift c) (var 0) h'.wk Prf.hyp0
  have width : Γ ⊢[PRAAx] m ≐ length Z+length V :=
    (GaussianSuperellipticTail.tail_rows_length f' m c hm).eqSymm.eqTrans (append_length Z V)
  exact sequence_layout_equal M T m (length Z+length V) (pairT (succ c) (tailRows f m c)) (pairT Z V)
    (GaussianRationalFiberVandermonde.tableBody RationalRowSpanGaussianEmbedding.matrixBody) appendBody
    (.eqRefl _) (.eqRefl _) width same

def tailF : PR 3 := PTm.toPR (tailRows (var 0) (var 1) (var 2))
theorem program_at (f m c : PTm n) : Γ ⊢[PRAAx] ap3 tailF f m c ≐ tailRows f m c := by
  simpa [tailF,ap3] using toPR_eq (Γ := Γ) (tailRows (var 0) (var 1) (var 2) : PTm 3) ![f,m,c]

theorem returned_table_embedding (f m c : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c) :
    Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.matrix (ap3 tailF f m c) m (succ c) ≐
      GaussianSuperellipticTail.tailRows (coefficients f (succ c)) m c := by
  have moved : Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.matrix (ap3 tailF f m c) m (succ c) ≐
      RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c) := by
    ipra_congr (RationalRowSpanGaussianEmbedding.matrix (var 0) (var 1) (var 2) : PTm 3) with
      [program_at f m c, .eqRefl m, .eqRefl (succ c)]
  exact moved.eqTrans (table_embedding f m c hm hf)

theorem actual_rational_superelliptic_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ length (var 0) ≐ succ (var 2) ⟶
      RationalRowSpanGaussianEmbedding.matrix (ap3 tailF (var 0) (var 1) (var 2)) (var 1) (succ (var 2)) ≐
        GaussianSuperellipticTail.tailRows (coefficients (var 0) (succ (var 2))) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (returned_table_embedding _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalSuperellipticTail

module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalSegmentCompose
public import M6PA.Model.PAInternalTracePrepend
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Left-word phase: the current head is the low bit of the left word. -/
def phaseFormula : ArithmeticSemisentence 10 :=
  “n qs ls rs q l r q' l' r'. ∃ u v u' v',
    !divDef u l 2 ∧ !remDef v l 2 ∧ !divDef u' l' 2 ∧ !remDef v' l' 2 ∧
    !segmentFormula n qs ls rs q u ((1+1)*r+v) q' u' ((1+1)*r'+v')”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def Phase (n qs ls rs q l r q' l' r' : V) : Prop :=
  Segment n qs ls rs q (l/2) ((1+1)*r+l%2) q' (l'/2) ((1+1)*r'+l'%2)

lemma phase_correct (b : Fin 10 → V) :
    (V ⊧/b phaseFormula) ↔
      Phase (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) := by
  simp [phaseFormula,Phase,div_defined.df,rem_defined.df,segment_correct]

lemma phase_zero (q l r : V) : ∃ qs ls rs, Phase 0 qs ls rs q l r q l r :=
  ⟨_,_,_,segment_zero q (l/2) ((1+1)*r+l%2)⟩

lemma phase_compose {n m qs ls rs q l r q' l' r' qys lys rys qe le re : V}
    (h : Phase n qs ls rs q l r q' l' r')
    (h' : Phase m qys lys rys q' l' r' qe le re) :
    ∃ qzs lzs rzs, Phase (n+m) qzs lzs rzs q l r qe le re :=
  segment_compose h h'
end M6.Arithmetic.PA.InternalTrace


import DiophantineConsistency.PRAHistoryResultGraph
/-! A conditional parameterized trace-to-graph bridge.

The trace hypothesis quantifies over all elements of the candidate-PRA model,
including nonstandard stages and parameters.  This file does not construct
those traces and therefore does not yet establish definability of `closeCode`.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ParamRecursionGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryIterator
  PRAHistoryTrace PRAHistoryResultGraph
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- A complete coded trace identifies the candidate recursion with the
canonical arithmetic recursion at an arbitrary model-valued stage. -/
theorem model_eq_of_trace [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {k : ℕ} (B : PR.Blueprint k) (c : PR.Construction M B)
    (base : Code k) (step : Code (k+2)) (v : Fin k → M) (n s : M)
    (hseq : Seq s) (hlen : lh s = n+1)
    (hmem : ∀ i < n+1, pair i (F (.prec base step) (Fin.cases i v)) ∈ s)
    (hz : c.zero v = F base v)
    (hs : ∀ i z, c.succ v i z = F step (Fin.cases i (Fin.cases z v))) :
    F (.prec base step) (Fin.cases n v) = c.result v n := by
  have hcseq : c.CSeq v s := by
    refine ⟨hseq, ?_, ?_⟩
    · rw [hz]
      have h := hmem 0 (by simp)
      rw [show F (.prec base step) (Fin.cases (0 : M) v) = F base v from modelBase base step v] at h
      exact h
    · intro i hi z hm
      have hi' : i < n+1 := by
        rw [hlen] at hi
        exact lt_of_lt_of_le hi tsub_le_self
      have hn : i+1 < n+1 := by
        rw [hlen] at hi
        simpa [lt_tsub_iff_right] using hi
      have heq : z = F (.prec base step) (Fin.cases i v) := hseq.isMapping.uniq hm (hmem i hi')
      rw [hs, heq]
      have hnxt := hmem (i+1) hn
      have hstep := modelStep base step (Fin.cases i v)
      change F (.prec base step) (Fin.cases (F Code.succ (fun _ => i)) v) =
        F step (Fin.cases i (Fin.cases (F (.prec base step) (Fin.cases i v)) v)) at hstep
      rw [← modelAddOne] at hstep
      rw [← hstep]
      exact hnxt
  apply (c.result_graph v _ n).mpr
  exact ⟨s,hcseq,hmem n (by simp)⟩
/-- Uniform trace existence yields the parameterized arithmetic graph. -/
theorem model_defined_of_traces [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {k : ℕ} (B : PR.Blueprint k) (c : PR.Construction M B)
    (base : Code k) (step : Code (k+2))
    (hz : ∀ v, c.zero v = F base v)
    (hs : ∀ v i z, c.succ v i z = F step (Fin.cases i (Fin.cases z v)))
    (htrace : ∀ (v : Fin k → M) (n : M), ∃ s, Seq s ∧ lh s = n+1 ∧
      ∀ i < n+1, pair i (F (.prec base step) (Fin.cases i v)) ∈ s) :
    𝚺₁.DefinedFunction (fun e : Fin (k+1) → M => F (.prec base step) e) B.resultDef := by
  apply HierarchySymbol.Defined.mk
  intro e
  have hc := c.result_defined_iff e
  have hv : Fin.cases (e 1) (fun i : Fin k => e i.succ.succ) =
      (fun i : Fin (k+1) => e i.succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  obtain ⟨s,hseq,hlen,hmem⟩ := htrace (fun i => e i.succ.succ) (e 1)
  have he := model_eq_of_trace B c base step (fun i => e i.succ.succ) (e 1) s
    hseq hlen hmem (hz _) (hs _)
  rw [hv] at he
  change B.resultDef.val.Evalb e ↔ e 0 = F (.prec base step) (fun i => e i.succ)
  rw [he]
  exact hc

#print axioms model_defined_of_traces
#print axioms model_eq_of_trace
end models
end PA194ParamRecursionGraph

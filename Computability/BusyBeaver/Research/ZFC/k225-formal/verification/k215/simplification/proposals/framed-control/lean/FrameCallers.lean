import FrameCallerBatch000
import FrameCallerBatch001
import FrameCallerBatch002
import FrameCallerBatch003
import FrameCallerBatch004
import FrameCallerBatch005
import FrameCallerBatch006
import FrameCallerBatch007
import FrameCallerBatch008
import FrameCallerBatch009
import FrameCallerBatch010
import FrameCallerBatch011
import FrameCallerBatch012
import FrameCallerBatch013
import FrameCallerBatch014
import FrameCallerBatch015
import FrameCallerBatch016
import FrameCallerBatch017
import FrameCallerBatch018
import FrameCallerBatch019
import FrameCallerBatch020
import FrameCallerBatch021
import FrameCallerBatch022

namespace SetTheory.BusyBeaver.ZFC.KFrameCallers
open KZip KRuntimeCore KLeftFrame KFramedTemplates KFrameContracts KTableCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def callers : List Caller :=
  callerBatch000 ++
  callerBatch001 ++
  callerBatch002 ++
  callerBatch003 ++
  callerBatch004 ++
  callerBatch005 ++
  callerBatch006 ++
  callerBatch007 ++
  callerBatch008 ++
  callerBatch009 ++
  callerBatch010 ++
  callerBatch011 ++
  callerBatch012 ++
  callerBatch013 ++
  callerBatch014 ++
  callerBatch015 ++
  callerBatch016 ++
  callerBatch017 ++
  callerBatch018 ++
  callerBatch019 ++
  callerBatch020 ++
  callerBatch021 ++
  callerBatch022

theorem caller_count : callers.length = 1423 := by decide +kernel
theorem callers_checked : callers.all checkCaller = true := by
  simp only [callers, List.all_append,
    callerBatch000_checked,
    callerBatch001_checked,
    callerBatch002_checked,
    callerBatch003_checked,
    callerBatch004_checked,
    callerBatch005_checked,
    callerBatch006_checked,
    callerBatch007_checked,
    callerBatch008_checked,
    callerBatch009_checked,
    callerBatch010_checked,
    callerBatch011_checked,
    callerBatch012_checked,
    callerBatch013_checked,
    callerBatch014_checked,
    callerBatch015_checked,
    callerBatch016_checked,
    callerBatch017_checked,
    callerBatch018_checked,
    callerBatch019_checked,
    callerBatch020_checked,
    callerBatch021_checked,
    callerBatch022_checked, Bool.true_and]

theorem caller_ok {c : Caller} (hc : c ∈ callers) :
    CallerOK (metaAt c.templateIndex) (templateAt c.templateIndex) c := by
  have h := (List.all_eq_true.mp callers_checked) c hc
  exact of_decide_eq_true ((Bool.and_eq_true_iff.mp h).2)

theorem index_valid {c : Caller} (hc : c ∈ callers) : c.templateIndex < metas.length := by
  have h := (List.all_eq_true.mp callers_checked) c hc
  exact of_decide_eq_true ((Bool.and_eq_true_iff.mp h).1)

theorem shape_of_index {i : Nat} (hi : i < metas.length) :
    Shape (metaAt i) (templateAt i) := by
  have h := (Bool.and_eq_true_iff.mp shapes_checked).2
  exact of_decide_eq_true ((List.all_eq_true.mp h) i (List.mem_range.mpr hi))

theorem template_member {i : Nat} (hi : i < metas.length) : templateAt i ∈ templates := by
  have he : metas.length = templates.length :=
    of_decide_eq_true ((Bool.and_eq_true_iff.mp shapes_checked).1)
  have hit : i < templates.length := by omega
  simp only [templateAt, List.getElem?_eq_getElem hit, Option.getD_some]
  exact List.getElem_mem hit

/-- A checked caller provides a positive whole-tape run of the exact machine
    and the exact source continuation, for every gap and valid register file. -/
theorem all_caller_contracts {c : Caller} (hc : c ∈ callers)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    let m := metaAt c.templateIndex
    sourceResult m c.word = c.prefix ++ m.result ∧
    Reach1 tm215
      (conc n vs (addLeft (c.prefix.reverse.map Seg.bit ++ [.bit true]) (localStart m)))
      (zc 84 [true] (c.prefix ++ m.result ++
        List.replicate (n + (16 + m.suffix.length - m.result.length)) false ++
          true :: sepsR vs)) := by
  exact caller_contract (template_member (index_valid hc))
    (shape_of_index (index_valid hc)) (caller_ok hc) n hv

/-- Exact standard primitive entries and the production gap formula. -/
theorem all_caller_standard {c : Caller} (hc : c ∈ callers)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    let m := metaAt c.templateIndex
    sourceResult m c.word = c.prefix ++ m.result ∧
    Reach1 tm215
      (leafPort m.q c.word (n + (64 - c.word.length)) vs)
      (zc 84 [true] (sourceResult m c.word ++
        List.replicate (n + (64 - (sourceResult m c.word).length)) false ++
          true :: sepsR vs)) := by
  exact caller_contract_standard (template_member (index_valid hc))
    (shape_of_index (index_valid hc)) (caller_ok hc) n hv

/-- Source action and full internal role route were checked on the same word. -/
theorem caller_bindings {c : Caller} (hc : c ∈ callers) :
    let m := metaAt c.templateIndex
    RegisterPath.walk KSource215.p215 (KSource215.p215.nnodes + 1)
      KSource215.p215.root c.word 0 = some (action m, c.word.length) ∧
    portState K215Decoder.roles 0 c.word.dropLast = some m.q :=
  ⟨(caller_ok hc).2.2.1, (caller_ok hc).2.2.2.1⟩

#print axioms shapes_checked
#print axioms callers_checked
#print axioms all_caller_contracts
#print axioms all_caller_standard
#print axioms caller_bindings
end SetTheory.BusyBeaver.ZFC.KFrameCallers

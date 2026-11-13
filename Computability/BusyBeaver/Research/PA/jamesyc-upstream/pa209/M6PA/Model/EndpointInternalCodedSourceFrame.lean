module
public import M6PA.Model.PATheory
public import M6PA.Model.InternalCodedSourceTraceInvariant
public import M6PA.Model.OriginalModelCoverage
public import M6PA.Model.EndpointInternalSymbolicGraphs
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.Arithmetic.PA
open M6.Arithmetic.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Symbolic PhysicalRegisters
attribute [local irreducible] Source.exactSites

def registerGraph : List (Fin 9) → 𝚺ᴬ₁.Semisentence 2
  | [] => .mkSigma “rs xs. ⊤”
  | r::rs => .mkSigma “v xs. ∃ a, !nthDef a v ↑r.val ∧
      !nthDef a xs ↑(Source.physicalRegister r) ∧ !(registerGraph rs) v xs”

def framesGraph : List (Source.Site × Nat) → 𝚺ᴬ₁.Semisentence 6
  | [] => .mkSigma “pc q l r n xs. ⊥”
  | entry::rest => .mkSigma “pc q l r n xs.
      (pc=↑(entry.2+1) ∧ !(FileBoxes.configGraph (OriginalCheck.frame (M6.Arithmetic.OriginalCheck.path entry.2))) q l r n xs) ∨
      !(framesGraph rest) pc q l r n xs”

def frameEntries : List (Source.Site × Nat) := Source.exactSites.toList.zipIdx

def frameGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “c n xs q l r. ∃ pc regs size, !fstIdxDef pc c ∧ !sndIdxDef regs c ∧
    !lenDef 9 regs ∧ !lenDef size xs ∧ 10≤size ∧
    !(registerGraph (List.finRange 9)) regs xs ∧ !(framesGraph frameEntries) pc q l r n xs”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def Frames (entries : List (Source.Site × Nat)) (pc n xs : V) (m : ModelConf V) : Prop :=
  ∃ entry∈entries, pc=((entry.2+1 : Nat) : V) ∧ m=PhysicalFrame.frame (M6.Arithmetic.OriginalCheck.path entry.2) n xs

def Refines (c n xs : V) (m : ModelConf V) : Prop :=
  ValidStore (store c) ∧ (10 : V)≤len xs ∧ registers (store c)=readFile xs ∧
    Frames frameEntries (M6.Arithmetic.PA.InternalTrace.CodedSource.control c) n xs m

lemma register_correct (rs : List (Fin 9)) (v : Fin 2 → V) :
    (V ⊧/v (registerGraph rs).val) ↔ ∀ r∈rs,registers (v 0) r=readFile (v 1) r := by
  induction rs generalizing v with
  | nil => simp [registerGraph]
  | cons r rs ih =>
    simp [registerGraph,nth_defined.df,ih,registers,readFile,numeral_eq_natCast]

private lemma config_vector (s : M6.Runtime.SConf) (v : Fin 5 → V) :
    (V ⊧/v (FileBoxes.configGraph s).val) ↔
      v 0=(config (v 3) (FileBoxes.box (v 4)) denseControl s).q ∧
      v 1=(config (v 3) (FileBoxes.box (v 4)) denseControl s).left ∧
      v 2=(config (v 3) (FileBoxes.box (v 4)) denseControl s).right := by
  have hv : v=![v 0,v 1,v 2,v 3,v 4] := by simp [funext_iff,Fin.forall_fin_succ]
  rw [hv]
  exact FileBoxes.config_correct s _ _ _ _ _

private lemma conf_eq (q l r : V) (m : ModelConf V) :
    (⟨q,l,r⟩ : ModelConf V)=m ↔ q=m.q ∧ l=m.left ∧ r=m.right := by
  cases m; simp only [ModelConf.mk.injEq]

lemma frames_correct (entries : List (Source.Site × Nat)) (v : Fin 6 → V) :
    (V ⊧/v (framesGraph entries).val) ↔
      Frames entries (v 0) (v 4) (v 5) ⟨v 1,v 2,v 3⟩ := by
  induction entries generalizing v with
  | nil => simp [framesGraph,Frames]
  | cons entry rest ih =>
    simp [framesGraph,config_vector,ih,Frames,PhysicalFrame.frame,
      conf_eq,numeral_eq_natCast,exists_or,or_and_right]

lemma frame_correct (v : Fin 6 → V) : (V ⊧/v frameGraph.val) ↔
    Refines (v 0) (v 1) (v 2) ⟨v 3,v 4,v 5⟩ := by
  simp [frameGraph,fstIdx_defined.df,sndIdx_defined.df,len_defined.df,register_correct,
    frames_correct,Refines,ValidStore,M6.Arithmetic.PA.InternalTrace.CodedSource.control,store,funext_iff,numeral_eq_natCast,Nat.cast_ofNat,eq_comm]

lemma frame_entry {i : Nat} {s : Source.Site} (hs : Source.exactSites[i]?=some s) :
    (s,i)∈frameEntries := by
  exact List.mem_zipIdx_iff_getElem?.mpr (by simpa only [Array.getElem?_toList] using hs)

lemma frames_at (i : Nat) (s : Source.Site) (hs : Source.exactSites[i]?=some s) (n xs : V) :
    Frames frameEntries ((i+1 : Nat) : V) n xs (PhysicalFrame.frame (M6.Arithmetic.OriginalCheck.path i) n xs) :=
  ⟨(s,i),frame_entry hs,rfl,rfl⟩

lemma frames_cases {pc n xs : V} {m : ModelConf V}
    (h : Frames frameEntries pc n xs m) :
    ∃ i s, Source.exactSites[i]?=some s ∧ pc=((i+1 : Nat) : V) ∧
      m=PhysicalFrame.frame (M6.Arithmetic.OriginalCheck.path i) n xs := by
  obtain ⟨⟨s,i⟩,hm,hpc,hframe⟩ := h
  exact ⟨i,s,by simpa only [Array.getElem?_toList] using List.mem_zipIdx_iff_getElem?.mp hm,hpc,hframe⟩
end Models
#print axioms frame_correct
#print axioms frames_at
#print axioms frames_cases
end M6.Arithmetic.PA.InternalTrace.CodedSource


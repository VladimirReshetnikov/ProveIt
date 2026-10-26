import ObservedClosure
import DiophantineConsistency.ObjectCodeBound

/-! Actual clients of the abstract certificate-closure interface.
The model set S remains of type V, never a Lean List or Finset. -/
namespace ClosureClients
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open DiophantineConsistency.ObjectCodeBound
universe u
variable {V : Type u} {mem : V → V → Prop}

private noncomputable def boundRules (H : ZFAxioms mem) : ObservedClosure.Rules mem (V × V) where
  encode p := kpair H p.1 p.2
  step S p := mem p.2 (omegaV H) ∧ BoundStep H S p.1 p.2
  mono hsub _ hp := ⟨hp.1, boundStep_mono H hsub hp.2⟩

theorem boundClosed_cup_via_kernel (H : ZFAxioms mem) {S T : V}
    (hS : BoundClosed H S) (hT : BoundClosed H T) : BoundClosed H (vcup H S T) :=
  fun c b => (boundRules H).cup H (fun p => hS p.1 p.2) (fun p => hT p.1 p.2) (c,b)

theorem boundClosed_insert_via_kernel (H : ZFAxioms mem) {S c b : V}
    (hS : BoundClosed H S) (hb : mem b (omegaV H)) (hs : BoundStep H S c b) :
    BoundClosed H (vcup H S (vsingle H (kpair H c b))) := by
  have hinj : Function.Injective (boundRules H).encode := by
    intro p q h
    exact Prod.ext (kpair_inj H _ _ _ _ h).1 (kpair_inj H _ _ _ _ h).2
  exact fun d e => (boundRules H).insert H hinj (i := (c,b))
    (fun p => hS p.1 p.2) ⟨hb,hs⟩ (d,e)

/-- Two further adapters in imported foundational modules use triple records. -/
private noncomputable def renameRules (H : ZFAxioms mem) :
    ObservedClosure.Rules mem (V × V × V) where
  encode p := satTriple H p.1 p.2.1 p.2.2
  step S p := IsVarMap H p.1 ∧ RenStep H S p.1 p.2.1 p.2.2
  mono hsub _ hp := ⟨hp.1, renStep_mono H hsub hp.2⟩

private noncomputable def rankRules (H : ZFAxioms mem) :
    ObservedClosure.Rules mem (V × V × V) where
  encode p := satTriple H p.1 p.2.1 p.2.2
  step S p := mem p.2.1 (omegaV H) ∧ mem p.2.2 (omegaV H) ∧
    RankStep H S p.1 p.2.1 p.2.2
  mono hsub _ hp := ⟨hp.1, hp.2.1, rankStep_mono H hsub hp.2.2⟩

private theorem triple_injective (H : ZFAxioms mem) :
    Function.Injective (fun p : V × V × V => satTriple H p.1 p.2.1 p.2.2) := by
  intro p q h
  obtain ⟨h1,h2,h3⟩ := satTriple_inj H h
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem renClosed_cup_via_kernel (H : ZFAxioms mem) {S T : V}
    (hS : RenClosed H S) (hT : RenClosed H T) : RenClosed H (vcup H S T) :=
  fun r c c' => (renameRules H).cup H
    (fun p => hS p.1 p.2.1 p.2.2) (fun p => hT p.1 p.2.1 p.2.2) (r,c,c')

theorem renClosed_insert_via_kernel (H : ZFAxioms mem) {S r c c' : V}
    (hS : RenClosed H S) (hr : IsVarMap H r) (hs : RenStep H S r c c') :
    RenClosed H (vcup H S (vsingle H (satTriple H r c c'))) :=
  fun r' d d' => (renameRules H).insert H (triple_injective H) (i := (r,c,c'))
    (fun p => hS p.1 p.2.1 p.2.2) ⟨hr,hs⟩ (r',d,d')

theorem rankClosed_cup_via_kernel (H : ZFAxioms mem) {S T : V}
    (hS : RankClosed H S) (hT : RankClosed H T) : RankClosed H (vcup H S T) :=
  fun c s p => (rankRules H).cup H
    (fun q => hS q.1 q.2.1 q.2.2) (fun q => hT q.1 q.2.1 q.2.2) (c,s,p)

theorem rankClosed_insert_via_kernel (H : ZFAxioms mem) {S c s p : V}
    (hS : RankClosed H S) (hs : mem s (omegaV H)) (hp : mem p (omegaV H))
    (hstep : RankStep H S c s p) :
    RankClosed H (vcup H S (vsingle H (satTriple H c s p))) :=
  fun d u v => (rankRules H).insert H (triple_injective H) (i := (c,s,p))
    (fun q => hS q.1 q.2.1 q.2.2) ⟨hs,hp,hstep⟩ (d,u,v)

#print axioms ObservedClosure.Rules.cup
#print axioms ObservedClosure.Rules.insert
#print axioms boundClosed_cup_via_kernel
#print axioms boundClosed_insert_via_kernel
end ClosureClients

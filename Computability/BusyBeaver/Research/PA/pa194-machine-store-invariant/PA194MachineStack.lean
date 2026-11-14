import PA194MachineProjections
import PA194TargetLineSoundness
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194MachineStack
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194MachineProjections PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A finite Foundation-vector trace follows the exact machine-Cantor stack
from its root to zero, and every visited head satisfies `G`. -/
def SoundStack (G : M → Prop) (w : M) : Prop :=
  ∃ n trace, trace.[0] = w ∧ trace.[n] = 0 ∧
    ∀ i < n, G (first trace.[i]) ∧ second trace.[i] = trace.[i+1]

theorem first_zero : first (0 : M) = 0 := by
  have h := first_cantor (0 : M) 0
  simpa [cantor,triangle] using h
theorem second_zero : second (0 : M) = 0 := by
  have h := second_cantor (0 : M) 0
  simpa [cantor,triangle] using h

theorem zero_sound (G : M → Prop) : SoundStack G 0 := by
  refine ⟨0,0,?_,?_,?_⟩
  · simp
  · simp
  · intro i hi
    exact False.elim (not_lt_zero hi)

theorem push_sound (G : M → Prop) (a w : M) (ha : G a) (hw : SoundStack G w) :
    SoundStack G (cantor a w) := by
  obtain ⟨n,v,hv0,hvn,hall⟩ := hw
  refine ⟨n+1,cantor a w ∷ v,?_,?_,?_⟩
  · simp
  · simpa [nth_succ] using hvn
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
    · simp [ha,hv0]
    · have hj : j < n := (add_lt_add_iff_right 1).mp hi
      have h := hall j hj
      simpa only [nth_succ,sndIdx_adjoin] using h

theorem pop_sound (G : M → Prop) (hzero : G 0) (w : M) (hw : SoundStack G w) :
    G (first w) ∧ SoundStack G (second w) := by
  obtain ⟨n,v,hv0,hvn,hall⟩ := hw
  rcases zero_or_succ n with (rfl | ⟨n,rfl⟩)
  · have hwzero : w = 0 := hv0.symm.trans hvn
    rw [hwzero,first_zero,second_zero]
    exact ⟨hzero,zero_sound G⟩
  · have hpos : (0 : M) < n+1 := by simp
    have hfirst := hall 0 hpos
    have hwfirst : G (first w) := by simpa [hv0] using hfirst.1
    refine ⟨hwfirst,n,sndIdx v,?_,?_,?_⟩
    · rw [← nth_succ]
      simpa only [zero_add,hv0] using hfirst.2.symm
    · simpa [nth_succ] using hvn
    · intro i hi
      have hi' : i+1 < n+1 := (add_lt_add_iff_right 1).mpr hi
      have h := hall (i+1) hi'
      simpa only [nth_succ] using h

theorem soundStack_def_generic (G : M → Prop) (f g : M → M)
    (hG : 𝚺₁-Predicate G) (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun w => ∃ n trace, trace.[0] = w ∧ trace.[n] = 0 ∧
      ∀ i < n, G (f trace.[i]) ∧ g trace.[i] = trace.[i+1]) := by
  haveI := hG
  haveI := hf
  haveI := hg
  definability

theorem soundStack_def (G : M → Prop) (hG : 𝚺₁-Predicate G) :
    𝚺₁-Predicate (SoundStack G) := by
  have hcode (c : Code 1) : 𝚺₁-Function₁ (fun p : M => F c ![p]) := by
    have h : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F c e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) c)
    convert h using 1
    funext e
    change F c ![e 0] = F c e
    apply congrArg (fun e : Fin 1 → M => F c e)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hf : 𝚺₁-Function₁ (first : M → M) := by
    have h := hcode fixedFirst
    convert h using 1
    funext p
    exact (fixedFirst_model p).symm
  have hs : 𝚺₁-Function₁ (second : M → M) := by
    have h := hcode fixedSecond
    convert h using 1
    funext p
    exact (fixedSecond_model p).symm
  exact soundStack_def_generic G first second hG hf hs

theorem zero_provable : TargetProvable (0 : M) := by
  have h := rho8_provable (0 : M) 0 0 0 (le_refl 0)
  simpa [rho8Value,impValue,cantor,triangle] using h

def TargetStack (w : M) : Prop := SoundStack TargetProvable w

theorem targetStack_def : 𝚺₁-Predicate (TargetStack (M := M)) :=
  soundStack_def TargetProvable targetProvable_definable

theorem targetStack_zero : TargetStack (0 : M) := zero_sound TargetProvable

theorem targetStack_push (a w : M) (ha : TargetProvable a) (hw : TargetStack w) :
    TargetStack (F fixedCantor ![a,w]) := by
  rw [modelCantorSelected fixedCantor fixedCantor_certified]
  exact push_sound TargetProvable a w ha hw

theorem targetStack_pop (w : M) (hw : TargetStack w) :
    TargetProvable (F fixedFirst ![w]) ∧ TargetStack (F fixedSecond ![w]) := by
  rw [fixedFirst_model,fixedSecond_model]
  exact pop_sound TargetProvable zero_provable w hw

/-- The model-level invariant for the scheduler's top, work stack and cache. -/
def SoundStore (t w h : M) : Prop := TargetProvable t ∧ TargetProvable h ∧ TargetStack w

theorem soundStore_zero : SoundStore (0 : M) 0 0 := ⟨zero_provable,zero_provable,targetStack_zero⟩

theorem shift_preserves (t w h : M) (hs : SoundStore t w h) :
    SoundStore h (F fixedSecond ![w]) (F fixedFirst ![w]) := by
  obtain ⟨ht,hh,hw⟩ := hs
  have hp := targetStack_pop w hw
  exact ⟨hh,hp.1,hp.2⟩

theorem mp_success_preserves (t w h a : M) (hs : SoundStore t w h)
    (he : h = impValue t a) : SoundStore a (F fixedCantor ![0,w]) 0 := by
  obtain ⟨ht,hh,hw⟩ := hs
  rw [he] at hh
  exact ⟨PA194TargetVectorJoin.mp_closed t a ht hh,zero_provable,targetStack_push 0 w zero_provable hw⟩

theorem mp_failure_preserves (t w h : M) (hs : SoundStore t w h) : SoundStore 0 w 0 :=
  ⟨zero_provable,zero_provable,hs.2.2⟩

/-- The AX source command's pushed list, in source order. -/
noncomputable def axStack (D H A d h t w : M) : M :=
  cantor (diagonalValue A)
    (cantor (head6Value D A H)
      (cantor (head5Value D H)
        (cantor (head4Value D A H)
          (cantor (head3Value D A H)
            (cantor (head2Value D A H)
              (cantor (head1Value D H)
                (cantor (rho8Value D A H d)
                  (cantor (allValue d h) (cantor t w)))))))))

noncomputable def axTop (H D A : M) : M :=
  if D = A ∨ H = A then 0 else oldBundleValue H D A

theorem ax_preserves (t w h d x y A : M) (hs : SoundStore t w h) :
    SoundStore (axTop (h+y) (d+x) A)
      (axStack (d+x) (h+y) A d h t w) 0 := by
  obtain ⟨ht,hh,hw⟩ := hs
  have hgate : TargetProvable (axTop (h+y) (d+x) A) := by
    unfold axTop
    split
    · exact zero_provable
    · rename_i hguard
      exact gate_provable (h+y) (d+x) A (fun ha => hguard (Or.inr ha.symm))
        (fun hb => hguard (Or.inl hb.symm))
  have s0 := push_sound TargetProvable t w ht hw
  have s1 := push_sound TargetProvable (allValue d h) _ (PA194TargetGeneralize.generalize_closed d h hh) s0
  have s2 := push_sound TargetProvable (rho8Value (d+x) A (h+y) d) _
    (rho8_provable (d+x) A (h+y) d le_self_add) s1
  have hh1 : TargetProvable (head1Value (d+x) (h+y)) := by
    rw [← machineHead1_model]
    exact head1_provable _ _
  have s3 := push_sound TargetProvable (head1Value (d+x) (h+y)) _ hh1 s2
  have s4 := push_sound TargetProvable (head2Value (d+x) A (h+y)) _ (head2_provable _ _ _) s3
  have s5 := push_sound TargetProvable (head3Value (d+x) A (h+y)) _ (head3_provable _ _ _) s4
  have s6 := push_sound TargetProvable (head4Value (d+x) A (h+y)) _ (head4_provable _ _ _) s5
  have s7 := push_sound TargetProvable (head5Value (d+x) (h+y)) _ (head5_provable _ _) s6
  have s8 := push_sound TargetProvable (head6Value (d+x) A (h+y)) _ (head6_provable _ _ _) s7
  have s9 := push_sound TargetProvable (diagonalValue A) _ (diagonal_provable _) s8
  exact ⟨hgate,zero_provable,s9⟩

#print axioms ax_preserves
#print axioms shift_preserves
#print axioms mp_success_preserves
#print axioms mp_failure_preserves
#print axioms zero_provable
#print axioms targetStack_def
#print axioms targetStack_push
#print axioms targetStack_pop
#print axioms push_sound
#print axioms pop_sound
end models
end PA194MachineStack

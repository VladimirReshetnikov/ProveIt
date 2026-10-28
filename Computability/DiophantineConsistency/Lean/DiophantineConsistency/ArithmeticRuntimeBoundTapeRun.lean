import DiophantineConsistency.ArithmeticRuntimeBoundTapeControl
import DiophantineConsistency.ArithmeticRuntime215

/-! # p215 control halt ⇒ blank decimal215 halt, with a quadratic clock

`ArithmeticRuntime215.control_blank_halts_iff` transfers halting between the
p215 control run from the seed file and the literal blank decimal215 machine,
without clocks. Here the forward direction is bounded. After `n` control steps
from the seed (registers `![0,0,0,0,0,0,4,0,0]`, 40 spares, gap 1) the canonical
entry has at most `40+n` spares, gap at most `1+2n` and every register at most
`4+n` (`RelN n`), so the next instruction costs at most
`4000*(26*n+4441)` machine steps (`ArithmeticRuntimeBoundTapeControl.siteB`).
With the fixed 95714-step boot prefix:

  `run215 ta (liveValue 1 seedFile) = 0 →
     ∃ t ≤ 95714 + ta*(4000*(26*ta+4441)), first (ArithmeticMachineRun215.run t) = 0`.

No existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBoundTapeRun
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticControlFrame215
open ArithmeticRuntimeBoundTapeBoxes ArithmeticRuntimeBoundTapeControl

/-- Every listed register of the file is at most `m`. -/
def regBoundDef : List (Fin 9) → 𝚺₁.Semisentence 2
  | [] => .mkSigma “f m. 0=0”
  | p::ps => .mkSigma “f m. ∃ v, !(projectionDef 8 p) v f ∧ v≤m ∧ !(regBoundDef ps) f m”

/-- The canonical entry relation after `n` control steps from the seed. -/
def relNDef : 𝚺₁.Semisentence 3 := .mkSigma
  “n l b. ∃ q, ∃ f, ∃ k, ∃ gap, 0<k ∧
    (∃ op, !(opcodeDef table215) op q ∧ op≠0) ∧
    !liveDef l q f ∧ !entryDef b q f k gap ∧ k≤40+n ∧ gap≤1+2*n ∧
    !(regBoundDef (List.finRange 9)) f (4+n)”

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance first_sigma1 : 𝚺₁-Function₁[V] first := first_defined.to_definable.of_zero

def RegBound (ps : List (Fin 9)) (f m : V) : Prop := ∀ p ∈ ps, regValue f p ≤ m

instance regBound_defined (ps : List (Fin 9)) :
    𝚺₁-Relation[V] (RegBound ps) via regBoundDef ps := by
  induction ps with
  | nil => exact .mk fun e => by simp [regBoundDef,RegBound]
  | cons p ps ih =>
    exact .mk fun e => by
      simp [regBoundDef,RegBound,regValue,(projection_defined 8 p).iff,ih.iff]

def RelN (n l b : V) : Prop := ∃ q f k gap : V,
  0<k ∧ opcodeValue table215 q≠0 ∧ l=liveValue q f ∧ b=entryValue q f k gap ∧
    k≤40+n ∧ gap≤1+2*n ∧ RegBound (List.finRange 9) f (4+n)

instance relN_defined : 𝚺₁-Relation₃[V] RelN via relNDef :=
  .mk fun e => by
    simp [relNDef,RelN,(opcode_defined table215).iff,(regBound_defined (List.finRange 9)).iff,
      numeral_eq_natCast]
instance relN_definable : 𝚺₁-Relation₃[V] RelN := relN_defined.to_definable

/-- The clock bound of the control instruction executed after `n` steps. -/
noncomputable def stepBound (n : V) : V := 4000*(26*n+4441)
/-- The clock bound of the first `n` control instructions. -/
noncomputable def runBound (n : V) : V := n*stepBound n
/-- The total blank-machine clock bound for a control halt at time `ta`. -/
noncomputable def Btape (ta : V) : V := 95714 + ta*(4000*(26*ta+4441))

theorem siteB_le (n gap k f : V) (hk : k≤40+n) (hg : gap≤1+2*n)
    (hr : RegBound (List.finRange 9) f (4+n)) :
    siteB gap (regValue f) k ≤ stepBound n := by
  have hF : fileCost (List.ofFn (regValue f)) ≤ 9*((4+n)+2) :=
    fileCost_ofFn_le _ _ (fun p => hr p (List.mem_finRange p))
  unfold siteB boxW stepBound
  calc 4000*(gap + (2*fileCost (List.ofFn (regValue f)) + 6*k + 7) + 4085)
      ≤ 4000*((1+2*n) + (2*(9*((4+n)+2)) + 6*(40+n) + 7) + 4085) := by
        apply mul_le_mul_of_nonneg_left _ (Arithmetic.zero_le _)
        exact _root_.add_le_add (_root_.add_le_add hg (_root_.add_le_add (_root_.add_le_add
          (mul_le_mul_of_nonneg_left hF (Arithmetic.zero_le _))
          (mul_le_mul_of_nonneg_left hk (Arithmetic.zero_le _))) le_rfl)) le_rfl
    _ = 4000*(26*n+4441) := by ring

theorem relN_step (n l b : V) (hr : RelN n l b) (hs : stepValue table215 l≠0) :
    ∃ t, t≤stepBound n ∧ RelN (n+1) (stepValue table215 l) (runFrom t b) := by
  obtain ⟨q,f,k,gap,hk,hq,rfl,rfl,hkn,hgn,hrn⟩ := hr
  obtain ⟨i,rfl⟩ := opcode_supported q hq
  obtain ⟨j,f',k',gap',hk',hst,⟨t,_,htB,hb⟩,hk1,hg1,hf1⟩ := entry_stepB i f k gap hk hs
  refine ⟨t,le_trans htB (siteB_le n gap k f hkn hgn hrn),(number j:V),f',k',gap',hk',
    opcode_nonzero j,hst,hb,?_,?_,?_⟩
  · calc k' ≤ k+1 := hk1
      _ ≤ 40+n+1 := _root_.add_le_add hkn le_rfl
      _ = 40+(n+1) := by ring
  · calc gap' ≤ gap+2 := hg1
      _ ≤ 1+2*n+2 := _root_.add_le_add hgn le_rfl
      _ = 1+2*(n+1) := by ring
  · intro p _
    calc regValue f' p ≤ regValue f p + 1 := hf1 p
      _ ≤ 4+n+1 := _root_.add_le_add (hrn p (List.mem_finRange p)) le_rfl
      _ = 4+(n+1) := by ring

theorem relN_halt (n l b : V) (hr : RelN n l b) (hz : stepValue table215 l=0) :
    ∃ t, t≤stepBound n ∧ first (runFrom t b)=0 := by
  obtain ⟨q,f,k,gap,hk,hq,rfl,rfl,hkn,hgn,hrn⟩ := hr
  obtain ⟨i,rfl⟩ := opcode_supported q hq
  obtain ⟨t,_,htB,ht⟩ := entry_haltB i f k gap hk hz
  exact ⟨t,le_trans htB (siteB_le n gap k f hkn hgn hrn),ht⟩

theorem runBound_succ (n : V) : runBound n + stepBound n ≤ runBound (n+1) := by
  unfold runBound stepBound
  exact le_of_add_eq (c := (n+1)*(4000*26)) (by ring)

/-- The bounded clock invariant, by Σ1 induction on the control time. -/
theorem clocks (l0 b0 : V) (h0 : RelN 0 l0 b0) : ∀ n : V, ∃ tb, tb≤runBound n ∧
    (first (runFrom tb b0)=0 ∨ RelN n (run215 n l0) (runFrom tb b0)) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · unfold runBound stepBound; definability
  case zero =>
    refine ⟨0,by simp [runBound],.inr ?_⟩
    rw [run215_zero,runFrom_zero]
    exact h0
  case succ n ih =>
    obtain ⟨tb,htb,hq⟩ := ih
    have hmono : runBound n ≤ runBound (n+1) := le_trans le_self_add (runBound_succ n)
    rcases hq with hz | hr
    · exact ⟨tb,le_trans htb hmono,.inl hz⟩
    · by_cases hs : stepValue table215 (run215 n l0)=0
      · obtain ⟨t,htB,ht⟩ := relN_halt n _ _ hr hs
        refine ⟨tb+t,le_trans (_root_.add_le_add htb htB) (runBound_succ n),.inl ?_⟩
        rw [runFrom_add]
        exact ht
      · obtain ⟨t,htB,ht⟩ := relN_step n _ _ hr hs
        refine ⟨tb+t,le_trans (_root_.add_le_add htb htB) (runBound_succ n),.inr ?_⟩
        rw [runFrom_add,show run215 (n+1) l0=stepValue table215 (run215 n l0) from
          controlRun_succ table215 n l0]
        exact ht

theorem seed_relN : RelN 0 (liveValue (1:V) ArithmeticRuntime215.seedFile) (bootCode:V) := by
  refine ⟨1,ArithmeticRuntime215.seedFile,40,1,by simp,ArithmeticRuntime215.seed_supported,rfl,
    ArithmeticRuntime215.seed_entry.symm,by simp,by simp,?_⟩
  intro p hp
  clear hp
  rw [ArithmeticRuntime215.seed_registers]
  revert p
  simp [Fin.forall_fin_succ]

/-- **p215 control halt ⇒ blank decimal215 halt, below an explicit quadratic clock.**
If the p215 control run from the seed file halts at internal time `ta`, the
literal blank decimal215 machine halts by time `Btape ta`. -/
theorem blank_halts_le_of_p215_halts (ta : V)
    (h : run215 ta (liveValue 1 ArithmeticRuntime215.seedFile)=0) :
    ∃ t ≤ Btape ta, first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨tb,htb,hq⟩ := clocks _ _ seed_relN ta
  rcases hq with hz | hr
  · refine ⟨95714+tb,_root_.add_le_add le_rfl htb,?_⟩
    rw [continuation]
    exact hz
  · obtain ⟨_,f,_,_,_,_,hl,_⟩ := hr
    rw [h] at hl
    exact absurd hl.symm (live_ne_zero _ _)

end Model
end DiophantineConsistency.ArithmeticRuntimeBoundTapeRun

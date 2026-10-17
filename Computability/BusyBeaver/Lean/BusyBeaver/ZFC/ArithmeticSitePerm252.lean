import BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252
import BusyBeaver.ZFC.SitePerm252

set_option autoImplicit false

/-!
All-model arithmetic meanings of the actual finite per-instruction site checks.
The existing site constructors, physical selector map, path/carry functions,
branch guards, fuel and Boolean checks are reused without a new certificate
format or a replay of the full coverage chunks. Register values, spare count,
gap and execution clocks are arbitrary internal IΣ1-model elements; the site
path, operation and syntax are externally fixed finite data.

These are conditional local contracts: accepted site checks imply their actual
whole numeric endpoints. No all-site coverage, represented internal-PC decoder,
dispatch invariant, whole runtime simulation or PA endpoint is asserted here.
Mira-Cult, Jeff and Wade retain their machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineRunFromPerm252
open ArithmeticSymbolicBoxesPerm252 (ValidValues)
open ArithmeticSymbolicExecutionPerm252 (value)
open SymbolicPerm252 (Branch SConfig)
open RegisterPath
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual Site.start syntax, interpreted with concrete numeric boxes. -/
noncomputable def startValue (values : List V) (count gap : V) (Q : List Bool) : V :=
  value values count gap (SitePerm252.start Q)

/-- Reuse the existing accepted runTo Boolean, not its standard-Nat Core
soundness field. The arithmetic checker theorem supplies the internal clock. -/
theorem runTo_sound (br : Branch) (Q : List Bool) (wanted : SConfig)
    (he : SitePerm252.runTo br Q wanted = true)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap wanted := by
  exact ArithmeticSymbolicExecutionPerm252.verifies_sound SitePerm252.fuel br
    (SitePerm252.start Q) wanted he values hv count gap

/-- State zero is projected only after the complete actual final halt step. -/
theorem runHalt_sound (Q : List Bool) (he : SitePerm252.runHalt Q = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values count gap Q)) = 0 := by
  exact ArithmeticSymbolicExecutionPerm252.verifiesHalt_sound SitePerm252.fuel none
    (SitePerm252.start Q) he values ⟨hlen,trivial⟩ count gap

/-- The original check itself includes the external forty-cell path bound. -/
theorem accepted_length (Q : List Bool) (edge : Edge)
    (h : SitePerm252.checkSite Q edge = true) : Q.length ≤ SitePerm252.minDistance :=
  SitePerm252.checkSite_length Q edge h

theorem inc_selector_bound (Q : List Bool) (r : Nat)
    (h : SitePerm252.checkSite Q (.inc r) = true) : r < 9 :=
  SitePerm252.check_inc_bound Q r h

theorem dec_selector_bound (Q : List Bool) (r : Nat)
    (h : SitePerm252.checkSite Q (.decnz r) = true) : r < 9 :=
  SitePerm252.check_decnz_bound Q r h

/-- The physical increment effect and overflow/carry target are exactly the
ones stored in the existing site checker. -/
theorem check_inc (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SitePerm252.checkSite Q (.inc r) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap
        (SitePerm252.target (incPath Q) (SitePerm252.allOnes Q)
          (.plain (.increment (SitePerm252.physical r hr)))) :=
  runTo_sound none Q _ (SitePerm252.check_inc Q r hr h) values ⟨hlen,trivial⟩ count gap

/-- Zero is tested on the original physically selected internal primary value.
The target is unchanged, with the exact original break/overflow convention. -/
theorem check_decnz_zero (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hz : values.getD (SitePerm252.physical r hr).val 0 = 0) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap
        (SitePerm252.target (breakPath 1 Q) (SitePerm252.allOnes (stripPath false 1 Q))
          (.plain .unchanged)) :=
  runTo_sound (some (SitePerm252.physical r hr,true)) Q _
    (SitePerm252.check_decnz Q r hr h).1 values ⟨hlen,hz⟩ count gap

/-- The positive branch decrements the original physical value and appends one
zero spare inside the concrete decrement effect; no second count update occurs. -/
theorem check_decnz_positive (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hn : values.getD (SitePerm252.physical r hr).val 0 ≠ 0) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap
        (SitePerm252.target (incPath Q) (SitePerm252.allOnes Q)
          (.plain (.decrement (SitePerm252.physical r hr)))) :=
  runTo_sound (some (SitePerm252.physical r hr,false)) Q _
    (SitePerm252.check_decnz Q r hr h).2 values ⟨hlen,hn⟩ count gap

theorem check_break (Q : List Bool) (k : Nat)
    (h : SitePerm252.checkSite Q (.brk k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap
        (SitePerm252.target (breakPath k Q) (SitePerm252.allOnes (stripPath false k Q))
          (.plain .unchanged)) :=
  runTo_sound none Q _ (SitePerm252.check_break Q k h) values ⟨hlen,trivial⟩ count gap

theorem check_continue (Q : List Bool) (k : Nat)
    (h : SitePerm252.checkSite Q (.cont k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target (continuePath k Q) false (.plain .unchanged)) :=
  runTo_sound none Q _ (SitePerm252.check_continue Q k h) values ⟨hlen,trivial⟩ count gap

theorem check_halt (Q : List Bool) (h : SitePerm252.checkSite Q .halt = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values count gap Q)) = 0 :=
  runHalt_sound Q (SitePerm252.check_halt Q h) values hlen count gap

/-- Nodes are not accepted operation sites; no missing node semantics is hidden. -/
theorem node_rejected (Q : List Bool) (r : Nat) :
    SitePerm252.checkSite Q (.node r) = false := SitePerm252.check_node_false Q r

end SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252

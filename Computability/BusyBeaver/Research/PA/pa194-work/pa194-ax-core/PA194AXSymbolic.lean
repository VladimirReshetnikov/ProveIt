import PA194AXSource
import M6.Source.AXSymbolic
import PA196.Commands.Code
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194AXSymbolic
open M6.Source M6.Source.AXSymbolic PA194AXSource
open PA196.Commands.Code

def tokenOps : Token → List AXMacro.Op
 | .push => [.push]
 | .copyD => [.push, .copyD]
 | .copyH => [.push, .copyH]
 | .copyA => [.push, .copyA]
 | .cons => [.cons]
 | .incT => [.incT]
 | .readH => [.readH]
 | .readDCons => [.readD, .push, .copyD, .cons]
 | .copyGuard | .compareGuard | .close => []

def core : List AXMacro.Op := (tokens.take 187).flatMap tokenOps

def initial : Store := ⟨.atom 0, .atom 1, .atom 2, .atom 3, [.atom 4, .atom 5], []⟩
def result : Store := (run core initial).getD initial

def valuation (t c d h y x : Nat) : Fin 6 → Nat := fun i => [t,c,d,h,y,x][i.val]!
def diagonal (c : Nat) := I c (U c c)

theorem core_length : core.length = 251 := by decide +kernel

theorem symbolic_run : run core initial = some result := by decide +kernel

theorem result_spec (t c d h y x tail : Nat) :
    materialize (valuation t c d h y x) tail result =
      ⟨oldBundle (h+y) (d+x) c, c, d+x, h+y, tail,
        [diagonal c] ++ heads (d+x) (h+y) c d h ++ [t]⟩ := by
  rfl

theorem macro_result (t c d h y x tail : Nat) :
    AXMacro.run core ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ =
      some ⟨oldBundle (h+y) (d+x) c,c,d+x,h+y,tail,
        [diagonal c] ++ heads (d+x) (h+y) c d h ++ [t]⟩ := by
  have hrun := run_sound core initial result symbolic_run (valuation t c d h y x) tail
  rw [result_spec] at hrun
  exact hrun

#print axioms core_length
#print axioms symbolic_run
#print axioms result_spec
#print axioms macro_result
end PA194AXSymbolic

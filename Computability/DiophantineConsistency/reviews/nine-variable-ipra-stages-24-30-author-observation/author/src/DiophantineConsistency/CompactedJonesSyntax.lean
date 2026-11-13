import DiophantineConsistency.NaturalSimplifier
import DiophantineConsistency.WitnessCompaction
import DiophantineConsistency.ExecutableJonesCore

/-! # Matrix-free data of the simplified and compacted Jones syntax

The definitions of `SimplifiedJones` and `CompactedJones`, with their
original names; the proofs stay in those modules, which import Mathlib's
matrices (colliding with Foundation's `Matrix.map`). -/

namespace DiophantineConsistency.SimplifiedJones

def left {A : Prop} (r : Rep Empty (fun _ => A)) := r.expression.splitNatural.1.simplify
def right {A : Prop} (r : Rep Empty (fun _ => A)) := r.expression.splitNatural.2.simplify

end DiophantineConsistency.SimplifiedJones

namespace DiophantineConsistency.CompactedJones

def left {A : Prop} (r : Rep Empty (fun _ => A)) :=
  WitnessCompaction.leftClosed (SimplifiedJones.left r) (SimplifiedJones.right r)

def right {A : Prop} (r : Rep Empty (fun _ => A)) :=
  WitnessCompaction.rightClosed (SimplifiedJones.left r) (SimplifiedJones.right r)

def witnessCount {A : Prop} (r : Rep Empty (fun _ => A)) : ℕ :=
  QuarticCompiler.witnessCount (left r) (right r)

/-- Executable final syntax using the simplified natural gate source. -/
def expression {A : Prop} (r : Rep Empty (fun _ => A)) : Expr (Fin 9) :=
  ExecutableJones.expression (QuarticSyntax.expression (left r) (right r)) 0

end DiophantineConsistency.CompactedJones

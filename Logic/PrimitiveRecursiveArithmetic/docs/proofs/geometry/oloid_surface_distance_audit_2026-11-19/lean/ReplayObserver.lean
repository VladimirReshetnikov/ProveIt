import Observer

open Oloid.Observer

/-- Low-precision integration/optimization smoke test, spanning all three
contact counts. Bounds here are in physical unit-radius length units. -/
def main : IO Unit := do
  for (j,lo,hi) in [(1, (13:Rat)/10, (15:Rat)/10),(2,19/10,21/10),(6,25/10,27/10)] do
    let x := observe samples[0]! samples[j]! 0
    IO.println s!"P1-P{j+1} at n=0: {x}"
    unless lo < x && x < hi do throw <| IO.userError "observer smoke test failed"

import Lean
/-!
LEVEL FUZZER.  The kernel decides `Sort a ≡ Sort b` with
`is_equivalent(l1,l2) = (l1 == l2) || normalize(l1) == normalize(l2)`.
A *false positive* there is Type-in-Type, hence `False`.

Ground truth: two level expressions denote the same function of their
parameters iff they agree on every assignment (checked on a box).
-/
open Lean Elab Command

private def evalLvl (s : Name → Nat) : Level → Nat
  | .zero      => 0
  | .succ l    => evalLvl s l + 1
  | .max a b   => Nat.max (evalLvl s a) (evalLvl s b)
  | .imax a b  => let vb := evalLvl s b; if vb == 0 then 0 else Nat.max (evalLvl s a) vb
  | .param n   => s n
  | .mvar _    => 0

private def semEq (a b : Level) (box : Nat) : Bool := Id.run do
  for i in [0:box] do
    for j in [0:box] do
      for k in [0:box] do
        let s : Name → Nat := fun n =>
          if n == `u then i else if n == `v then j else if n == `w then k else 0
        if evalLvl s a != evalLvl s b then return false
  return true

private def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % (2^64)

private partial def genLvl (seed depth : Nat) : Level × Nat :=
  let r := lcg seed
  if depth == 0 then
    match r % 6 with
    | 0 => (Level.zero, r)
    | 1 => (Level.succ Level.zero, r)
    | 2 => (Level.succ (Level.succ Level.zero), r)
    | 3 => (Level.param `u, r)
    | 4 => (Level.param `v, r)
    | _ => (Level.param `w, r)
  else
    match r % 7 with
    | 0 => (Level.zero, r)
    | 1 => (Level.param `u, r)
    | 2 => (Level.param `v, r)
    | 3 => (Level.param `w, r)
    | 4 => let (a, r1) := genLvl r (depth-1); (Level.succ a, r1)
    | 5 => let (a, r1) := genLvl r (depth-1); let (b, r2) := genLvl r1 (depth-1); (Level.max a b, r2)
    | _ => let (a, r1) := genLvl r (depth-1); let (b, r2) := genLvl r1 (depth-1); (Level.imax a b, r2)

run_cmd do
  let env ← getEnv
  let mut seed : Nat := 987654321
  let mut lvls : Array Level := #[]
  for d in [1, 2, 3, 4] do
    for _ in [0:220] do
      let (l, s) := genLvl seed d
      seed := s
      lvls := lvls.push l
  let mut bad : Nat := 0
  let mut checked : Nat := 0
  let mut yes : Nat := 0
  let mut incompl : Nat := 0
  for a in lvls do
    for b in lvls do
      checked := checked + 1
      let sem := semEq a b 6
      match Lean.Kernel.isDefEq env {} (mkSort a) (mkSort b) with
      | .ok true =>
          yes := yes + 1
          unless sem do
            bad := bad + 1
            if bad ≤ (10 : Nat) then
              logError m!"*** LEVEL UNSOUNDNESS ***  Sort ({a}) === Sort ({b})  but semantically different"
      | _ => if sem then incompl := incompl + 1
  logInfo m!"[levels] levels={lvls.size} pairs={checked} kernelAccepted={yes} UNSOUND={bad} (incompleteness cases={incompl})"

/-
Kernel def-eq is HISTORY-DEPENDENT: `equiv_manager`'s union-find turns the
(non-transitive) def-eq relation into its transitive closure, and the closure is
consulted whenever two expressions happen to share a 32-bit `Expr.hash`.

Consequence: whether the kernel accepts `X =?= Z` depends on which *unrelated*
def-eq checks were performed earlier while checking the SAME declaration.

This is NOT unsoundness: every link of the chain is an individually valid
acceptance (proof irrelevance, iota), and transitively closing a semantically
valid relation stays valid.  The theorem that is accepted, `cnt N2 hs = 2`,
is true.  See ../../Reports/2026-07-29-defeq-history-dependence.md.

Reproduces identically on v4.32.0 and on v4.32.2 (patched for lean4 #14576).
-/
import Lean
set_option linter.defProp false
open Lean Elab Command

-- ---------------------------------------------------------------- the witness
inductive Ord2 where | zero | succ (n : Ord2)
inductive Lt2 : Ord2 → Ord2 → Prop where | s (n : Ord2) : Lt2 n (Ord2.succ n)

def accZero : Acc Lt2 Ord2.zero := Acc.intro _ (fun _y h => by cases h)
def accStep (n : Ord2) (ih : Acc Lt2 n) : Acc Lt2 (Ord2.succ n) :=
  Acc.intro _ (fun _y h => by cases h; exact ih)
def Racc : (n : Ord2) → Acc Lt2 n :=
  fun n => Ord2.rec (motive := fun n => Acc Lt2 n) accZero accStep n

noncomputable def cnt (x : Ord2) (h : Acc Lt2 x) : Nat :=
  Acc.rec (motive := fun _ _ => Nat)
    (fun x _hx ih =>
      Ord2.casesOn (motive := fun x' => ((y : Ord2) → Lt2 y x' → Nat) → Nat) x
        (fun _ => nat_lit 0) (fun y f => Nat.succ (f y (Lt2.s y))) ih)
    h

def N2 : Ord2 := Ord2.succ (Ord2.succ Ord2.zero)
noncomputable def hs : Acc Lt2 N2 := Classical.choice ⟨Racc N2⟩   -- opaque => `cnt N2 hs` is STUCK

example : cnt N2 hs = cnt N2 (Racc N2) := rfl   -- A = B   (definitional proof irrelevance)
example : cnt N2 (Racc N2) = 2         := rfl   -- B = C   (iota reduction)
-- example : cnt N2 hs = 2 := rfl               -- A = C   FAILS: `cnt N2 hs` never reduces

-- ------------------------------------------------------- expressions + padding
inductive Tag : Nat → Type where | mk : (n : Nat) → Tag n   -- forces a def-eq on its index

def NN2 : Expr := mkApp (mkConst ``Ord2.succ) (mkApp (mkConst ``Ord2.succ) (mkConst ``Ord2.zero))
def AA  : Expr := mkApp2 (mkConst ``cnt) NN2 (mkConst ``hs)              -- A, stuck
def BB  : Expr := mkApp2 (mkConst ``cnt) NN2 (mkApp (mkConst ``Racc) NN2) -- B
def CC  : Expr := mkRawNatLit 2                                           -- C
def padE (e : Expr) (n : Nat) : Expr :=
  mkApp (Expr.lam `x (mkConst ``Nat) e .default) (mkRawNatLit n)          -- (fun _ : Nat => e) n
def A' (k : Nat) : Expr := padE AA k
def C' (k : Nat) : Expr := padE (padE (padE CC k) 0) 0

def chainC (nm : Name) (pairs : List (Expr × Expr)) : Declaration :=
  .defnDecl { name := nm, levelParams := [], type := mkConst ``Unit,
              hints := .abbrev, safety := .safe,
              value := pairs.foldr (fun (l, r) acc =>
                Expr.letE `w (mkApp (mkConst ``Tag) r) (mkApp (mkConst ``Tag.mk) l) acc false)
                (mkConst ``Unit.unit) }

def tryAdd (nm : Name) (d : Declaration) : CommandElabM Bool := do
  match (← getEnv).toKernelEnv.addDecl {} d with
  | .ok _    => logInfo m!"[{nm}] KERNEL-ACCEPTED"; return true
  | .error _ => logInfo m!"[{nm}] kernel-rejected"; return false

elab "run" : command => do
  let env ← getEnv
  let A := A' 160526                                -- hash-colliding pair
  let C := C' 10933
  let A0 := A' 0                                    -- non-colliding control
  let C0 := C' 0
  logInfo m!"colliding : hash A'={A.hash}  hash C'={C.hash}   (depths {A.approxDepth}/{C.approxDepth})"
  logInfo m!"control   : hash A0={A0.hash} hash C0={C0.hash}"
  let iso (s : String) (a b : Expr) : CommandElabM Unit := do
    match Kernel.isDefEq env {} a b with
    | .ok r => logInfo m!"isolated {s} => {r}" | .error _ => logInfo m!"isolated {s} => ERROR"
  iso "A'=?=B  " A BB
  iso "B =?=C' " BB C
  iso "A'=?=C' " A C
  iso "A0=?=C0 " A0 C0
  logInfo "-- ONE declaration = ONE type_checker = ONE equiv_manager --"
  let _ ← tryAdd `t1_AC_alone      (chainC `t1_AC_alone      [(A ,C )])
  let _ ← tryAdd `t2_AB_then_AC    (chainC `t2_AB_then_AC    [(A ,BB),(A,C)])
  let _ ← tryAdd `t3_BC_then_AC    (chainC `t3_BC_then_AC    [(BB,C ),(A,C)])
  let _ ← tryAdd `t4_AB_BC_then_AC (chainC `t4_AB_BC_then_AC [(A ,BB),(BB,C),(A,C)])
  let _ ← tryAdd `t5_BC_AB_then_AC (chainC `t5_BC_AB_then_AC [(BB,C ),(A,BB),(A,C)])
  let _ ← tryAdd `t6_AB_BC_then_CA (chainC `t6_AB_BC_then_CA [(A ,BB),(BB,C),(C,A)])
  let _ ← tryAdd `t7_CONTROL_nohash (chainC `t7_CONTROL_nohash [(A0,BB),(BB,C0),(A0,C0)])
  logInfo "-- same three checks, THREE declarations = three type_checkers --"
  let _ ← tryAdd `u1 (chainC `u1 [(A,BB)])
  let _ ← tryAdd `u2 (chainC `u2 [(BB,C)])
  let _ ← tryAdd `u3 (chainC `u3 [(A,C)])
  -- ---- a REAL theorem accepted only when primed ----
  let eqTy   := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) A C          -- A' = C'
  let bare   := mkApp2 (mkConst ``rfl [1]) (mkConst ``Nat) A           -- @rfl Nat A' : A' = A'
  let primed := Expr.letE `w1 (mkApp (mkConst ``Tag) BB) (mkApp (mkConst ``Tag.mk) A)
                 (Expr.letE `w2 (mkApp (mkConst ``Tag) C) (mkApp (mkConst ``Tag.mk) BB) bare false) false
  let thm (nm : Name) (v : Expr) : Declaration :=
    .thmDecl { name := nm, levelParams := [], type := eqTy, value := v }
  let _ ← tryAdd `thm_bare   (thm `thm_bare   bare)
  let _ ← tryAdd `thm_primed (thm `thm_primed primed)
  liftCoreM <| addDecl (chainC `installed [(A,BB),(BB,C),(A,C)])
  liftCoreM <| addDecl (thm `paradoxical primed)

run

#print axioms installed
#print axioms paradoxical
example : cnt N2 hs = 2 := paradoxical
-- example : cnt N2 hs = 2 := rfl   -- still fails: fresh type_checker, no priming

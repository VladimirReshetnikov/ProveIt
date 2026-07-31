/-
PROJECTION INDEX TRUNCATION — `size_t` narrowed to `unsigned` in the kernel.

`Expr.proj` stores its field index as a `Nat`.  Three kernel paths in
`src/kernel/type_checker.cpp` (`infer_proj`, `reduce_proj`, and
`lazy_delta_proj_reduction`) move that index into a C++ `unsigned` after
checking only `is_small()`, which guarantees `< 2^63`, not `< 2^32`.  An index
of `2^32 + k` therefore silently becomes `k`.

Consequence: the kernel infers types for, reduces, and ACCEPTS declarations
containing projections whose index is out of range for the structure, treating
them as the aliased in-range field.  The surface elaborator refuses such indices
("Index `4294967298` is invalid for this structure"), so the defect is reachable
only from a metaprogram building `Expr.proj` directly — but `addDecl` is the
ordinary checked path, and it accepts the result.

This is NOT, by itself, a proof of `False`.  Truncation is applied consistently
by inference and by reduction, so the aliased projection stays internally
coherent: `x.(2^32+1)` behaves exactly like `x.1`, a true statement about a real
field.  Turning it into `False` requires two *distinct* fields to collide, i.e.
a structure with 2^32 fields — which is why upstream rates it P-medium.  What it
does establish is that the kernel's range check on projection indices can be
bypassed, and that `is_small()` is not a sufficient guard.

Upstream: lean4#12746 (OPEN, P-medium, filed 2026-03-01, found by Opus 4.6).
lean4#13602 reported the same defect as an accepted theorem and was closed as a
duplicate of #12746.  Neither is fixed.

Verified with `elan run leanprover/lean4:<v> lean --trust=0` on this file:

  | toolchain    | truncated index accepted | control (index 2) |
  | v4.32.0      | yes                      | rejected          |
  | v4.32.2      | yes                      | rejected          |
  | v4.33.0-rc1  | yes                      | rejected          |

CONTROL (`smallOutOfRange`): the identical construction with a small
out-of-range index is rejected by the kernel, which is what makes acceptance of
the truncated index meaningful — the range check exists and works, and is
defeated only by the narrowing.

All `addDecl` calls below use the SYNCHRONOUS kernel entry point
`(← getEnv).toKernelEnv.addDecl {}`, not `Lean.addDecl`, because the latter is
asynchronous in 4.32.x and would report kernel rejections as acceptances.
-/
import Lean
open Lean

structure Pair where
  first : Nat
  second : Nat

/-- `(Pair.mk 0 1).<idx> = 1`, proved by `rfl`, submitted to the kernel. -/
private def acceptsProjAt (idx : Nat) : MetaM (Except Kernel.Exception Unit) := do
  let kenv := (← getEnv).toKernelEnv
  let v := mkApp2 (mkConst ``Pair.mk) (mkNatLit 0) (mkNatLit 1)
  let stmt := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) (Expr.proj ``Pair idx v)
                (mkNatLit 1)
  let prf := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit 1)
  let decl := Declaration.thmDecl
    { name := `probe, levelParams := [], type := stmt, value := prf }
  return (kenv.addDecl {} decl).map (fun _ => ())

run_meta do
  -- In range: `second` is 1, so the theorem is honest.
  match ← acceptsProjAt 1 with
  | .ok _ => logInfo "idx 1 (in range): accepted — expected, this is field `second`"
  | .error e => logError m!"idx 1 unexpectedly rejected: {e.toMessageData {}}"

  -- OUT of range: 2^32 + 1 must not name a field of a two-field structure.
  match ← acceptsProjAt (2 ^ 32 + 1) with
  | .ok _ =>
      logInfo "idx 2^32+1 (OUT of range): ACCEPTED — index truncated to 1 (lean4#12746)"
  | .error e => logInfo m!"idx 2^32+1 rejected (defect fixed?): {e.toMessageData {}}"

  -- CONTROL: small out-of-range index, no narrowing involved.
  match ← acceptsProjAt 2 with
  | .ok _ => logError "CONTROL FAILED: kernel accepted small out-of-range index 2"
  | .error e =>
      logInfo m!"control OK — small out-of-range index 2 rejected: {e.toMessageData {}}"

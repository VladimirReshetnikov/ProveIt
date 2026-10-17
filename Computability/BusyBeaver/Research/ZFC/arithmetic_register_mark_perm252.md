# Internal marking of a primary register

[`ArithmeticRegisterMarkPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterMarkPerm252.lean)
marks one primary register in the frozen 252-state table. For a fixed finite
prefix `pre` with `pre.length < 9`, the exact endpoint is

```
runFrom (2*fileTime pre+3)
  (frame (skipCode pre.length : V) left
    (fileCode pre (registerBlock value right)))
 = leftFrame (markExit pre) left
     (fileCode pre (4*bitPrefix true value right))
```

All register values and both complete tape halves range over every IΣ1 model.
The target's `0,1,ones(value)` becomes `0,0,ones(value)`, preserving every other
bit. The complete right half is arbitrary: no spare-count or suffix-shape
premise is needed. An empty prefix retains return entry 4; a nonempty prefix
ends at probe 7. The prefix length and selector are external finite data,
covering the nine physical positions. This is not an internal variable-length
list or arbitrary internal-selector theorem.

State numbers use arithmetic coding, one above the canonical table index;
0 means halt. The nine literal selector codes are
`[60,44,31,56,38,40,28,1,68]`. Each zero separator lowers this finite selector
by one, then the chosen state's one self-loop scans the entire unary block.
Actual rows 60/2/4 erase the target header in three moves. The checked
mark-return family uses entries 4/7 and one-loop 6. Finite prefix induction
composes these with the already proved all-internal uniform scans; the total
clock is `2*fileTime pre+3`.

For the known spare family, instantiate `right` with the remaining primary
registers, eight zero spares, the distinguished one, and a variable zero tail.
Mark preserves that tail exactly. Its marked target feeds the checked
[increment](arithmetic_register_file_perm252.md),
[positive decrement](arithmetic_register_decrement_perm252.md) or
[zero decrement](arithmetic_register_zero_perm252.md) interfaces. Positive
decrement alone appends a zero spare. This marking checkpoint does not assert
first exit, an absolute head, a stored-PC update or return to dispatch. The
all-internal symbolic instruction/refinement layer remains separate; the
existing Nat instruction theorem is not a theorem about nonstandard models.
No machine table, calculus or consistency endpoint changes here.

The proof follows `RegisterMarkPerm252` and the attributed mira-emmy PR20
`Box.v` contracts. Mira-Cult, Jeff and Wade retain their machine,
verification and framework attributions.

The [fresh check](results/arithmetic-register-mark-perm252-verification.json)
passes eight ordered axiom reports and twelve callers, with standard Lean
axioms only and zero warnings. Source and audit took 2.754 and 2.524 seconds
on pinned Lean 4.32.0. Exactly 37 project providers, five external first
providers, actual direct Lean/Omega imports, all 94 input identities and the
fresh object are checked. Dependencies were reused without build or download.
The source passed on its first attempt and remained unchanged. Run1 retains
an audit-only `by decide` free-variable rejection for `[x].length < 9`; using
`by simp` fixes that same guard without changing any caller.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_mark_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --zero-evidence /outside/successful-register-zero/verification.json \
  --output /outside/new-empty-register-mark-check
```

The portable checker verifies the zero 6/10 predecessor, exact selected
source/object closure, dependency pins and actual first Lean/Omega providers,
then freshly checks only this source and its audit. `--cache` relocates all
selected project objects while requiring the same hashes. The maintained
preflight is **PREPARED_NOT_BUILT**, with no proof commands; maintained source
and audit match the successful snapshots. Only the portable frozen default
audit hash differs from the executed original checker, which used an explicit
override. Three argument/provider rejection controls pass without proof
compilation. The [publication record](results/arithmetic-register-mark-perm252-publication.json)
keeps these checks and the historical nonpass separate.

The [independent final review](results/arithmetic-register-mark-perm252-review.json)
binds the entire proof, audit, portable guard and maintained preflight to
exact bytes. It checks 531 identities across 100 paths without a reviewer
proof rebuild. The original source-pass/audit-failure attempt remains separate.

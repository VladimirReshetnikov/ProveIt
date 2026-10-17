# Internal zero decrement preserves the register file

[`ArithmeticRegisterZeroPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterZeroPerm252.lean)
proves the zero branch of marked-register decrement for the frozen 252-state
table. For fixed finite lists `pre` and `rest` of arbitrary internal register
values, its endpoint is

```text
runFrom (2*fileTime pre+5)
  (frame 43 left (fileCode pre (4*fileCode rest (zeroBlocks count 0))))
 = leftFrame 5 left
     (fileCode pre (registerBlock 0 (fileCode rest (zeroBlocks count 0))))
```

The marked zero becomes the ordinary zero block. Every register value and
the spare count are preserved. The values, count and complete left tape half
range over an arbitrary model of IΣ1; list lengths are externally fixed.
The full register-file endpoint has a blank right exterior. Its local
`zero_box` theorem allows an arbitrary complete right suffix after the
required leading zero. The even-suffix lemma supplies that zero for every
register file and zero-spare tail, including an empty suffix and count zero.

The exact restoring path is

```text
(43,L,8R) → (59,2L,4R) → (74,4L,2R) → (2,2L,4R) → (3,L,8R+2).
```

One further transition enters the leftward return scanner. Seeking and
returning over the prefix each take `fileTime pre`, yielding the stated
`2*fileTime pre+5` steps. Arithmetic state numbers are one greater than
canonical working-state numbers; arithmetic state zero denotes halt.

This completes the zero case alongside the
[positive-decrement endpoint](arithmetic_register_decrement_perm252.md),
which appends one zero spare, and the
[full register-file increment](arithmetic_register_file_perm252.md).
The fixed boot suffix `rest ++ replicate 8 0 ++ [1]` with `56+count` zero
spares is an explicit audit caller. The subsequent
[register-marking proof](arithmetic_register_mark_perm252.md) completes the
four box operations. Dispatcher refinement and the internal binary/scheduler
equivalence remain separate steps. This
module asserts neither first exit nor a PA consistency endpoint, and changes
no transition table. Its contracts follow the attributed
`RegisterBoxesPerm252` and mira-emmy PR20 work; Mira-Cult, Jeff Ketchersid and
Andrew James Wade retain their machine and framework credit.

The [fresh verification](results/arithmetic-register-zero-perm252-verification.json)
passes six ordered axiom reports and ten callers, with the standard three
Lean axioms and zero warnings. Source and audit take 2.545 and 2.286 seconds
on pinned Lean 4.32.0 with one thread and `-M4096`. Exactly 36 project
providers, five external boundaries, the actual first Omega provider,
all 92 input identities and the fresh object are checked. No dependency is
built or downloaded. Run 1 failed to normalize a recentered left tape half;
run 2 adds one explicit `leftFrame_even` rewrite. All statements and audit
callers are unchanged, with no increased resource limit.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_zero_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --decrement-evidence /outside/successful-positive-decrement/verification.json \
  --output /outside/new-empty-zero-decrement-check
```

The portable guard verifies the exact positive-decrement 10/12 predecessor,
source/object closure, pinned dependencies and actual first providers.
Its maintained-default preflight is **PREPARED_NOT_BUILT** and runs no proof
compiler. The original successful record is byte-preserved; the portable
guard freezes the final source hash used by that run's explicit override.
Three rejection controls cover Python `-O`, nonempty output and a fake first
Omega provider. The [publication record](results/arithmetic-register-zero-perm252-publication.json)
separates the kernel check, failure history, unbuilt preflight, guard controls
and [independent final review](results/arithmetic-register-zero-perm252-review.json).

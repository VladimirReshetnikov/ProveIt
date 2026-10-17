# Arithmetic interpretation of the finite symbolic tape

[`ArithmeticSymbolicTapePerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicTapePerm252.lean)
interprets the actual existing `Segment`, `Token` and `SConfig` syntax as
complete numeric tape halves. It reuses the existing `norm`, `normL` and
`isMatch` definitions. Every accepted `isMatch` comparison gives equality of
the full numeric configuration, retaining state and left-facing orientation.

A run's length is `a*gap+c`, where `a`, `c`, Boolean labels and all syntax
lists are external finite data. The gap and the values produced by box
prefixes range over an arbitrary IΣ1 model. Boxes are parameters
`Box → V → V`; the normalization theorem needs no execution or definability
law for these functions. Concrete register boxes and their formula graphs
remain a separate interface.

The arithmetic foundation is the all-internal law

```
bitPrefix b (n+m) suffix = bitPrefix b n (bitPrefix b m suffix)
```

Its Σ1 induction fixes the other parameters. External finite-fold induction
then proves that conversion to tokens, deletion of zero-length runs and
merging adjacent equal-bit runs preserve numeric prefixes, including an
arbitrary terminal suffix.

`dropExterior_zero` and `normL_zero` deliberately use terminal numeric 0.
The final false run maps 0 to 0; all earlier prefix functions receive exactly
the same value, including parameterized box functions. This justifies the
left-exterior normalization used by actual `isMatch`. The configuration
interpretation likewise starts each whole tape half with terminal 0. No
general-suffix deletion is used. State codes follow the actual
`ArithmeticMachinePerm252.stateCode`, with 0 for halt.

This is a tape-algebra checkpoint. Fixed external syntax may contain
internally long runs; it is not an internal variable-length syntax datatype.
Concrete box effects, an arithmetic symbolic-step theorem, positive clocks
and the complete binary/scheduler refinement remain separate obligations.
The existing symbolic syntax and checker retain their Mira-Cult, Jeff and
Wade framework attributions through `SymbolicPerm252`. No machine table,
calculus or consistency endpoint changes.

The [fresh check](results/arithmetic-symbolic-tape-perm252-verification.json)
passes ten ordered axiom reports and twelve callers, with standard Lean
axioms only and zero warnings. Source and audit took 2.843 and 2.161 seconds
on pinned Lean 4.32.0. The merged dependency pool has 36 project providers:
the pinned UniformScans 21/18 closure and the native symbolic module's actual
11-module import traversal, with shared source/object identities checked.
The native 169-unit evidence itself is byte-pinned. Five external first
providers, direct Lean imports plus Omega, all 93 inputs and the fresh object
are checked before and after. No dependency was rebuilt or downloaded.

Run1 preserves an unsolved normalization goal and one unused-simp warning.
Run2 changes only that cons-case proof to an explicit foldr goal and existing
rewrites; definitions, theorem statements and audit callers are unchanged.
The successful record is retained byte-for-byte.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_symbolic_tape_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --scans-evidence /outside/successful-uniform-scans/verification.json \
  --native-evidence /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/results/command-word254-integration-verification.json \
  --output /outside/new-empty-symbolic-tape-check
```

The portable checker freshly checks only this module and its audit after
validating the exact selected source/object pool and actual first providers.
`--cache` relocates all selected project objects while preserving hashes.
Its maintained-default preflight is **PREPARED_NOT_BUILT**, with no proof
commands. Maintained source and audit match the successful snapshots; only
the portable frozen default source hash differs from the executed original
checker, which used an explicit source override. Three argument/provider
rejection controls pass without proof compilation. The
[publication record](results/arithmetic-symbolic-tape-perm252-publication.json)
keeps the proof, preflight, controls and historical nonpass separate.

The [independent review packet](results/arithmetic-symbolic-tape-perm252-review.json)
preserves the full mathematical source/audit/guard read and a separate final
proof/preflight binding. The latter checks 535 identities across 99 paths,
plus the native symbolic import traversal. Reviewers perform no proof rebuild.

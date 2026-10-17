# Compact finite control and the common dispatch frame

`ArithmeticFiniteControl254.lean` supplies compact arithmetic constants, a fixed
bounded finite lookup graph, and an exact common representation of accepted
finite decoder paths. These are substrate lemmas for a represented variable-PC
interpreter. The actual6,460-row control table, its represented step/run, and the
all-internal L2 scheduler comparison remain open.

`binaryTerm` constructs a constant from a fixed least-significant-first bit list
by `(1+1)*child+bit`. The child appears once. Its value in every IOpen model is
the existing native `bitsCode` cast into the model. This avoids unary expansion
of large PC constants. The audit includes an actual34-bit maximum PC witness,
with native code15,952,311,447, without unfolding that many unary additions.
The maximum designation comes from the Python inventory; this caller does not
prove a global maximum over the formal row list.

`lookupDef rows` is an explicit parameter-freeΣ0 formula for any externally
fixed finite row list. Its key and branch inputs are arbitrary internal model
elements. Zero selects the first output; every nonzero branch input selects the
second. Missing keys produce0. `lookup_supported` classifies any nonzero result
by an actual member of the fixed list; it needs neither a standardness premise
for the key nor unique rows. Duplicate numeric keys use the first matching row.
For a later actual table, uniqueness must concern numeric key values, since
trailing false bits preserve a key's denotation. Use a positive opcode/descriptor
to establish validity: a legitimate PC field can itself be0.

Under IΣ1, `bitsPrefix_split` and `start_fixed_frame` identify the complete actual
`Site.start` interpretation with a single40-bit frame:

```
frame95 1 (pc + bitPrefix false40
  (bitPrefix false gap (2*boxPrefix(values,count,unchanged,0)+1))).
```

This is whole-configuration equality for every external path of length≤40 and
arbitrary internal gap, spare count and register values. It retains the existing
spare layout and literal final padding. It does not assert a binary execution,
first-exit property, or graph for a variable-length internal list.

The focused pinned Lean4.32 check passed in3.845619s for the168-line source and
2.264626s for the67-line audit: eight ordered axiom probes, thirteen generic/
concrete callers, only `propext`, `Classical.choice`, `Quot.sound`, and zero
warnings. It reused the exact79-project closure from successful DispatchRebase
evidence plus six pinned external boundary providers. All181 recorded inputs and
the fresh object were unchanged after the audit. No dependencies, bootstrap,
233 coverage chunks, or8,391 binary guards were rebuilt.

Three failed development attempts remain in the publication record: premature
unfolding of term evaluation; vector-function rewrite orientation; then explicit
coherence of the imported numeral2 with1+1. They changed proof normalization,
with no change to the lookup policy or frame statements. The original successful
record/driver remain unchanged. The maintained guard changes only the final
source hash pin; prepare-only and four negative controls exercise that guard
without repeating the proofs.

A portable guarded fresh check uses an existing built pinned dependency checkout
and the successful Rebase evidence/cache:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_finite_control254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --rebase-evidence /path/to/arithmetic-dispatch-rebase-perm252-verification.json \
  --output /outside/new-empty-directory
```

Add `--prepare-only` to verify the compiler, selected source/object providers and
closure without compiling a source/audit. `--cache` may relocate all project
objects when their hashes match. Actual first Init/Omega and external providers
are checked; no download or dependency build is performed. The core Std-only
umbrella is not expanded by this separate arithmetic checkpoint.

Separately, a scratch Python extraction checked all6,460 false-first DFS leaf
controls of literal `Prog254` (6,459 nodes), all8,390 successor edges/8,391 guard
cases, and five table mutations in0.96s. The initial leaf is path000/`decnz8`
(physical register1); zero→control3 and positive→control2. That table is untrusted
formal data. Its future certificate can derive entries from `ActualTree254` and
reuse existing accepted-site coverage and all-model rebasing, rather than repeat
binary guard evaluation. Native path increment and the LSB tape encoding must
remain separate. No new binary halting equivalence, PA consistency endpoint,
calculus reduction or state-count claim follows from this checkpoint.

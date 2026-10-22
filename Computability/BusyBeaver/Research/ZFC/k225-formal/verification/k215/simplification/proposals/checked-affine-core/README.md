# K215: checked affine cores and CM215 endpoint verification

Research packet for incorporation in Vladimir Reshetnikov's **ProveIt**,
21 October 2026.

Reviewed revision: `56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`.

**No verified machine with 214 or fewer states is delivered.** The packet
provides a checked source-proof reduction, an applied Lean proof refactor,
verification of an existing second 215-state endpoint, and a precisely scoped
214-state runtime experiment with an independently replayed obstruction.

## Read first

`report.pdf` is the mathematical report; `report.tex` and the three included
TeX fragments are its complete source. It explains the proof architecture,
the drain and contraction theorems, literal-program bindings, candidate
comparison, actual state-reduction results, and an incremental integration
plan. Exact compiler outcomes and source identities are recorded in the
component receipts rather than inferred from the existence of generated files.
`VERIFICATION.json` indexes the accepted formal receipts and their hashes,
source exceptions, compiler metrics and the separately scoped search results.

| Component | Main result | Important scope |
|---|---|---|
| `affine_core/` | Both literal `p215` and `dagPerm` halt iff their common accelerated core halts, for every natural-valued register file | 1,059 drains contracted; 367 retained control vertices; the binary TM still has 215 states |
| `lean_integration/` | Exact CM215 endpoint attachment and a checked `KSeedModel222` proof patch | CM215 and the patch design are inherited; the packet supplies current-snapshot integration and checks |
| `state_search/` | New quotient/deletion experiments, independently checked counterexamples, and all 1,900 quantified increment contracts for a rejected no-append skeleton | The first-redispatch zero-decrement obligation fails; no 214-state consistency result follows |

## The proof simplifications

The direct Lean patch removes three repeated formula inductions in
`KSeedModel222.lean`. A named equality-free bundle is derived directly, then
the already proved semantic encode/decode theorem transfers satisfaction to
the decoded bundle. The module decreases from **269 to 234 lines** and from
**11,711 to 10,436 bytes**, with unchanged public `seed_eqFree` and endpoint
statements. The internal helper API changes. The final acceptance gate is the
ten affected project modules plus four typed endpoint clients, not just the
edited file in isolation.

A separate resource adjustment splits each of four large certificate proofs
into four smaller kernel-checked lemmas. The public statements and all literal
machine, program and certificate data are unchanged. The completed baseline
therefore uses 180 byte-identical project modules and four explicitly recorded
proof-body overlays. The original sources and the exit-137 failure under an
8 GiB memory limit are preserved. A companion generator postpass reproduces the four checked
replacements exactly and leaves the other fourteen generated source modules
byte-identical. This applies an existing batching technique and adds 100 lines
across the four generated proof modules (11 to 36 lines each); it is not part
of the 35-line handwritten saving above.

The source-level affine proof makes a different improvement. A single theorem
proves the exact behavior of an arbitrary drain loop; generic adequacy and
contraction theorems turn finite checked data into an all-register equivalence
for both literal programs. The exported result has the existing source theorem
type, and a same-name facade and typed client exercise that interface. This is
an auxiliary source lane, checked with Coq 8.18.0. It does not rebuild the
complete production Rocq binary-machine/ZFC endpoint.

The accelerated relation still refers to the original graph data. Its
367-control interface follows from checked entry, membership and closure
facts. Generated graph/rank and location sources total **284,987 bytes**,
larger than the earlier **109,958-byte** normalized certificate. No overall
byte-size or compilation-time reduction is claimed. Keep the direct
normalized-certificate path until measurements or a new source with different
loop implementations justify changing the default.

For the largest remaining runtime proof, the report gives a concrete plan to
attach the existing framed-decoder pilot: prove its literal source binding,
construct block-chain premises for every valid source path, and discharge the
97 primitive-entry interfaces with prefix-sensitive carry/strip and register
contracts. Its 281 local blocks and 234 decoder roles are prior work, already
checked locally; the full site-coverage attachment remains future work. The
two-bit history sufficient for internal decoder blocks must not be assumed
sufficient for arbitrary leaf and return behavior.

## Which additional 215-state candidate?

CM215 is the most economical *incremental endpoint proof* among the inspected
packets: its source program is unchanged, six transition rows change, and a
three-clause invariant supports positive one- or three-step simulation blocks.
It reuses the complete K215 calibration. Its 430 literal rows are compared
with the Lean definition. This is not a claim that its entire independent
proof foundation is shorter.

M124/FM215 has a smaller isolated marker argument (four changed rows and two
marker clauses), but its exact dense-semantics adapter remains a separate
integration task. ZC215 has attractive scheduler mathematics, while its
end-to-end physical endpoint requires more work. The report compares these
routes without treating transition-edit count as proof complexity.

## What happened at 214 states?

The no-append experiment changes native row `66/0` from `1 R198` to `0 L54`
and deletes native state 198 (dense state 189). The table has 214 listed
working labels; 212 remain graph-reachable after the edit. The inherited
symbolic checker verifies all **1,900 source increment occurrences** for
arbitrary register values, gap and nonempty spare suffix, preserving that
suffix exactly. This is quantified symbolic verification outside a proof
assistant, not bounded numerical testing and not a new kernel theorem.

The shared helper also performs zero-decrement restoration. At the delivered
`0100 / CD0` witness, the ordinary table first redispatches correctly after
640 transitions; the edited table first redispatches after 3,966 with wrong
logical registers and continuation. An independent simulator replays both
runs. The file is therefore prominently named
`state_search/rejected_noappend214.native.tm`.

The broader relaxed-spare deletion screen tests 24,824 row replacements. All
59 short-screen survivors have independently checked obstructions: 50 wrong
first-redispatch outputs and nine exact configuration cycles. Bounded failures
of the other candidates are not promoted to universal negative results. These
experiments neither prove a 214-state lower bound nor decide a mutated table's
blank-tape consistency calibration.

A separate coordinated provider family contains **639** tables. Independent
replay establishes 568 explicit primitive-contract obstructions and 71 bounded
failures. All 109 short-screen survivors have explicit wrong-output witnesses.
Three supplied variants preserve the parent's entire first decoded blank-start
frame and pass more than 5,900 guarded source cases, but their eventual bad
prefixes do not even read the register data. At their failing source addresses,
the continuation is wrong for either decrement branch and for every legal
register/gap/spare valuation. These examples show why a long passing test
prefix is insufficient. The separate `state_search/forced_provider189/README.md`
describes the exact family, the witnesses and the limits of the conclusions.
The companion `source_reachability/` packet identifies the failures in the
mandatory final AX gate. A short independently replayed entry prefix, literal
source binding and inherited total macro-run theorems give an ordinary
eventual-visitation argument for the parent source. This is stronger than
failing to find an address in a bounded trace, but it is not a new kernel
reachability theorem or a calibration theorem for an altered binary table.
The provider-role analysis also isolates a six-leaf region containing two
disjoint transfer loops. Three simple source swaps/reassociations and literal
rewiring experiments still have 215 working states. The source arguments and
physical table counts are recorded separately; no runtime correctness is
inferred for those rewires.

## Reproduction

Python 3 is sufficient for artifact identity and finite witness checks:

```sh
python3 verify.py
```

The top-level verifier hashes every archived payload file and runs the search
audits, including the coordinated provider witnesses, in a temporary copy,
preserving the original receipts. It does not
compile formal proofs. To rerun the symbolic arbitrary-value increment
contracts as well:

```sh
python3 verify.py --universal
```

The focused Coq build, including its separate recursive `coqchk`, is:

```sh
cd affine_core
python3 verify_data_binding.py
python3 build.py
```

`lean_integration/README.md` provides the exact Lean 4.32.0 baseline,
CM215 and changed-calculus commands, memory setting, resumability requirements
and source manifests. The baseline closure and its checks must be accepted
before checking either integration. Source files are included; toolchains and
compiled proof objects are not.

The report can be rebuilt with a TeX installation containing the standard
packages named in its preamble:

```sh
python3 build_report.py
```

This writes `build/report.pdf` and its TeX log without replacing the archived
PDF. `python3 verify.py --hashes-only` performs only the identity checks.
Rebuilding a component may create or update its build products and receipts;
retain an untouched extraction when comparing against the supplied manifest.

## Integration and attribution

Review the small Lean source and driver patches independently. Keep the CM215
exact-table bindings and endpoint with its earlier transport proposal. Add the
affine core as an optional source lane before considering any replacement of
the maintained certificate path. Keep the rejected machine and negative
search results under research, separate from accepted candidate tables.

The earlier affine proposal already discovered the drain decomposition and
matrix dictionary. The existing transport proposal already designed CM215,
its invariant, transport theorem and endpoint wrapper. The three-induction
patch also predates this packet. Their original work is credited in
`NOTICE.md`, the report and the component notices. The new proof completion,
verification work and search results are distinguished explicitly. All
vendored reference bytes are bound to the reviewed revision by the component
source manifests.

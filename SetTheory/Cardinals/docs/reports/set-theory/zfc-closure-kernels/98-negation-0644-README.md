# Theory controls and independently audited source identities

This directory provides a portable research supplement to the direct-negation
machine search. It establishes a new register-source identity and records
complete alternative-basis compiler controls. It does **not** claim a new
literal binary Turing machine with a proved ZFC consistency equivalence.

## Reproduce

Python 3.10 or later is sufficient; all code uses the standard library and all
runtime inputs are included. From any working directory:

```sh
python /absolute/path/to/theory/verify_packet.py
python /absolute/path/to/theory/verify_packet.py --church-search
```

The first command checks all vendored source hashes and runs the AST,
symbolic-negation, affine-commutation, and partial-rewrite checks. The second
also repeats the complete 7,500-trial coarse Church-basis search, compares
every saved transition-table hash, and checks all 50 emitted fine words.
On the research machine, the full Church search took about 28 seconds.
Runtime varies with hardware. It writes temporary compiler results to a
fresh temporary directory and removes them after comparison. The audit JSON
files are regenerated beside the scripts.

The smaller commands are:

```sh
python audit_negation_peephole.py --words church-results/fine_words.json
python audit_affine_commutation.py
python audit_source_variants.py
python church_basis_experiment.py --seeds 50 --output /tmp/church-replay
```

## Exact negation contraction

Let `P(x,y) = (x+y)(x+y+1)/2 + y`. In the actual fine token vocabulary,

```text
L N P Q M V Q P W  ->  L M P W
```

holds at a constructor boundary with scratch registers 6 and 7 zero. Both
sides terminate, preserve the logical stack and the other registers, clear
the two scratches, and replace top `t` by `4 P(t,1)`. The old word pushes its
operand onto the stack and immediately unpairs that cell. The new word
retains the operand in scratch storage. In fact, equality of the two local
programs requires only register 7 zero; if register 6 initially contains `u`,
both output `4 P(t+u,1)`. Both-zero is the intended formula-constructor
interface and is established at every audited site.

`negation_peephole_proof.tex` proves the pair, unpair, transfer, and copy-loop
contracts for all natural register values, then derives the identity.
`audit_negation_peephole.py` independently executes the supplied actual AST
and performs a symbolic replay of each full AX body using those contracts.
Symbolic variables stand for arbitrary initial register values; only the two
scratch values start at zero. The program checks each occurrence's incoming
scratch values and all nine final register expressions. The unchanged
`YZGaZ` gate/cleanup suffix is reached with exactly the same state.

The finite AST regression checks are 432 general pair cases, 512 clean
unpair cases, and 256 complete negation cases, comprising 2,297,532 primitive
operations. Nonzero-scratch counterexamples prevent the proof from being
misread as an unconditional peephole. Finite tests are supporting checks;
the all-values assertion follows from the displayed loop invariants and
symbolic replay.

The original routed AX word has 30 clean occurrences and shortens from
1,270 to 1,120 fine terminals. All 50 supplied Church/control words also
pass, giving 51 complete word audits in `negation_audit.json`.
`audit_source_variants.py` checks a further 135 supplied old/new pairs:
130 partial contraction variants and five direct contraction variants,
with 1,919 local applications. Each new word is compared with its own base;
different base formulas need not have identical numerical encodings.

### Established command-boundary premise

The exact original-source premises are in `vendor/reference/L2Root254.v`:

- `enc` puts zero in scratch registers 6 and 7 and selector register 3.
- `prefix_ok` returns a nine-field record whose scratch fields are explicitly
  zero after fetching and reading a command.
- The selector-handling prefixes in `disp_1`, `disp_2`, and `disp_ax`
  decrement only register 3 before entering the selected command.
- In the AX case, `root_sem` applies `ax1` with both zero premises discharged
  by reflexivity. Every nonhalting root command returns `enc` of the next
  enumerator state.
- `root_step_gen`, `root_step_det`, and `iter_halts_dag` give the iterated
  command interface. `Main254.R0_enc` gives the original initial relation.

`ProgLib254.v` contains the original corresponding contracts `w198`, `w200`,
and `w193` for the parameter-copy loops; `unpair115` and `unpair116` for the
two unpair loops; `pair162` for pairing; and `w117` for multiplication by four
while moving scratch. Some fine ASTs regroup the original code and exchange
adjacent increments. Their contracts here are proved directly on the actual
fine control graphs. The original Coq declarations are therefore precise
interface/provenance references, not a claim that a changed AST is literally
the Coq term in that declaration. Transferring the interface to a routed
compiled source uses its existing source-equivalence certificate.

All three Coq files were compared by Git blob identity with the current
ProveIt tree at `fd1adfa19f8fe8da41444e3fa43b89a59d891067`:

| File | Git blob |
|---|---|
| `L2Root254.v` | `d5abf0ccb48f6d6dc6afa28af3d5f914ab08e30a` |
| `ProgLib254.v` | `cce027d6ee49c30e36ad270e9fec1c422d5fd012` |
| `Main254.v` | `f057d40d3ecbf6251f9951cfb6f499d6faa776e2` |

The original repository paths are recorded in `vendor_sources.json` and
can be opened at the pinned commit under
`lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/`.

### Related prior construction

Current ProveIt intake source 56 already records a pairing-shift negation
identity `P(x,1)=P(0,x)+2`, hence `Neg(x)=4 P(0,x)+8`. See
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-159-source-56.md`
and `intake-158-159.md` at the same pinned commit. This is relevant prior
constructor optimization. The present operand-retention contraction is a
different identity and comes with its own complete occurrence/scratch audit.
This packet does not claim to repair the missing whole-AX source evidence
identified for the separate prior 255-state pairing-shift candidate.

## Exact affine commutations

`audit_affine_commutation.py` recognizes 22 fine tokens as exact affine maps
on the nine registers. A recognized loop has one decreasing guard, a zero
exit, and an increment-only positive branch returning to the same guard
without incrementing it. Induction gives the exact map. Homogeneous 10 by 10
integer matrices then certify commutation by exact multiplication.

This yields 44 overlapping-support pairs beyond 134 disjoint-support pairs:
178 safe unordered pairs in `affine_pairs.txt`. The JSON contains guards,
finite control paths, increment vectors, and matrices. In particular, `WM`
commutes with `MW`, and `NM` with `MN`. No random sampling or finite-field
test is used to infer these identities.

## Measured complete Church-basis controls

`theory_exploration.tex` gives the formulas, falsity/dual-row dependency,
ordinary proof-theoretic explanation, and measurements. `L` is the inherited
single-axiom propositional row. `K`, `S`, `P`, `DNE`, and `PF` are the displayed
Church combinator, Peirce, double-negation, and falsity-specialized Peirce
rows. Only the explicit DNE basis is combined with the dual quantifier row:
the old quantifier row supplies ex falso in the Peirce controls, a dependency
that must not be silently lost.

These are measurements in the public coarse Wade backend. Its unchanged
control already costs 269 states, so the numbers do not predict costs in the
compact routed runtime.

| Basis | Quantifier row | Bundle | Fine terminals | Decision states | Framework | Working states |
|---|---|---|---:|---:|---:|---:|
| L | old | original | 1270 | 206 | 63 | 269 |
| L | old | DNE simplified | 1126 | 208 | 62 | 270 |
| KSP | old | original | 1331 | 210 | 62 | 272 |
| KSP | old | DNE simplified | 1187 | 210 | 63 | 273 |
| KSDNE | old | original | 1329 | 210 | 63 | 273 |
| KSDNE | old | DNE simplified | 1185 | 211 | 63 | 274 |
| KSDNE | dual | original | 1329 | 211 | 63 | 274 |
| KSDNE | dual | DNE simplified | 1185 | 213 | 62 | 275 |
| KSPF | old | original | 1330 | 210 | 63 | 273 |
| KSPF | old | DNE simplified | 1186 | 211 | 63 | 274 |

There are 50 emitted fine words. Each row order receives 50 seeds and three
grammar exponents, totaling 7,500 trials. Every saved candidate has a source
DAG, grammar, formula rows, bundle, and normalized transition table. Every
emitted decision edge is re-extracted and compared. All ten table hashes and
all 50 words were reproduced by the portable replay. These controls have no
claimed complete binary-runtime or ZFC-calibration theorem, and none improves
its own 269-state control.

The bundle's eight syntactic double-negation cancellations concern the
specific Boolean layout used here. They are not the previous six-redex
layout, and not the new numeric negation-constructor identity.

## Equality-free consistency comparison

`equality_erasure.tex` and the corresponding subsection of
`theory_exploration.tex` complete the two-sided observational-profile idea
already mentioned in the repository's `logical_engine_completeness.md`.
There is no priority claim for that equality-erasure idea.

Define two objects equivalent when both their incoming and outgoing
membership profiles agree. Pure equality-free first-order logic makes this
an equivalence and a congruence in both membership slots. Quotienting a model
of **full** equality-free CP/GIC/IR by that equivalence produces a model of
the full equality-bearing native theory. Every equality-bearing GIC matrix
translates to an equality-free GIC matrix, including parameters and coincident
values. The reverse consistency implication is inclusion. An explicit
recursive formula translation describes primitive-recursive proof maps;
this packet does not include a serialized proof object or new Lean theorem.

This comparison does not justify removing equality rows from the current
numerical engine. Those rows support cross-variable instantiation, and the
repository already supplies typed countermodels to the naive deletion.
A new complete equality-free proof-search compiler still needs to be built
and measured. The current identity avoids that new calibration burden.

## Files and attribution

- `fine_source_ast.json` is the compact complete AST and original AX word
  extracted from the supplied routed-source input. `negation_ast.json` is
  the actual token AST excerpt; the runner checks their agreement.
- `source_variant_inputs.json` freezes the additional source pairs and
  records hashes of their generating files.
- `church-results/` holds the ten compiled controls, their grammar/source
  descriptions, hashes, measurements, and all 50 fine words.
- `vendor/` contains unchanged attributed emitters, compiler helpers, the
  published source DAG/specification, and Andrew James Wade's MIT-0 backend.
  `vendor_sources.json` records every copied file's origin and content hash.
- `vendor/LICENSE.ProveIt` and `vendor/snapshot/ZF/generator/LICENSE.wade`
  preserve the source licenses. The specialized emitter is attributed to
  the supplied `sub246-audit-and-alternatives` research packet.
- The three proof sections are ordinary LaTeX fragments for the main report.
  `theory_exploration.tex` already includes the equality-erasure section, so
  a wrapper should not input `equality_erasure.tex` again.

Historical source paths in metadata identify the input used during research;
no replay script reads from those paths. Source-level termination and
equivalence, grammar correctness, a literal binary runtime, blank-tape
initialization, and internalized consistency calibration remain different
claims. The larger archive states which are established for each machine.

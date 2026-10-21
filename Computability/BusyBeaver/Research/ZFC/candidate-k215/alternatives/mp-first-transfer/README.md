# T215: new enumeration, one-head credit, and a quantifier-calculus reduction

## Result

This packet supplies an exact **215-working-state, two-symbol, blank-tape**
Turing machine, with a separate halt state and all initialization included.
Using the explicitly inherited ProveIt numerical-calculus calibration, the
ordinary proof establishes, by reasoning formalizable in ZFC,

> ZFC proves: T215 does not halt on blank tape if and only if Con(ZFC).

**No sound 214-state construction is claimed.** No new Lean/Rocq endpoint has
been compiled. The main result uses the user's alternative target: a materially
different, completely checked 215-state implementation.

Read `report/report.pdf` for the full argument; all LaTeX sources are beside it.
The full dense transition table is both in the PDF appendix and in
`machine/t215.tm`. That table starts at state 0, uses working states 0..214,
and halts at 215. `machine/t215.native.tm` preserves the construction labels:
start 0, dispatcher 84, halt 254. `machine/canonicalization.json` gives the bijection.

## What changed

The earlier transfer machine assigned S=0 and MP=1. The primary machine here
assigns **MP=0, S=1, AX tags>=2**. Two closed source bodies are exchanged and
eight literal transition rows change. This changes the meanings of candidate
numbers and the exact transition graph. It is not a state renaming or global
reflection of any of 47 distinct prior 215 tables checked (23 rooted graphs).

A new diagonal argument proves a **one-head** conservative stack-credit bound
from candidate cutoff 1, versus two for the earlier ordering. The initialized
AX computation supplies ten theorem heads, leaving margin 9. “Exact one-head”
refers to accounting which ignores successful-MP truth pushes; it does not
claim minimal necessary credit for every semantic run.

The transfer itself is inherited: `DROP;NIP;NIP`, with 78 primitive occurrences.
Its exact semantics has **both** guards, incoming top=1 or incoming cache=1.
The report explicitly corrects the earlier single-guard description. The old
strong compiler remains valid because an earlier falsity halt is an allowed
success and every nonhalting output is unchanged.

| Primary candidate fact | Value |
|---|---:|
| Working states / transition rows | 215 / 430 |
| Primitive source occurrences | 4,775 |
| Distinct source subtrees | 201 |
| Maximum source depth / zero run | 44 / 6 |
| Arbitrary-natural guarded runtime cases | 6,209 |
| Symbolic proof-rule applications | 1,610,781 |
| Covered transition rows | 430 |
| Minimum duration constant | 10 |
| Blank transitions to exact matched frame | 68,442 |
| Synthetic AX prefix primitive steps | 174 |
| Conservative initial credit / supplied credit | 1 / 10 |

The main native table SHA-256 is
`485ca26885508bdaf76ecd8f46827b64518ca1d9e32de81b2a8ac2904a49d9f2`.
The source SHA-256 is
`8ddb942f0f1d8e2e3b12ab7217c7232eb553cd288fca38dbf9b0eded73893dd5`.
The dense table SHA-256 is
`6aa05045c7a2dd8fa5b4626f12ea39f3a13240532a2e01a2eccb01e65e2b3ab6`.

## A new logical reduction

Only one orientation of quantifier commutation is needed per unordered pair
of distinct numerical binder labels. Keeping rho4(a,b,X) for a<b recovers the
opposite orientation at its **exact native code**, using normality, rho6,
classical implication, and theorem-only generalization. Thus all theorem
codes, including the gated set-theory bundle, are preserved.

`formalism/ordered_commutation_dag.json` is a 600-node finite Hilbert
certificate. An independently implemented reader checks 488 output-dependency
nodes, five closed generalizations, and exactly one permitted orientation
instance, at matrix `not(Box_b(Box_a X))`. No opposite commutation axiom or
constructor-injectivity assumption is used. This is a logical interface for
optimization; it has not yet reduced the binary state count. Restricting the
parameters of the entire AX macro to a<=b would be unjustified.

## Research candidates and exact failure boundaries

* A direct 35-primitive transfer source has 201 subtrees, but its initial 215
  physical allocation decrements the wrong register in a concrete context.
  The exact 634-step counterexample is retained.
* A new scratch-biased short-transfer variant has a valid 215-state physical
  implementation and a complete 6,152-case runtime proof. Its inserted scratch
  increment changes parsing and candidate-counter advancement. Cofinality and
  protected-credit analysis remain open; **it is not a calibrated consistency
  machine in this packet**. See `research/short-transfer` and the report.
* The old 214 runtime fold has certified blank-start failures. Both spare
  policies and all 856 one-bit configurations relevant to adding a single
  initializer have exact finite halt/ray classifications. This has a narrow
  unchanged-core scope, not a general214-state impossibility claim.
* A maximum-zero-run-five source with 206 subtrees preserves the exact guarded
  control-flow graph. Its extra source nodes do not yield a net physical saving.
* The primary table's bounded local search examined 46,010 ordered state pairs
  and 629,160 rewrite specifications, radius 5/fuel 97, without a fold. Its exact
  search family and rejection digest are included. This is not an optimality
  theorem.

## Reproduce

Use Python 3.10 or later, standard library only, with assertions enabled.
From this packet's root:

```sh
python3 -B verify.py
python3 -B verify.py --runtime --out /a/new/output/directory
```

The default checks the manifest; reconstructs the source and table; checks two
independent source control-flow resolvers and the closed-body transports;
checks native/dense state renaming; replays blank startup in two independent
tape representations and dense/native lockstep; matches the entire source AX
prefix; audits the stored runtime census; reruns the mathematical certificates;
and verifies the binary comparison and negative-control evidence.

`--runtime` additionally derives every arbitrary-natural guarded primitive
case afresh from the exact transition rows. It compares every resulting case
summary with the stored census and retains per-case row coverage. The complete
replay performed for this packet took about 114 seconds on the build host;
that time is not a mathematical assumption. The source/runtime theorem is an
executable symbolic induction argument, not a finite register-value test.

The mathematical and binary checks can be run separately:

```sh
python3 -B code/check_mathematics.py --out /tmp/math-audit.json
python3 -B code/check_binary_evidence.py --out /tmp/binary-audit.json
```

Build the PDF with a standard TeX Live installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

A third pass may be needed if the table of contents changes. Compilation writes
TeX auxiliary files; these are intentionally omitted from the deliverable.

## Proof dependencies and scope

The base repository snapshot is
`ead95b5b336818a53c89b8c3d5249822e0570939`:
https://github.com/VladimirReshetnikov/ProveIt/tree/ead95b5b336818a53c89b8c3d5249822e0570939/Computability/BusyBeaver/Research/ZFC

The full earlier transfer packet is preserved in `reference/transfer-parent`,
including its source, literal machine, independent runtime verifier, fixed
3,728-node dominated-rho8 certificate, proof reviews, licenses, and provenance.
The accepted K215 and dominated-rho8 proof documents are also retained.
The ultimate equiconsistency with ZFC is the identified inherited theorem;
this packet does not reprove the full set-theoretic interpretation in a proof
assistant. The new source translation, scheduler proof, exact-table runtime,
and blank connection close the new candidate relative to that calibration.

`STATUS.json` separates completed assertions, inherited dependencies, and open
research. `MANIFEST.json` binds every delivered file except itself to exact
bytes. New verification writes receipts to a fresh output directory; it does
not alter the archived evidence.

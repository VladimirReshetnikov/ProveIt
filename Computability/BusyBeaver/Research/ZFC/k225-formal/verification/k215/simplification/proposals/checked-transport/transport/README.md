# Concrete Context215 transport

This directory contains a new checked concrete proof for the existing five-row
Context215 retargeting. The machine itself and its ordinary six-block proof
were already present in ProveIt/incoming work; they are not claimed as new.

`NativeContext.v` proves, on two infinite binary streams and a scanned bit,

```coq
context_halts_iff l b r :
  halts old (C 0 l b r) <-> halts new (C 0 l b r).
```

It uses an invariant at seven old controls. A kernel-checked filter reduces
its nontrivial preservation obligations to eleven incoming rows. A transient
relation preserves the entire tape and head position and matches each old
step by one or three new steps. Iteration gives `n <= m <= 3*n`. Positivity,
terminal persistence and halt reflection establish the reverse implication
without a separate reverse simulation. The sharper ordinary two-to-one
block-clock bound is not claimed as a theorem of this file.

`LiteralBindings.v` binds `new` to a literal 430-row table, proves the same
all-tape and blank halting equivalences for `literal_new`, and checks the
215 working controls, 430 rows, unchanged working-label list, and closed
target set. `generate_tables.py --check` separately checks literal rows
against the supplied native bytes, exact SHA-256 values, full binary domains,
and the five retargetings. Without `--check`, it emits the corresponding Coq
literal list. This byte audit is separate from kernel theorem checking.

Native start is 0; the terminal control 254 is not counted among the 215
working controls. Missing rows stutter in this native semantics. The actual
repository's BusyCoq semantics treats missing rows as halting. The adjoining
`adapter/` component discharges active-domain closure and translates between
these conventions. Its state map is 301→102, 302→120, 254→230, identity
otherwise. Do not bypass that semantic obligation when attaching an endpoint.

## Reproduction

The standalone native core can be built with Coq 8.18.0:

```sh
coqc NativeContext.v
coqc LiteralBindings.v
coqchk -silent LiteralBindings
python3 generate_tables.py --check
```

Prefer the complete minimal fresh build from the archive root, which also
checks the exact repository adapter and all its dependencies:

```sh
python3 adapter/build.py --native-dir transport --out /tmp/context-check
```

Use an empty output directory. The archive root reproduction driver runs this
and the scheduler proof in separate fresh directories. No full ZFC dependency
closure or Lean build is performed by this minimal command.

The native and literal compilation logs in `verification/` record two and
three closed theorem-level assumption reports respectively. The adapter's
final receipt and recursive `coqchk` add the semantic endpoint checks. There
are no custom axioms or admitted proof obligations in the new transport code.

## Input provenance

Baseline: ProveIt `aa66d0a33f1f8237a348899eb8095b045a502832`.
The exact `old.tm`, `new.tm` and `patch.json` are copied from the
`Affine_Proof_Cores_and_Transport_2026-10-21` incoming contribution's concrete
Context215 instance. The native bytes match the existing primary and
context-return candidate artifacts. Their hashes are printed in the report
and audit receipt. The patch data and underlying machines remain attributed
to their original contributors; this directory adds the concrete proof and
literal-binding checks. See the root `NOTICE.md` and `LICENSE`.

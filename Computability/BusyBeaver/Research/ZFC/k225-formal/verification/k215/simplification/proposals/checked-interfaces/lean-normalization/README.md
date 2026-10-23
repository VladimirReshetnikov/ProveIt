# Normalize subtype operations before transporting witnesses

This is a checked, detached proof-only patch for the current
`BusyBeaver.ZFC.ConstructibleAbs` module at ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

The patch rewrites five proof bodies: `functional_iff`, `isFunctionOn_iff`,
`isEnvOn_iff`, `atom_clause`, and `bin_clause`. It adds no import, declaration,
helper, premise, or global simplifier attribute. All existing public theorem
statements and section directives remain intact.

| Whole-file measure | Baseline | Proposal | Reduction |
|---|---:|---:|---:|
| UTF-8 source bytes | 50,827 | 49,991 | 836 |
| Source lines | 917 | 911 | 6 |

These are source measurements, not proof-term sizes or a compilation-speed claim.
The paired local module checks took 0.938 seconds and 1.009 seconds respectively;
that single observation supplies no evidence of a speedup.

## What changes mathematically

The underlying arguments are unchanged. Before introducing quantified witnesses,
the proof uses an explicit `simp only` list to transport the relevant operations
and equalities to the ambient model. For example, `val_kpair`, `val_natV`,
`val_vbit`, and `Subtype.ext_iff` remove repeated conversions between a subtype
statement and its ambient equivalent. After that normalization, both sides use
the same predicate. Only the witness support remains: a component of a
constructible pair or satisfaction triple is constructible by transitivity.

In `bin_clause`, two existing closure facts provide the four subtype witnesses.
The resulting tuple carries the entire unchanged conjunction `h`; the proof no
longer separately transports each conjunct in both directions. The guard in
`atom_clause` is preserved: the equivalence `hQ i j` is used only after the two
omega-membership hypotheses have been obtained.

This is a useful local discipline, not a claim that arbitrary unbounded formulas
are absolute. In particular, do not replace `code_up` and `code_down` by an
ordinary external formula induction. Their represented formula codes may be
nonstandard; the existing internal rank argument has a different obligation.

## Verification completed here

`evidence/result.json` records a fresh Lean 4.32.0 replay with 25 successful
invocations: 21 unchanged dependency modules, the original module, its API client,
the modified module, and the identical API client. The six complete public type
and axiom reports are byte-for-byte identical. They cover the five changed
theorems and the downstream theorem `vEqL`; every report lists exactly
`propext`, `Classical.choice`, and `Quot.sound`. Both module logs and both API logs
have zero warnings and zero errors. The patch also passes `git apply --check`.

The whole modified module is checked, including its unchanged downstream proofs.
The complete K215 endpoint and its other descendants were not rebuilt in this
pilot. Integrating this patch still requires the project's normal affected-client
and endpoint gates. This contribution makes no machine-size or internal PA/ZFC
derivation claim.

## Reproduce

From this directory, with Python 3.11 or newer and Lean 4.32.0:

```sh
python3 reproduce.py --repo /path/to/ProveIt --lean /path/to/lean --out /new/output/directory
```

The script verifies every source digest in `sources.json`, uses a fresh output
directory, compiles the exact listed modules, and compares the complete public
type/axiom reports. It writes only under `--out`; the checkout is never edited.
The proposed source is supplied for review and replay; `normalize-first.patch`
is the integration artifact. Compiled objects are not included in this packet.

## A rejected abstraction experiment

Two abstract guarded-subtype quantifier lemmas were proved without axioms in an
initial isolated experiment. Using them in three selected current proofs saved
272 bytes in the target file but introduced a 1,176-byte helper, for a net growth
of 904 bytes. That version was rejected as a source-shortening proposal. The
accepted patch uses only existing facts. This comparison illustrates why new
abstraction overhead must be counted rather than measuring just the edited
callers.

One later editing attempt accidentally removed the existing `omit he in`
directive before `bin_clause`, adding an unintended section argument and breaking
three calls. Its failed source and log remain under `history/failed-omit-directive`.
Restoring the original directive repaired the edit. That failed attempt is not
part of the accepted compilation evidence.

The existing mathematical construction and formalization retain the attribution
and licensing notices in the source and repository. This contribution changes
only the five indicated proof bodies.

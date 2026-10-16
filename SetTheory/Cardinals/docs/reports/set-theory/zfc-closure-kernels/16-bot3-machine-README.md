# Exact-word compiler measurements for a small consistency machine

**These are reproducible experiments, not proved ZFC-consistency machines.**

The new measurements retain the original rho6 logical schema and optimize a
fixed register-program macro word. They produce a 250-state relative-falsity
table and a 251-state table using a new genuine-Bottom ternary codec. A separate
PSC control reaches 252 states with that codec. Each delivered numeric machine
is total on its working states, has two symbols, and starts on a blank tape.
The necessary interpretation of its non-halting as Con(ZFC) remains unproved.

## Run the fixed winners

Python 3.10 or later is sufficient. No third-party Python package, network,
Lean, Coq, or random search is needed for the default replay.

```sh
python reproduce.py --output reproduced
```

The command verifies all 12 pinned input files, reconstructs the three winning
named tables, checks their exact hashes, creates total numbered tables, and
independently parses both representations to compare every transition. It also
executes the generic quantifier-calculus counterinterpretation. Output stays
outside `proveit_snapshot/`, which is read only.

The checked output is already in `tables/`. The terminal state is numbered by
the working-state count and has no outgoing rows. It is excluded from the count.

| Output stem | Logical source | Codec | States | Total rows |
|---|---|---|---:|---:|
| `cgv-relative-bottom-250` | C/G/V, original rho6 | Imp=3P, Rel=3P+1, All=3P+2 | 250 | 500 |
| `cgv-genuine-bottom3-251` | Same C/G/V word, original rho6 | Truth=0, Bottom=1, Imp=3P, Rel=3P+4, All=3P+2 | 251 | 502 |
| `psc-genuine-bottom3-252` | PSC control, original rho6 | The new genuine-Bottom ternary codec | 252 | 504 |

Each stem has `.named.tm`, `.tm`, and `.labels.json` files. The two parsers check
499, 501, and 503 original rows respectively, together with the one added
tape-preserving halt row. All working states are graph-reachable. Graph
reachability does not assert that every state is visited from the blank tape.

## New measurement and its scope

The repository's old-rho6 C/G/V control first reproduces **254 = 192+62** states,
where 192 are decision states and 62 are framework states. The fixed emitted
word contains 138 macro calls and orders the logical rows as rho8, rho2, rho4,
original rho6; the gated bundle is `V AND (C AND G)`.

An exact-word grammar built by weighted Re-Pair, seed 7 and exponent 4, reduces
that measurement to **250 = 188+62** states. No logical row, predicate, gate,
variable read, constructor call, or cleanup action is deleted or moved. The
search changes the sharing and association of contiguous macro subsequences.
The final seed-7 grammar has 19 rules and 67 residual tokens. Its full expansion
equals the original 138-token word both before and after backend sharing.
Every one of the 19 named macro roots has zero escaping break/continue levels.

The first 200 seeds find eight 250-state grammars. A further 2,000 seeds, numbered
200 through 2199, find another 120. No member of those 2,200 samples has fewer
than 250 states. This is a measured minimum in the sampled family; it is not a
lower bound for other grammars or other machines. The deterministic seed-7
winner is supplied rather than depending on rerunning the whole search.

The new ternary codec changes only the membership constructor from +1 to +4.
The existing add-four helper is reused; the extra reachable helper state makes
the C/G/V table **251 = 189+62**. The target constant remains code 1, the formula
multiplier remains three, and the proof/stack Cantor pairing is unchanged.
All 225 small register-constructor contract cases pass for each genuine-Bottom
winner. The separately documented mathematical codec argument is stronger
than those finite tests, but neither one proves the entire machine simulation.

The PSC control reaches **252 = 190+62**, seed 93. It has the same measured count
as the repository's four-tag primitive-Bottom PSC control. Its benefit is a
genuine Bottom with a three-residue numerical representation. It inherits the
PSC control's incomplete quantifier calculus and is not a calibrated result.

## Why exact-word sharing is a conservative source transformation

Regard each closed macro as a partial transformation of register configurations,
allowing divergence or halting. Concatenation is composition. An acyclic
straight-line grammar denotes its expanded word, by induction on its rules.
Consequently two grammars with exactly the same expanded word have the same
register-level behavior. The closed-macro requirement prevents reassociation
from changing the meaning of break/continue levels outside a macro.

The executable experiment checks the finite premises: word equality and the
escape bounds. A complete Lean proof must still connect those checks, the
source macro semantics, the Wade compiler, its initialization, and the literal
machine. This experiment does not supply that theorem. In particular, a source
rewrite can preserve an uncalibrated source program perfectly without making
its consistency strength known.

## Totalization and exact correspondence

The Wade output has one missing binary row, `1.inc/read1`, under its convention
that undefined transitions halt. The normalizer supplies `write1, R, halt`,
keeping the tape unchanged and adding no working state. Start is numbered 0,
remaining working names are sorted lexicographically, and halt is numbered last.

The independent correspondence check compares every original write, direction,
and target after this bijective relabelling and verifies the unique added row.
Thus the numeric table and its named source agree until termination; only the
final head position can differ on the previously undefined transition. Under
the attempted-step partial semantics, states and tapes agree at every time.
This is sufficient to preserve halting and the final tape, without a sampled
blank run. No bounded simulation is offered as evidence of non-halting.

## Logical limitations

The inherited C/G/V presentation still needs an actual proof-calculus
calibration, the parameter/binder coverage argument, and an enumerator theorem.
The 250-state version retains relative falsity `Rel(0,0)` and its associated
semantic obligations. The 251-state version removes that coding alias but does
not automatically repair missing substitution or establish first-order
completeness. Both retain original rho6, avoiding the particular generic
dual-rho6 replacement error documented at the pinned head.

`quantifier_obstruction.py` proves a further generic diagnostic. Interpret
every universal-quantifier operator as identity, implication materially,
Bottom as false, and differently labelled membership atoms independently.
This validates rho8, original rho6, the dual, quantifier distribution,
commutation, atomic vacuity, same-variable specialization, and explicit
explosion. MP and GEN preserve validity. Yet assigning `Rel(0,1)=true` and
`Rel(2,1)=false` refutes

```text
All(0,Rel(0,1)) -> Rel(2,1).
```

That formula is an ordinary first-order validity. Therefore adding
same-variable specialization and explosion alone does not make this reduced
logical skeleton complete. The missing cross-variable substitution/renaming
bridge must be proved or implemented. This counterinterpretation is not
asserted to satisfy the additional C/G or PSC theory rows. It is not a
countermodel to those theories, and it proves no non-halting statement about
any supplied machine.

## Optional search reproduction

The historical first 200 seeds and the additional 2,000 seeds are preserved in
`evidence/`. They can be rerun independently:

```sh
python old_rho6_grammar_search.py --repo proveit_snapshot --output search200 --seeds 200
python old_rho6_grammar_search.py --repo proveit_snapshot --output search2000 --start-seed 200 --seeds 2000
python bottom3_measurement.py --repo proveit_snapshot --output bottom3_search200 --seeds 200
```

`snapshot-sha256.json` lists exact input hashes. The result JSON files pin the
search scripts and source programs; they explicitly record that theory
calibration, compiler verification, and a new ZFC state bound are not claimed.

## Provenance and notices

The ProveIt snapshot is pinned at
`96836f9eea3540e96322c3d28c7127a582aae223`:

- [Research/ZFC](https://github.com/VladimirReshetnikov/ProveIt/tree/96836f9eea3540e96322c3d28c7127a582aae223/Computability/BusyBeaver/Research/ZFC).
- [Old-rho6 repair measurements](https://github.com/VladimirReshetnikov/ProveIt/blob/96836f9eea3540e96322c3d28c7127a582aae223/Computability/BusyBeaver/Research/ZFC/dual_quantifier_gap.md).
- [PSC component experiment](https://github.com/VladimirReshetnikov/ProveIt/blob/96836f9eea3540e96322c3d28c7127a582aae223/Computability/BusyBeaver/Research/ZFC/psc_backend_experiment.md).
- [Imported benchmark attribution and license boundary](https://github.com/VladimirReshetnikov/ProveIt/blob/96836f9eea3540e96322c3d28c7127a582aae223/lib/jeff-busy-beaver-zfc254/README.proveit.md).

Mira-Cult designed the published machine and register program; Jeff supplies
the pinned verification snapshot at `297ab8df7e5de329605c3875b4934643b371a5e3`.
Andrew James Wade supplies the public backend under the retained MIT-0
`LICENSE.wade`. The six ProveIt research modules use its MIT-0 grant. The new
scripts in this deliverable are provided under that same MIT-0 form.

The upstream-wide busy-beaver repository has no declared blanket license in
the imported snapshot. The two necessary unchanged specification/DAG reference
inputs remain attributed upstream material; no new license is asserted for
them. The retained `notices/upstream-provenance.md` describes that boundary.
This subset preserves exactly the inputs needed to reproduce the experiment;
it is not the full Coq verification package.

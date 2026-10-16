# Closed-helper grammar comparison for the complete original program

This supplementary experiment matches the already known **269-state public-
backend control**. It establishes no new state record and no ZFC theorem about
the generated binary table. Its useful result is a separate exact recipe that
prices helper reuse explicitly while preserving all original theory and logic.

## Replay

Python 3.10 or later and the included files suffice. No network or proof assistant
is required. Run with assertions enabled:

```sh
python library_grammar.py --output reproduced
python vendor/verify_rm_certificate.py \
  --source upstream/ZF/m254/coq/prog/Dag254.v \
  --candidate reproduced/candidate_dag.json \
  --certificate reproduced/rm_bisimulation.json
```

The first command executes one fixed recipe; it does not rerun a random search.
The candidate contains 207 register-decision nodes and the unchanged Wade
framework contributes 62 binary states. There are 537 explicit named rows; the
total numbered table has 538 rows. Its only normalization fills the absent
`1.inc/read1` row with write 1, move right, halt. This is the usual conversion
from undefined-transition halting and adds no operational state.

The total table SHA-256 is
`5473038a3a07ab73677229208a91fc6e4bc4062603710f9ed48410bc784c522c`.
This is a new *comparison-table serialization*, not a newly proved consistency
machine. It is distinct from the prior source-08 table with the same state count.

## What changes and what is checked

The original 186-call AX word, its equality rows, original rho6, CP/GIC bundle,
gates, four-tag coding, proof enumerator and register instructions are retained.
Three constructor macros are expanded at interfaces with no escaping control
effects: `wal` (universal quantifier), `wel` (membership), and `weq` (equality).
Their exact 229-token expansion is compressed using adjacent-pair substitutions.
An already present helper pair costs no additional decision node. New pairs
cost one. The residual is right-associated. The winning recipe uses exponent
4 and seed 0; the label `quantifier` in the JSON denotes this three-constructor
expansion family.

The inherited independent verifier checks an operation-site bisimulation from
the actual 219-node pinned program to the resulting 207-node program. It checks
4,533 related pairs, including both decrement exits, with 2,601 increment labels,
1,931 decrement labels and one halt label. It uses separate string/integer
path arithmetic and does not import the generator or the Wade backend. Emitted
decision edges are independently inverted by the inherited source helper.

These finite premises establish the stated register-program correspondence
under the documented RM semantics. They do not establish the binary compiler,
blank initialization, the ZFC proof predicate, or an internal ZFC equivalence.
No Lean or Coq build was performed for this experiment.

## Search evidence and its limits

An initial 960 executions covered eight expansion families, three exponents and
40 seeds. A targeted continuation covered the two promising constructor and
variable families with three exponents and 1,000 seeds each. This totals 6,960
executions and 6,720 distinct family/exponent/seed choices because the first 40
seeds overlap. No result improves the pre-existing 269-state control.
`evidence/search_results.json` records the 6,000-case continuation. The fixed
replay uses only its winning recipe and has its own `evidence/results.json`.
No minimum beyond these samples, and no lower bound for other machines, follows.

The complete continuation is optional:

```sh
python library_grammar.py --search --seeds 1000 \
  --families quantifier,variables --output search
```

## Attribution and source boundaries

The new `library_grammar.py` adapts the weighted Re-Pair and exact operation-
correspondence infrastructure of the earlier source-08 report. The unchanged
`vendor/rebracket_axioms.py` and `vendor/verify_rm_certificate.py` are those
earlier helpers, not new work here. Their original notice is retained in
`vendor/ORIGINAL_NOTICE.txt` (its paths describe its original archive).

The three root-level ProveIt helper files were retrieved from the user-selected
repository at commit `5e5603303de0815c59a792763704bb00589fed99`; their original
MIT-0 license is retained. They read the small attributed upstream input subset
at `297ab8df7e5de329605c3875b4934643b371a5e3`. The upstream source SHA-256 checks
are enforced by the original helpers.

Mira-Cult designed the original machine, register program, proof calculus and
nonextensional theory. Jeff published the verification and numeric DAG. Andrew
James Wade wrote the public binary backend under the retained `LICENSE.wade`.
There is no blanket upstream license; the two small unchanged DAG/specification
inputs retain their attribution and are not assigned a new license here.
`UPSTREAM_PROVENANCE.md` retains the repository's complete import notice.

The source-08 helper origin is the archive introduced at commit
`39409c8c921cccdbd6162c8767c84cfb7df65df1`, later preserved in the maintained
closure-kernel report and the `5e560330` incoming report. This package contains
only the inputs for this comparison and is not a Coq verification source bundle.

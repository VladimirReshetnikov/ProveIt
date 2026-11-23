# Executable reference constructions

Run `python3 validate.py` from this directory. Python 3.10 or later is enough;
there are no third-party dependencies. The test writes
`validation_results.json` and prints its complete summary.

`proplogic.py` contains:

- finite propositional syntax, evaluation, substitution and truth tables;
- canonical DNF/CNF;
- replayable resolution saturation certificates and a proof checker;
- a deterministic bounded splitting SAT solver;
- definitional Tseitin CNF with extension/projection witnesses;
- Boolean forgetting and Craig interpolation;
- an explicit IPC/CPC natural-deduction DAG checker;
- finite Kripke models and forcing;
- finite relative IPC consequence saturation, with a checked derivation DAG
  for every accepted sequent, and all finite prime theories as a canonical
  Kripke countermodel structure.

Formula variables are numbered from zero. Clause literals use `i+1` for the
positive variable `p_i` and `-(i+1)` for its negative literal, so signed zero
never occurs. A clause is a `frozenset` of literals and a CNF is a `frozenset`
of clauses. An empty clause is false; an empty CNF is true. Empty normal-form
folds and zero-variable formula cases are included in the checks.

The `Formula` datatype is an AST. Lists, dictionaries and sets are convenient
reference representations. The report and Lean formalization plan specify
how to replace these by natural-number codes and bounded PR loops. Python
termination alone is not a proof of primitive recursiveness, and these checks
are not proofs in iPRA.

## Validation coverage

The checked-in JSON records the actual run, including interpreter version.
The exhaustive universe is every formula with at most five AST nodes over
`bot,p0,p1` (516 formulas). The CNF universe is all 512 subsets of the nine
non-tautological clauses over two variables. Additional targeted tests cover
Peirce's law, double-negation elimination, weak excluded middle, double-negated
excluded middle, an intuitionistic distributivity theorem, and contexts with
assumptions. Every saturated IPC proof DAG is replayed by the independent
checker, and every canonical model satisfies the full finite truth lemma on
its formula universe.

A regression evaluates the article's printed formula
`p -> ((q or r) -> (r -> not p))` at `p=true,q=false,r=true` and confirms that
it is false. The checker also rejects a CPC LEM step when run in IPC mode.

These finite tests detect implementation mistakes and validate representative
proof constructions. They cannot establish universal correctness; the human
proofs supply that argument, and object-level Lean verification remains work
to be completed.

## Representation correspondence

The report's numeric formula codes use `bot=0`, `var(i)=5*i+1` and binary
constructor codes `5*((a+b)^2+a)+tag` with tags 2, 3 and 4. The Python module
uses dataclasses instead, so no claim is made that its objects are those
numeric codes. Its mathematical constructors and semantics agree exactly
with that grammar; `FormalizationPlan.md` specifies the arithmetization.

The report presents list contexts. The executable kernel uses finite sets:
exchange, weakening and contraction identify the corresponding contexts.
The report proves these structural transformations, so a checked set-context
proof can be expanded to a list-context proof. `weak` and `cut` are explicit
accepted derived rules in this reference checker and must be expanded when
exporting to the report's base rule list. `check_nd` checks every node of a
DAG, while `check_nd_conclusion` additionally checks a specified nonempty
proof target and its exact context.

The report permits synchronous saturation rounds. Python uses sequential
in-place scans; each new witness refers only to earlier DAG nodes. This
computes the same least closure. Every nonstable scan adds a previously
absent sequent, so the report's finite ascending-measure bound still applies.
The Kripke checker explicitly rejects an empty frame.

## Complete proof-or-counterexample API

```python
from proplogic import *
p = Var(0)
ipc = decide_ipc((), Or(p, Not(p)))
assert ipc.kind == "countermodel" and ipc.world == 0
assert check_ipc_result(ipc)

cpc = truth_table_prove((), Or(p, Not(p)))
assert cpc.kind == "proof"
assert check_cpc_result(cpc)
assert not check_nd(cpc.proof, classical=False)
```

A `ProofResult` has `context`, `goal`, `proof`, `root`, and a `logic` tag.
The proof is pruned to the ancestors of the final root. An
`IPCCountermodelResult` has a nonempty rooted `model` and a designated
`world`; the exported root is always zero. A
`BooleanCountervaluationResult` contains an explicit Boolean valuation.
The result checkers validate the requested sequent, not just the syntax of
the underlying object.

`result_data` and `result_from_data` convert certificates to and from JSON
compatible data. Invalid serialized syntax may raise an error during
parsing; parsed certificates must still pass the appropriate result checker.
`python3 demo.py` writes four complete examples to `demo_certificates.json`
and replays each imported certificate. The validation suite exercises full
serialization round trips for every one of the 551 exported sequents in each
logic. The printed article counterexample is obtained by the public CPC
constructor, as well as checked directly at the stated valuation.

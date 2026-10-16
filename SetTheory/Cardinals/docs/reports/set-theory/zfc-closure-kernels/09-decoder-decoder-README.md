# Certified decoder reduction

Run the independent checker with an ordinary Python 3 installation:

```sh
python verify.py
```

The checker uses only the standard library and the three supplied JSON
inputs. It verifies both directions of a finite bisimulation between the
baseline 203-node register-program DAG and the candidate 202-node DAG.
The result applies to every initial register file. The 2,985-entry
certificate compares both branches of every related decrement test and
the exact increment counts between tests; it is not a bounded simulation
of small register values.

## Files

- `baseline_dag.json`: exact structural sharing of the frozen `p254` tree.
- `candidate_dag.json`: the 202-node register-program candidate.
- `bisimulation_certificate.json`: all 2,985 test-site pairs and successors.
- `verify.py`: independent integer-PC checker.
- `verification_results.json`: the executed checker output, including hashes.
- `search_results.json`: deterministic constrained search parameters/results.
- `repair_search_results.json`: unsuccessful randomized RePair experiment.
- `rejected_zero_run_dag.json` and `rejected_zero_run_results.json`: the
  mathematically equivalent 200-node negative control whose maximum PC
  zero run of fifteen violates the unchanged dispatcher's intended format.
- `rejected_zero8_results.json`: compact metadata for a 201-node candidate
  whose register-program certificate passed but whose literal-table audit
  did not pass. No validated machine is claimed for that candidate.
- `machine_emission_results.json`: the measured 267-state emission and its
  subsequent reduction to 256 working states, with both verification scopes
  stated explicitly.
- `search/`: the deterministic mutation search and source-literal parser.

The source baseline is `ZF/m254/coq/tm/Prog254.v` from the pinned
`lib/jeff-busy-beaver-zfc254` import in ProveIt. It stores 6,459 internal
tree nodes and 6,460 leaves; sharing equal subtrees gives the supplied
203-node DAG. Both representations have exactly the same path semantics.

## Turing-machine status

The 202-node candidate has depth 35 and maximum zero run seven. Its first
literal-table emission was independently audited on all 8,391 instruction
cases and its original 264,982-step blank-tape boot. After state pruning
that emission has 267 working states. Eleven combined contextual folds then
reduced the count to 256; all 8,391 cases and the same complete blank-tape
boot passed again. Thus a smaller register-program DAG did not by itself
improve the 254-state Turing-machine record. The separate machine audit
directory contains the literal tables, folds, and verification scripts.

The relaxed 201-node candidate has depth 52 and maximum zero run eight.
Its register-program certificate passed, but the emitted table failed
38 of the 8,391 affine cases, including two protected-box violations and
36 checker-fuel failures. These failures reject the proposed bridge; a fuel
failure alone is not a proof that the Turing machine behaves incorrectly.

## Reproducing the search

The supplied frozen certificate can be checked without any checkout.
To reproduce the search, set `PROVEIT_ZFC254_ROOT` to the pinned source
directory ending in `ZF/m254`, then run:

```sh
python search/rotate_search.py --iterations 10000 --restarts 10 --maxzeros 7 --maxdepth 58 --seed 254 --suffix reproduced
```

The parser checks the SHA-256 of `coq/tm/Prog254.v` before reading it.
The output candidate and search metadata are written beside the search
script. This is the same search algorithm, iteration count, and seed as
the supplied `search_results.json`; elapsed time is machine dependent.

No new Lean or Coq kernel proof is claimed for these generated artifacts.
The mathematical finite-certificate argument is documented in the report;
the executable checker is an independent audit of its finite hypotheses.

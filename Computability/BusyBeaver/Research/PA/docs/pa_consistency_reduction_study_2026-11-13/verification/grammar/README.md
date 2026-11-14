# Independent check of the finite grammar witness

Run:

```sh
python3 verify_grammar.py
```

The verifier uses only Python's standard library and its checks remain active with `python -O`. Both JSON inputs are included, so this directory can be copied into the release unchanged.

It independently expands the `productions` dictionary in `min_grammar_result.json` and compares every token with the pinned primary PA194 AX macro word. The reference file's SHA-256 is embedded in the verifier. As in the optimization instance, the free macros `node60` and `node61` expand to two and four copies of `inc 1`, respectively. Other fixed source macros remain atomic.

The fresh check establishes:

- Both dictionaries are acyclic and every defined nonterminal is reachable from its root.
- Every nonterminal is defined, all primitive/macro tokens belong to the specified alphabet, and JSON object keys are unique.
- The witness's 25 productions expand to exactly the reference's 190-token macro word.
- The exact integer sum `sum(len(rhs) - 1)` is 67.

The stored `checked_receipt.json` is the output of the fresh run. The verifier ignores the optimizer's floating-point objective, bound, gap and elapsed-time fields. **This is a feasible-witness check, not an optimality proof or an exact lower-bound certificate.** It also does not establish source control-flow equivalence, scanner bounds, state folds, blank initialization or TM correctness for a binary association of the witness.

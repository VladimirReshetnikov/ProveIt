Portable replay: python3 -B verify_invariant.py --threshold 16 --output replay
Compare replay/source_abstract_facts_k16.json and replay/source_abstract_summary_k16.json with the delivered files. Requires Python 3.10+ standard library only; leave assertions enabled.

The finite post-fixpoint scan verifies an ordinary mathematical inductive invariant for all source steps from the exact initialized register seed. No numerical execution bound is used. The source rewrite theorem is in source_invariant.tex. Binary compilation, state reduction and blank initialization of any rewritten decoder remain separate obligations.

Additional relational replay: python3 -B verify_relational_parity.py --output replay-relational
It refines the value classes using arbitrary sets of nine-register parity patterns. The fixed-point certificate passes and finds the same two forced guards and three unreachable leaves. The summary contains elapsed time, so compare functional fields and the exact facts, not the entire timing-bearing summary.

# R9 quotient-size obstruction: Lean-checked conditional lemma

For a discrete ordered commutative ring, `Trace74R9QuotientSize.impossible` assumes `q≥64`, `y≥q³`, `x>1048572(q−1)y`, and

`4y(x+1)−1 | (q−1)(4y−1)(2052y−1)(511y−128)`.

It derives the positive quotient and strict size bounds needed by the checked R9 bounded-quotient obstruction. These are explicit arithmetic premises; the lemma itself does not supply a graph zero, a first Pell index or a guard.

The controlled Lean check passed in actual outer session 65044, exit 0; terminal SHA-256 `ae1de48959c6d0e7f1981660e1ba57d0d70a7df9cc2f2afbe705f1f218302cff`. The [independent result audit](../../reviews/trace74-r9-quotient-size-result-independent/README.md) verified 37 recorded direct pins, object, log and report. Full historical project/package/dynamic ancestry and ongoing search-path selection remain outside this evidence.

# Conditional compact44 controller unit

`ArithmeticConstructionUnitCompact44.lean` proves a conditional rank-factor
unit theorem in every model of IΣ₁. For model elements `K,m,e`, put
`N=581197^(m+1)`, `w=581197^e`, and

```
Gamma = 2^(67*1063) * ((2^(590069*N))^2 - 1)
        * (1 + 2^(590069*N) * (K + 2^(590069*w))).
```

If `K % 342946332593 = 284898815895`, the theorem `gamma_unit` provides an
inverse of `Gamma` modulo `590069*N`. The exponents and inverse are model
elements, including when `m` or `e` is nonstandard. `gamma_unit_nat` instead
accepts the corresponding standard natural-number residue premise for `k` and
uses the cast `(k : V)`. The proof adapts the 2011
`ArithmeticConstructionUnit` argument to compact44 constants: modular
exponentiation, model Σ₁ induction for the Frobenius congruence, and the
existing exponent-lifting theorem construct the inverse explicitly.

The bounded author-side compile actually exited 0 in 79.408 seconds, with
no warnings; `gamma_unit` and `gamma_unit_nat` report exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The final source,
compiler log, exact command, direct-object hashes and exit receipt are retained
here. An initial import attempt exited 1 before elaboration because the
overlay lacked sibling project modules. Its output and receipt are retained;
the successful run used an overlay whose other project modules were linked to
the historical provider. That setup can be recreated with
`cp -as /tmp/pell-class-simp-188/final/DiophantineConsistency/.` into the
overlay's `lib/DiophantineConsistency/` after placing the earlier controller
data object there, followed by `python3 run.py`.

This is an incremental, single-author run using the previously built
`ArithmeticControllerDataCompact44` object and historical provider, not a
paired replay or a fresh authenticated source closure. Package, transitive,
dynamic-loading and between-snapshot ancestry remain inherited. The theorem
**does not establish the residue premise for** `paramKernel (2^67)`, identify
the retained K bytes, prove that this formula is the actual rank variation,
construct the dummy locations, or establish a graph-zero or iPRA theorem.
The recipe-derived numerical observation in the companion
[unit plan](../compact44-controller-unit-plan/README.md) is external evidence
and does not discharge the Lean premise.

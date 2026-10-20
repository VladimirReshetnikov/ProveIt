# Three-value singleton algebra diagnostic

The complete bounded search found **no model** for the proposed fourth parameter `R(A,B)`. It examined 78,732 implication/quantifier/equality assignments in 0.361 seconds under a hard 60-second alarm. This excludes only the finite family below; it neither calibrates the proposal with ZFC consistency nor rules out a larger or label-dependent algebra.

The carrier is `{f=0,t=1,x=2}`, with exactly `t` designated, every membership atom valued `f`, and every equality atom valued one fixed `e`. All three choices of `e` were examined, in order `t,f,x`. Every binder is interpreted by the same unary function `q`. The search fixes `I(t,t)=t` for the literal code-zero alias, imposes `I(t,y) != t` for `y != t` to preserve modus ponens, and fixes `q(t)=t` to preserve generalization. It imposes neither classical negation nor reflection/designatedness equivalence for `q`.

There are `2² × 3⁶ = 2,916` implication tables and nine quantifier maps for each equality value: `26,244 × 3 = 78,732`. For each table, the tested values are the closure of `{f,t,e}` under `I` and `q`. These are exactly the values represented by codes under the proposed interpretation. The extra value can remain unreachable; the Boolean control deliberately has only two reachable values.

The formulas were transcribed from the current `Code254.lean` and `KCode222.lean` definitions. All of rho1 through rho6, G, and the **literal** `bundle222` are checked. In particular `N(z)=I(z,f)` is not assumed involutive: the bundle is kept as `N(I(vrel,nks))`. The repeated quantifiers in `req` and `clos`, including their shadowed labels, remain repeated applications of `q`. The syntactic gate on the bundle is not mistaken for inequality of singleton-domain objects: fresh natural labels still realize a gated instance for every matrix code, so every reachable matrix value is tested.

The restricted rho8 check substitutes `u=f`, because every possible `R(A,B)` atom has that value. The unrestricted control requires all reachable `u`. It is sufficient to apply the latter test after the former: every unrestricted model is a restricted model in this same family. Thus the zero unrestricted count does not omit an equality choice or assume Boolean semantics.

| Equality value | Enumerated | Pass retained rows and literal bundle | Pass restricted rho8 | Pass unrestricted rho8 |
|---|---:|---:|---:|---:|
| `t` | 26,244 | 23 | 0 | 0 |
| `f` | 26,244 | 1 | 0 | 0 |
| `x` | 26,244 | 0 | 0 | 0 |

The separate Boolean control validates the nonbundle rows and unrestricted rho8, while the true-matrix literal bundle fails, as expected for empty singleton membership. The candidate search uses early rejection and records first-failing rows, so its failure counts are ordered-filter counts, not counts of all violated axioms. An independent declarative formula evaluator is present for any surviving candidate; there were no survivors on this run. The source/API transcription was read before execution; no Lean compiler or delivered search program was invoked.

Actual outputs are under `/tmp/k219-singleton-algebra-run1/`, with adjacent captured stdout/stderr. The run directory preserves the exact search source and both Lean definition snapshots. A future positive finite-matrix result would still require a code-evaluation and derivation-induction proof before claiming a consistency theorem. No such positive result occurred here.

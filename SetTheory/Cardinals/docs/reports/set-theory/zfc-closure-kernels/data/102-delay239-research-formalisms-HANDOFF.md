# Formalism research handoff

## Main contribution

`specialization_obstructions.tex` is a polished supplementary section ready to
input into the parent's report. It proves two exact logical nonderivability
results, including **all seven retained logical rows, GEN, MP, atomic fresh
vacuity, and IR**. Neither CP nor GIC is included in the countermodels.

1. **Any positive reconstruction of the fourth input fails to recover Peirce:**
   for any implication-only term `U(a,b,c,Truth)` of any size, the rho8 replacement
   `L(a,b,c,U)` is valid in the three-valued Lukasiewicz matrix, but Peirce is not.
   Full L has exactly one bad tuple `(a,b,c,u)=(1,2,1,0)`; the positive subalgebra
   `{1,2}` excludes it. This is a structural-induction theorem, not a bounded search.
2. **The untested `u = not b` escape also has a quantified obstruction:**
   the four-valued matrix and universal-minimum order in the section validate
   that axiom and all retained logical schemas; Peirce at `P=1,Q=0` has value1.

The three-valued matrix itself is inherited from Source71's missing-Peirce
propositional example. Its application to every positive substitution term and
its quantified expansion are new results of this investigation. The four-valued
certificate was found in this investigation; do not claim novelty relative to
all published algebraic logic.

## Reproduce

```sh
python check_specialization_obstructions.py
python measure_specializations.py --repo /path/to/ProveIt
```

The first command is standalone and needs only Python's standard library. The
second uses unchanged repository helper modules and bundled pinned upstream
compiler/DAG/spec inputs. It writes diagnostic tables and `controls/specialization_costs.json`.

The finite checker passes all declared obligations, including 81/256 quantifier
distribution cases, 9/16 two-point rho6 vectors, and 648/2048 tests of the three
equality rows over every membership truth table on a two-element domain.

## Exact emitted costs

Unshared public Wade backend:

| Fourth input | rho8 macros | AX macros | Decision+framework |
|---|---:|---:|---:|
| independent u | 15 | 186 | 219+62=281 |
| a, b, c | 13 | 184 | 216+62=278 |
| Truth | 13 | 184 | 217+62=279 |
| F | 12 | 183 | 216+62=278 |
| a→b | 15 | 186 | 218+62=280 |
| b→a | 15 | 186 | 218+62=280 |
| not b | 14 | 185 | 217+62=279 |

Common-subsequence extraction makes only b→a one state smaller (279). All
controls retain a missing `1.inc/read1` row inherited from the public backend;
these are diagnostic partial transition programs, not new total ZFC machines.
The delta does not transfer to the current optimized240 backend. No set-theory
calibration or internal PA endpoint is claimed by these controls.

## Files worth incorporating

- `specialization_obstructions.tex`
- `check_specialization_obstructions.py`
- `specialization_obstructions.json`
- `measure_specializations.py`
- `controls/` (JSON plus18 emitted diagnostic tables)
- `reference/` (pinned TMBuilder.py, tm.py, tmdb.py, Dag254.v, spec.py, LICENSE.wade)

Do **not** include the scratch CD executables, failed-search logs, or exploratory
`*_results.json` files. Their bounded searches contributed no positive proof.

## Source URLs

Current exact baseline status:
https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Research/ZFC/candidate-rotation240/README.md

Published logical source and completed classical basis:
https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/design/logic.md
https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/tools/logic/spec.py

Published SIR closure axioms and equiconsistency argument:
https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/design/settheory.md

Existing Source71 countermodels and controls (at repo commit above):
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/71-qt-research-formalisms-formalism_notes.txt`

Primary research on shortest implication/false axioms (19 symbols for one
single axiom under condensed detachment; not a lower bound on TM states):
https://fitelson.org/ar.html

Primary basis for an alternative intuitionistic/nonextensional route:
Harvey Friedman, *The consistency of classical set theory relative to a set
theory with intuitionistic logic*, JSL38(2),315–319,1973.
https://doi.org/10.2307/2272068
https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/consistency-of-classical-set-theory-relative-to-a-set-theory-with-intu1tionistic-logic1/86B4DACED9C8BE1296F245106C423F41

Friedman's extract explicitly gives a syntactic transformation of collection-ZF
without native identity into intuitionistic set theory without extensionality,
using an auxiliary weak-power theory. It also warns that direct double-negation
translations of ordinary extensionality and powerset are problematic. Thus an
intuitionistic route is well motivated, but the present matrix-obstructed
calculus is not established to contain full intuitionistic logic or that theory.
No equiconsistency follows merely from naming IZF.

Primary reference for disequality/distinctors as a possible freshness encoding:
https://us.metamath.org/mpeuni/mmzfcnd.html

An unconditional encoding `D(c,a) -> (D(c,b) -> B)` with
`D(c,a)=not All(c, Eq(c,a))` is semantically equivalent to numeric freshness over
native-equality models with at least two elements. But replacing the gated
vacuity rows at the same time makes deriving all required guards potentially
circular in this particular calculus. There is no source-calculus recovery proof
or cost improvement for that proposal here.

## Other potentially useful observations

Replacing rho8 by K and S only might avoid an explicit Peirce axiom by deriving
DNE from rho6 and fresh quantifier transport. I did not prove the necessary
noncircular vacuity/UI bootstrap; do not describe this as a calibrated source.
Prior Source71 controls tested K/S/Peirce and K/B/Peirce, and later K/B/Peirce-F.

The scalar source transformations measured here are independent of the parent's
new239 construction and do not alter its proof requirements. Keep any ordinary
mathematical239 endpoint distinct from exact-table Lean and internal-PA status.

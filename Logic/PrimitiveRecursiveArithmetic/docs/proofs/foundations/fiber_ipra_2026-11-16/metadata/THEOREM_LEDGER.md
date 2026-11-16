# FIBER-iPRA theorem and status ledger

Status vocabulary:

- **human-complete**: a full mathematical proof is in the report;
- **inherited-checked**: the result is a named checked ProveIt dependency;
- **source-candidate**: Lean source is supplied but was not elaborated here;
- **tested-reference**: exact Python tests exercise the finite algorithm only;
- **conditional**: the theorem retains an explicit producer residual;
- **obstruction**: the stronger requested interface is proved impossible and a
  corrected formulation is supplied.

| ID | Claim | Report | Status | Formal residual |
|---|---|---|---|---|
| K1 | Local certificate sealing | Thm. 4.1 | inherited-checked | `Prf.exE` |
| K2 | Simultaneous residual discharge | Thm. 4.3 | inherited-checked | `Prf.trans` |
| K3 | Fixed bounded-formula Boolean reflection | Thm. 4.4 | human-complete schema | implement folds and generator |
| K4 | Canonical bounded selection | Thm. 4.5 | human-complete over inherited search; tested-reference | one-success adapter |
| K5 | Master-certificate theorem | Thm. 4.7 | human-complete; tested-reference | sequence coding/object proof |
| K6 | Least finite monotone demand closure | Thm. 4.8 | human-complete; tested-reference | encoded-vector object proof |
| K7 | Bounded strategy realization | Thm. 4.10 | human-complete; tested-reference | generic fixed-pattern compiler |
| C1 | FIBER compilation theorem | Thm. 5.1 | human-complete metatheorem | compiler implementation |
| C2 | Realizer composition | Thm. 5.2 | human-complete | generated `Prf.trans` proof |
| R1 | Bounded producer elimination | Sec. 6.3 | human-complete | instantiate search/cut |
| A1 | Dyadic adjacent-motion theorem | Thm. 7.1 | human-complete; tested-reference | signed-integer object lemmas |
| A2 | General summable-tail theorem | Sec. 7.2 | human-complete schema | finite sum/triangle library adapters |
| A3 | Finite-net lifting | Thm. 7.3 | human-complete; tested-reference | concrete object encoding |
| A4 | Guarded bisection uniqueness | Sec. 7.7 | human-complete pattern; tested-reference | interval checker and positivity certificate |
| O1 | No PR universal evaluator | Thm. 2.1 | human-complete obstruction | none; interface redesigned |
| O2 | No unguarded finite-use exact sign selector | Thm. 8.1 | human-complete obstruction | separation guard or relational output |
| G1 | Stable cluster transport | Thm. 8.2 | human-complete schema | finite incidence/multiplicity checker |
| G2 | Gap-guarded labels | Prop. 8.3 | human-complete | positive separation producer |
| G3 | Finite-algebra observation | Thm. 8.4 | human-complete | quotient identity certificates |
| L1 | Structural Lean kernel candidate | `lean/FIBER/Kernel.lean` | source-candidate | elaborate in pinned repo |
| L2 | Full Lean architecture | Sec. 10 and plan | source-candidate | phases 1-9 |

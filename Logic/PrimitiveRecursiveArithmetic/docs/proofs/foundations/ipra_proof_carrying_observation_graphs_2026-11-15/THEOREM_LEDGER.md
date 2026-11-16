# Theorem and claim ledger

Status vocabulary:

- **Human-complete** — the report contains a full mathematical argument.
- **Finite-tested** — the exact reference implementation exercises the claim on
  nontrivial finite instances.
- **Inherited checked core** — an existing repository packet reports a Lean
  build of an actual `Prf PRAAx` declaration; the current environment did not
  rerun that build.
- **Lean blueprint** — concrete definitions, target signatures, and a
  dependency-ordered completion path are supplied, but no build is claimed.
- **Conditional/open** — a theorem-specific quantitative producer is isolated
  and not supplied by this framework.

| ID | Claim | Report | Status | Lean / executable route |
|---|---|---|---|---|
| B1 | Booleanization of every fixed quantifier-free formula | §4 | Human-complete | `BoolReflection`; Boolean PR equations |
| B2 | Reflection for bounded universal/existential folds | §4 | Human-complete | `PRA.qfInd` on fold equations |
| B3 | Booleanization of fixed strictly bounded formulas | §4 | Human-complete; Lean blueprint | Host recursion on `BForm` |
| B4 | Least bounded witness, minimality, and no-witness branch | §4 | Human-complete; finite-tested; Lean blueprint | Primitive-recursive search state |
| T1 | Finite-trace reflection at arbitrary PR fuel | §5 | Human-complete; inherited checked core | `primitiveRecursionInvariant`, `primitiveRecursionAt` |
| T2 | Terminal invariant implies a public certificate | §5 | Human-complete; inherited checked pattern | `TraceExit.compile`, `loopProducesCertificate` |
| G1 | Finite proof-graph compilation by topological fold | §5 | Human-complete; source core supplied | `Rule`, `Compiled.extend` |
| G2 | Staged internalization of a fixed PCOG | §5 | Human-complete as a conditional compiler metatheorem; Lean blueprint | Compile traces, then fold graph rules |
| D1 | Least safe backward demand assignment | §6 | Human-complete; finite-tested | Reverse topological table trace |
| D2 | Forward validity at computed demands | §6 | Human-complete; finite-tested | Topological proof composition |
| R1 | Backward viability iff finite compatible path | §7 | Human-complete; finite-tested; Lean blueprint | Reverse-time PR recurrence |
| R2 | Lexicographically least viable finite path | §7 | Human-complete; finite-tested | Bounded least search at each level |
| R3 | Shrinking finite-horizon coherence and Cauchy modulus | §7 | Human-complete; Lean blueprint | Rational metric/table module |
| R4 | Exact label collapse under a positive gap | §7 | Human-complete; finite-tested | Bounded containment search |
| O1 | Independent-certificate observation comparison | §8 | Human-complete; inherited checked core | Integrate `ObservableGlue` |
| O2 | Finite-net infimum transfer | §8 | Human-complete conditional schema | Coverage/modulus nodes plus bounded minimum |
| F1 | Mixed-radix rank for fixed-dimensional descent | §9 | Human-complete; finite-tested | Tuple/rank equations and QF induction |
| F2 | Common good index outside finitely many exceptional sets | §9 | Human-complete; finite-tested | Indicator sums, union bound, least search |
| H1 | Explicit height bound implies a complete finite list | §9 | Human-complete; finite-tested | Bounded enumeration and filter reflection |
| H2 | Complete finite list implies a height bound | §9 | Human-complete | Finite maximum and completeness |
| A1 | Finite auxiliary exhaustion avoids a target-to-auxiliary selector | §9 | Human-complete | Bounded union and target filter |
| E1 | Cubic bisection invariant for `y^3+y=x` | §12 | Human-complete; finite-tested | First end-to-end benchmark target |
| E2 | Guarded reciprocal precision `q+2a+4` and final cubic observable width | §12 | Human-complete; finite-tested; Lean blueprint | Rational interval inequalities |
| X1 | General effective Faltings/Siegel height or cover producer | §§10,13 | Conditional/open | Downstream list compiler is complete once supplied |
| X2 | Uniform general Mordell–Weil covering/generator producer | §§10,13 | Conditional/open | Verification/descent layer isolated |
| X3 | Deep prime-distribution estimates and effective constants | §§10,13 | Conditional/open | Finite sums and final inequalities compile |
| X4 | Uniform exact singular-branch selector from arbitrary Cauchy names | §§7,10,13 | Deliberately not claimed | Finite clouds; gap-guarded collapse only |

No row marked “Lean blueprint” is asserted as a theorem merely because its
proposition or structure typechecks. A completed application must end in an
actual `Prf PRAAx [] ...` declaration and pass the repository build and axiom
audit.

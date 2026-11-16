# Theorem ledger

Status vocabulary:

- **upstream checked** — compiled in the pinned ProveIt tree.
- **candidate** — no-placeholder Lean source supplied, not elaborated here.
- **human complete** — a full mathematical argument is supplied.
- **blueprint** — exact target and path, no proof term claimed.
- **executable evidence** — finite reference implementation/tests only.
- **conditional** — the conclusion explicitly assumes a producer boundary.

| ID | Result | Status | Lean endpoint / residual work |
|---|---|---|---|
| SCR-T01 | One-certificate scoped realization | human complete; candidate | `Contract.close`; elaborate `Kernel.lean` |
| SCR-T02 | Missing producer gives `(∃c, V c) → G` | human complete; candidate | `Contract.conditional` |
| SCR-T03 | Dependent nested sealing | human complete | implement reusable two-/list-contract combinators |
| SCR-T04 | Finite SCR compiler soundness | human complete | host program syntax optional; compile by structural recursion |
| SCR-T05 | Boundary normal form | human complete | `Boundary.collect` and implication wrapper |
| SCR-T06 | Bounded-existential reflection via search | human complete; blueprint | reflected atom package and search adapter |
| SCR-T07 | Bounded-universal reflection by counterexample search | human complete; blueprint | `Boolean.ballReflect` |
| SCR-T08 | Least accepted certificate below explicit cutoff | human complete; blueprint | wrap upstream `Search.search_found/spec/minimal` |
| SCR-T09 | Whole-path selection avoids greedy dead ends | human complete; executable evidence | path test passes |
| SCR-T10 | Trace prefix invariant by one qf induction | human complete; blueprint | `Trace.badSplit`, `Trace.prefixInvariant` |
| SCR-T11 | Bounded inflationary demand iteration stabilizes | human complete | code product-lattice rank and qf induction |
| SCR-T12 | Fixed-shape finite-strategy soundness | human complete; blueprint | begin with `∀∃` shape |
| SCR-T13 | Fixed-shape finite-strategy completeness | human proof architecture; blueprint | nested search/table construction |
| SCR-T14 | Exact observer output is single-valued | human complete; blueprint | `Observer.unique` |
| SCR-T15 | Diameter transport through a modulus | human complete; blueprint | rational metric library adapter |
| SCR-T16 | Separation gap stabilizes exact label | human complete; blueprint | clear denominators and use order library |
| SCR-T17 | Open Foundation-to-Concise finite-context transport | human complete; blueprint | repeated deduction + existing `hilbertToConcise` |
| SCR-T18 | Open sequent equivalence up to zero normalization | blueprint with detailed path | prove Foundation round trip on PR codes |
| APP-E01 | Exact cubic bisection trace and width | human complete; executable evidence | formalize rational state and local preservation |
| APP-E02 | Symmetric root observer erases permutations | human complete; executable evidence | formalize finite permutation/root certificate |
| APP-E03 | Strong carrier selections induce same homology map | human complete at finite-chain level | chain/prism library required |
| APP-E04 | Complete curve point list inside supplied height box | executable evidence; human complete verifier | formalize box enumeration; global theorem conditional on height producer |

No row in this ledger asserts a new kernel-checked theorem.

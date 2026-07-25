# Turing degrees in Lean and Rocq

This project formalizes the central definitions and a substantial part of the
theorem inventory in the
[Turing degree article](https://en.wikipedia.org/w/index.php?title=Turing_degree&oldid=1353991718).
The two developments are complementary rather than cosmetically identical:
Lean builds a quotient of set representatives on Mathlib's oracle-recursion
semantics, while Rocq exposes deeper jump and priority results from a pinned
constructive computability library. See the
[claim-by-claim coverage ledger](COVERAGE.md) for the exact boundary.

## Lean development

The Lean files build on
[`Mathlib.Computability.TuringDegree`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TuringDegree.html)
and its genuine `RecursiveIn` oracle semantics. They prove:

- characteristic-oracle Turing reducibility and equivalence for `Set ℕ`;
- the quotient `SetTuringDegree`, its partial order, and its least degree;
- a representative has degree zero exactly when its membership predicate is
  computable;
- the article's exact even/odd join, both injections, its LUB theorem, and the
  resulting join-semilattice;
- complement invariance;
- c.e.-completeness and noncomputability of the ordinary halting set, hence
  `0 < 0'` and every c.e. degree lies below `0'`;
- precise structural notions for minimality, density, GLBs (including within
  c.e. degrees), exact pairs, relative lowness, recursive approximations, and
  the finite-change hierarchy, together with their elementary consequences;
- an explicit finite syntax complete for singleton-oracle `Nat.RecursiveIn`;
- every degree class is countably infinite, every lower cone is countable,
  there are exactly continuum many degrees, and every strict upper cone has
  cardinality continuum.

The last four cardinality claims are derived from countable program syntax and
countable fibers; no degree-existence theorem is postulated. Lean does not yet
provide the general jump, Kleene--Post, Shoenfield-limit, Post-hierarchy, or
priority constructions formalized on the Rocq side. Jump inversion and density
of the c.e. degrees remain outside both developments.

### Lean build

The root workspace registers the `TuringDegrees` library:

```powershell
$env:LEAN_NUM_THREADS = '1' # needed only if the ambient value is 0
lake build +TuringDegrees +TuringDegrees.Audit
```

The project-local build is also available:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake --dir Computability/TuringDegrees/Lean build
```

`TuringDegrees/Audit.lean` checks the public results and prints their Lean
axiom dependencies.

### Lean file map

- `Lean/TuringDegrees/Basic.lean`: characteristic oracles, reducibility,
  equivalence, quotient, and partial order.
- `Lean/TuringDegrees/Computable.lean`: degree zero and computable sets.
- `Lean/TuringDegrees/Join.lean`: exact join, LUB, semilattice, and complement.
- `Lean/TuringDegrees/Halting.lean`: `0'`, c.e. sets, and many-one completeness.
- `Lean/TuringDegrees/Structure.lean`: structural and finite-change notions.
- `Lean/TuringDegrees/Representatives.lean`: explicit distinct representatives.
- `Lean/TuringDegrees/Cardinality.lean`: program coding and cardinality proofs.
- `Lean/TuringDegrees/Audit.lean`: public API and axiom audit.

## Rocq development

The Rocq files use the constructive oracle-machine semantics from
[`coq-synthetic-computability`](https://github.com/uds-psl/coq-synthetic-computability),
pinned as a git submodule at commit
`8fc0014f1b35f832e78d98f72dfef525aa39861f` (MIT license). They prove:

- oracle Turing reducibility on predicates over `nat`;
- Turing equivalence as setoid equality, with a preorder and partial order;
- the zero degree, with the `MP` boundary for its characterization as the
  degree of decidable sets;
- the exact even/odd join, its LUB theorem, and semilattice laws;
- a well-defined monotone jump with `A <T A'` for every `A`;
- Kleene--Post incomparable degrees and failure of linearity;
- c.e. sets, many-one completeness of `0'`, and non-c.e. complement of `0'`;
- corrected structural, exact-pair, and finite-change notions;
- Shoenfield's limit lemma with its constructive hypotheses visible;
- hierarchy membership, many-one hardness, and relativized-enumerability
  clauses of Post's theorem;
- an intermediate c.e. degree `P` with `0 <T P <T 0'`, under explicit `MP`
  and the constructive Post-problem principle.

The Rocq files intentionally use a setoid presentation rather than a quotient:
representatives are predicates `nat -> Prop`, equality is mutual Turing
reducibility, and the order is proper for that equality. This avoids requiring
an undecidable quotient or informative classical choice.

### Constructive assumptions

Elementary order, zero, join, and structural results need only the library's
abstract partiality implementation. The converse “zero degree implies
decidable” and the strict lower inequality in the Post-problem result use
`MP`. Jump, Kleene--Post, hierarchy, and Post-problem results take an `EPF`
(enumeration of partial functions) and relevant encodings as parameters. The
forward limit lemma uses `LEM_Σ 1`; its reverse additionally uses pointwise
`definite` hypotheses. None is installed as a global axiom: `Audit.v` reports
all principal exported theorem groups closed under the global context.

### Rocq build

The tested environment is Rocq 9.2 with OCaml 4.14.2,
`rocq-equations.1.3.2+9.2`, and `rocq-stdpp.1.13.0`:

```powershell
opam install rocq-equations.1.3.2+9.2 rocq-stdpp.1.13.0
git submodule update --init lib/Coq-Synthetic-Computability
pwsh -NoProfile -File Computability/TuringDegrees/Coq/BuildSyntheticComputability.ps1
pwsh -NoProfile -File Computability/TuringDegrees/Coq/Build.ps1
```

The first helper applies the tracked Rocq 9.2/stdpp 1.13 compatibility patch,
builds the upstream 63-file default target, and restores the submodule to its
pristine pinned commit even after failure. The second verifies the exact local
source set before compiling all ten wrappers. The root `_CoqProject` registers
the same load paths and wrapper files.

### Rocq file map

- `Coq/Core.v`: setoid degrees, order, and zero.
- `Coq/Join.v`: exact even/odd join and upper-semilattice laws.
- `Coq/Jump.v`: jump monotonicity, extensionality, strictness, and iterates.
- `Coq/Structure.v`: Kleene--Post and nonlinearity.
- `Coq/ComputablyEnumerable.v`: c.e. completeness of `0'`.
- `Coq/DegreeNotions.v`: minimality/density, relative GLBs, exact pairs,
  sequence LUBs, relative lowness, and finite-change approximations.
- `Coq/Limit.v`: Shoenfield's limit lemma.
- `Coq/PostTheorem.v`: Post's theorem for predicates on naturals.
- `Coq/PostProblem.v`: a conditional intermediate c.e. degree.
- `Coq/Audit.v`: public API and global-assumption audit.

## Deliberate boundary

The project does not postulate the article's remaining deep theorems merely to
lengthen the checklist. Current omissions include minimal-degree existence,
density of the c.e. degrees, jump inversion, continuum antichains, arbitrary
countable-poset embeddings, nonlattice witnesses, exact-pair existence, the
r.e.-degree lattice embedding/nonembedding theorems, and the first-order-
theory completeness results. The omitted classification and construction
results also include universal incomparable partners, the `V = L` maximal
chain, interval antichains, relative-low extensions, descending jump-control
sequences, definability of jump, non-c.e. degrees below `0'`, the finer
`n`-c.e./weakly-`n`-c.e. hierarchy claims, and the simple-low construction.

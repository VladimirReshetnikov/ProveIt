# Lean formalization: C1, and report 10

Lean 4 (v4.32.0) + Mathlib (v4.32.0).  The library `CoarseDegrees` formalizes the statement
**C1** of the research plan (`Computability/TuringDegrees/Research/CoarseDegrees/research-plan`) — *every nonuniform coarse-equivalence class
contains a representative of least Turing degree*, the coarse instance of Question 7 of
Gerdes, arXiv:2508.06925v1 — and proves that it is false, together with its analogue for uniform
coarse equivalence:

```lean
theorem CoarseDegrees.not_C1         : ¬ C1
theorem CoarseDegrees.not_C1Uniform  : ¬ C1Uniform
theorem CoarseDegrees.not_C1_dyadic  : ¬ C1   -- a third route, independent of HJKS
```

Turing reducibility is Mathlib's oracle semantics (`Mathlib.Computability.TuringDegree`,
`RecursiveIn`).  Set-level reducibility (`≤ᵀₛ`), characteristic oracles and the finite
oracle-program syntax used for *uniform* coarse reductions come from the `TuringDegrees`
library beside it in this project (`Computability/TuringDegrees/Lean`).  This library was
developed in the separate Cardinals repository, where ProveIt was a sibling checkout at
`C:\ProveIt`; the comments in the Lean sources still name it so.  It reached ProveIt with the
Cardinals merge and now lives in the Turing-degrees project.

The library also formalizes research report 10 (`Computability/TuringDegrees/Research/CoarseDegrees/research-reports/10`): coarse classes
with no representative of least *hyperdegree*, and the failure of Martin's cone theorem for the
coarse degrees.  See "Report 10" below.

## Build

From the ProveIt root (one target at a time, as the repository README requires):

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '2'
lake build CoarseDegrees
lake build CoarseDegrees.Audit     # prints the axioms behind each main theorem
```

or with the project-local package, `lake --dir Computability/TuringDegrees/Lean build`.

**Admitted statements.** Unlike the rest of ProveIt, this library closes eight published
results with `admit` (listed in the two admitted-statement tables below).  The build therefore
reports eight `declaration uses 'sorry'` warnings, and `CoarseDegrees.Audit` shows `sorryAx`
in exactly the theorems that rest on them.  The `TuringDegrees` library admits nothing, and
the repository-wide import surface `ProveIt.lean` does not import `CoarseDegrees`.

## What is formalized

The proof is the *literature route* that all nine research reports identified (synthesis,
Section 1): every coarse description of `X` lies in the coarse class of `X`, so a representative
of least degree is computable from all of them; if the sets computable from every coarse
description of `X` (its *core*, the `X^𝔠` of Hirschfeldt–Jockusch–Kuyper–Schupp) are all
computable, the least representative is computable, and then `X` would be coarsely computable.

Writing this down in Lean exposes two steps that the three-line informal deduction passes over,
and both are proved:

* **Functions versus sets.** C1 quantifies over arbitrary total functions `g : ℕ → ℕ`, while the
  core consists of sets.  `graph_tRed` and `computable_of_graph` show that the graph of `g` is
  computable from `g` and that a computable graph makes `g` computable (unbounded search);
  `computable_of_core_trivial` is the resulting bridge.
* **Numerical versus binary descriptions.** A coarse description of a characteristic function may
  take values other than 0 and 1.  `setCoarselyComputable_of_coarselyComputable` is the binary
  normalization (synthesis, Lemma 2.2).

| File | Content | Status |
|---|---|---|
| `Density.lean` | `count`, `DensityZero`; monotonicity, finite unions | proved |
| `Basic.lean` | oracles of total functions, `≤ₜ`; coarse descriptions `CoarseEq`; `≤ₙ`, `≤ᵤ`, `≡ₙ`, `≡ᵤ`; `C1`, `C1Uniform`; synthesis Lemmas 2.1, 2.3, 2.4 (`CoarseEq.ucEquiv`, `NCEquiv.exists_description`, `exists_computable_ncEquiv_iff`, `no_least_of_two_witnesses`), `no_least_of_trivial_core` | proved |
| `Sets.lean` | `SetCoarseEq`, `SetCoarselyComputable`, `core`; binary normalization; graph coding; definitions of `OneGeneric` and `GenericallyComputable` | proved |
| `Generic.lean` | 1-generic sets exist (finite-extension construction over all codes) | proved |
| `GenericDensity.lean` | a 1-generic set is not coarsely computable (Jockusch–Schupp 2012, remark after Prop. 2.15; synthesis Lemma 5.1), including the computability of the extension map and the c.e.-ness of its range | proved |
| `Published.lean` | three published theorems | **admitted** |
| `DyadicRoute.lean` | `not_setCoarselyComputable_Rc`, `no_least_of_dyadic`, `exists_not_limitComputable`, `not_C1_dyadic`, `not_C1Uniform_dyadic` | proved from **1 admitted** consequence of Cooper 1973 |
| `C1.lean` | `no_least_of_core_trivial`, `OneGeneric.no_least`, `exists_re_no_least`, `not_C1`, `not_C1'`, `not_C1Uniform`, `not_C1Uniform'`, `exists_binary_counterexample` | proved from the above |
| `Audit.lean` | axiom audit | — |

## Policy on admitted statements

Only results from the literature are admitted, each closed by the tactic `admit` with its source
in the docstring; nothing else uses `sorry`.  For C1, three admitted statements remain, all in
`Published.lean` (report 10 has five more, listed in its own section below):

| Admitted statement | Reference | Used by |
|---|---|---|
| `OneGeneric.core_trivial` | HJKS, Theorem 4.2: "If `X` is 1-generic then `X^𝔠 = 𝟎`" | Route G: `not_C1`, `not_C1Uniform` |
| `exists_re_genericallyComputable_not_coarselyComputable` | JS, Theorem 2.26: "There is a generically computable c.e. set `A` which is not coarsely computable" | Route C: `not_C1'`, `not_C1Uniform'`, `exists_binary_counterexample` |
| `GenericallyComputable.core_trivial` | HJKS, Theorem 4.3, final clause ("In particular, the above holds when `X` is generically computable but not coarsely computable") | Route C |

HJKS = D. R. Hirschfeldt, C. G. Jockusch Jr., R. Kuyper, P. E. Schupp, *Coarse reducibility and
algorithmic randomness*, J. Symb. Log. 81 (2016), 1028–1046, arXiv:1505.01707.  JS = C. G.
Jockusch Jr., P. E. Schupp, *Generic computability, Turing degrees, and asymptotic density*,
J. London Math. Soc. 85 (2012), 472–490, arXiv:1010.5212.  Theorem numbers were checked against
the arXiv texts on 18 September 2026.  Neither paper is formalized in `C:\ProveIt`.

A third route, in `DyadicRoute.lean`, uses neither paper; see "The dyadic route" below.

| Admitted statement | Reference | Used by |
|---|---|---|
| `exists_minimal_pair_limit` | consequence of Cooper, *Minimal degrees and the jump operator*, JSL 38 (1973), 249–271 (every degree above `0′` is the jump of a minimal degree); the derivation is in the docstring | Route D: `not_C1_dyadic`, `not_C1Uniform_dyadic` |

The three routes share no admitted statement, so `¬ C1` is obtained three times, once from a
single admitted theorem (HJKS 4.2), once from two others, and once from Cooper 1973.  `Audit.lean` confirms that everything
outside `Published.lean` and `C1.lean` depends only on `propext`, `Classical.choice` and
`Quot.sound`, and that the theorems of `C1.lean` add only `sorryAx`.

## Report 10

```lean
theorem CoarseDegrees.bridge                      -- the bridge lemma in forcing form (Lemma 4.2)
theorem CoarseDegrees.exists_generic_pair          -- the generic pair for a budget (Section 4.3)
theorem CoarseDegrees.exists_hyp_minimal_pair      -- Theorem 1.1 (Z = ∅)
theorem CoarseDegrees.exists_no_least_hyperdegree' -- Corollary 1.2
theorem CoarseDegrees.no_cone_theorem              -- Theorem 1.5(b), nonuniform coarse degrees
theorem CoarseDegrees.leastClass_invariant         -- invariance of the set 𝒜 of Theorem 1.5
theorem CoarseDegrees.description_iff_limit        -- Theorem 1.4, the criterion for R(A)
theorem CoarseDegrees.hcore_Rc                     -- Theorem 1.4(a), Core_h(R(A)) = Δ¹₁(A)
theorem CoarseDegrees.hyperarithmetic_compactness_fails  -- Theorem 1.4(b)
```

| File | Content | Status |
|---|---|---|
| `BudgetForcing.lean` | disagreement sets of strings, hybrids; `Budget`, `countingBudget`; the forcing `Cond 𝔅` (copy extensions, padding, one-bit reserve); abstract decision systems `DecSys`; `bridge_step`, `bridge`; Rasiowa–Sikorski chains; `exists_generic_pair` | proved |
| `Hyper.lean` | `Sigma11In`, `HypIn`, `Hyp`, `HRed` (Kleene normal form); `HypIn.of_setTuringReducible` (proved); `not_setCoarseEq_of_ext`; `exists_hyp_minimal_pair`; `tRed_graph`; `exists_no_least_hyperdegree`; the square-root budget forces density zero | proved from **2 admitted** classical facts |
| `Columns.lean` | the dyadic columns `col n` (the exponent of 2 in `n+1`) and their computability; the exact tail count `\|{n < N : 2^K ∣ n+1}\| = ⌊N/2^K⌋`; a set meeting every column in a bounded set has density zero | proved |
| `Limit.lean` | reductions making a single oracle query; `LimitComputableIn`; `LimitComputableIn.hypIn` — a limit of a `B`-computable approximation is `Δ¹₁(B)`, by writing both the set and its complement in Kleene normal form | proved |
| `Dyadic.lean` | the dyadic code `Rc A = {n : col n ∈ A}`; `Rc A ≡ᵀₛ A`; `exists_description_of_limit` — the easy direction of Theorem 1.4 | proved |
| `Majority.lean` | `recursiveIn_prec_total` (primitive recursion relative to an oracle, for total base and step); the column counting function `cnt` and its `D`-computability; `errCnt_div_tendsto` — the errors have relative density zero in each column; majority decoding and `limit_of_description`; `description_iff_limit` | proved |
| `Compactness.lean` | `HypIn.mono`; the hyper-core `hcore`; `hcore_Rc`; computable approximations `listApprox` at every radius; `hyperarithmetic_compactness_fails` | proved (`hcore_Rc` uses `HypIn.trans`) |
| `Block.lean` | the block code `𝓘(A)` and its computability (`computable_log2`); block counting `bcnt` and its `D`-computability; `bcnt_div_tendsto`; `blockCode_decode` — every coarse description of `𝓘(A)` computes `A`, by block majority above a threshold and a finite table below it | proved |
| `BlockChar.lean` | `exists_description_of_degree` (the sparse-coding step of the spectrum identity); `isLeastNC_blockCode`; `isLeastNC_iff_blockCode` — a coarse class has a representative of least Turing degree exactly when it is the class of a block code | proved |
| `Cone.lean` | `LeastClass` and its invariance; density estimates for joins and halves of descriptions; relatively 1-generic sets exist (`exists_oneGenericRel`); `exists_least_above`, `exists_nonleast_above`, `no_cone_theorem` | proved from **2 admitted** facts |

The new mathematics of report 10 is in `BudgetForcing.lean` and is proved with nothing
admitted: the bridge lemma is stated for an abstract decision relation `dec σ ψ n b` on strings
that persists under extension, is consistent and has dense domain, so that it covers Cohen
forcing for ranked sentences (report 10) and, in the absence of a partiality cylinder,
convergence of Turing functionals (case C of the synthesis, Lemma 8.3) at once.  The cube path of the paper proof is replaced by the chain of
hybrids `u₁.take i ++ u₀.drop i`, and the single common suffix by a suffix that grows along the
chain.

Admitted for report 10 (each closed by `admit`, with the reference in its docstring):

| Admitted statement | Reference |
|---|---|
| `HypIn.trans` | transitivity of hyperarithmetic reducibility: Rogers 1967, §16.8; Sacks, *Higher Recursion Theory*, Ch. II |
| `cohen_forcing_package` | Cohen forcing over `L_{ω₁^CK}`, facts (H2)–(H5) of report 10: Feferman, Fund. Math. 56 (1965); Sacks, *Higher Recursion Theory*, Ch. IV §3.  A single existential statement: a countable set of names with a decision relation satisfying the `DecSys` axioms, countably many dense sets of strings, hyperarithmetic definability of `{n : ∃ α ⊇ σ, α ⊩ ψ(n̄)}`, and, for every set meeting the dense sets, naming of the sets hyperarithmetic in it together with forcing = truth, and the instance of "hyperarithmetic dense sets are met" that is needed |
| `OneGenericRel.core_le` | HJKS, Theorem 4.2, relativized to an oracle |
| `OneGenericRel.not_coarselyComputableIn` | JS, remark after Proposition 2.15, relativized to an oracle (the unrelativized statement is proved in `GenericDensity.lean`) |

`blockCode_decode` was admitted until 19 September 2026 and is now proved, by the same
majority argument as the dyadic criterion: a block `[2ⁿ, 2ⁿ⁺¹)` is half of the initial segment
ending at its right endpoint, so the errors in it are eventually a minority.  The reduction is
*nonuniform*, and the formalization shows where: the finitely many blocks on which the vote may
fail are corrected from a finite table, spliced in along a computable set, and neither the
threshold nor the table is computed from the description.

Caveats.  `cohen_forcing_package` is a repackaging, made for this library, of theorems that
the sources state separately and in their own language (ramified formulas, the structures
`𝓜(ω₁^CK, G)`); its docstring says how each clause arises, but the packaging itself has not
been checked against the sources, and the report quotes those facts from memory.  The two remaining `Cone.lean` statements are
relativizations of published theorems rather than the published statements themselves.  Theorem 1.5 is formalized for the nonuniform coarse degrees and with the witness
`𝓘(Z) ⊕ X`, `X` 1-generic relative to `Z`, instead of the report's `J(h) ⊕ A`; the report's
witness needs the relativized minimal-pair theorem of the synthesis, which is not formalized.

### The dyadic route to `¬ C1`

With the criterion in hand, the route of research reports 03 and 04 and of Section 6 of the
synthesis can be run, and it uses neither HJKS nor JS:

* `not_setCoarselyComputable_Rc`: if `A` is not the limit of a computable approximation, that is
  if `A ≰ᵀ ∅′`, then `R(A)` is not coarsely computable — a computable coarse description *is* a
  computable approximation.
* `exists_not_limitComputable`: such an `A` exists.  The sets reducible to `∅` form a countable
  lower cone (`lowerConeSets_countable`, from `C:\ProveIt`), each determines the limit of the
  approximation it codes, and Cantor's theorem finishes it.
* `no_least_of_dyadic`: if `A` is limit-computable in each half of a minimal pair, the two
  descriptions the criterion supplies are the two witnesses of `no_least_of_two_witnesses`, so
  neither coarse class of `R(A)` has a representative of least Turing degree.

The one admitted ingredient is the minimal pair, `exists_minimal_pair_limit`.  It is a
consequence of Cooper's theorem that every degree above `0′` is the jump of a minimal degree,
not one of its verbatim statements: apply Cooper to `deg(A ⊕ ∅′)` and to its jump, note that
distinct minimal degrees form a minimal pair, and read `A ≤ᵀ Mᵢ′` in limit form.  The docstring
spells this out.

### Which classes do have a least degree

With `blockCode_decode` proved, the synthesis's structural theorems follow.  `BlockChar.lean`
has the characterization (synthesis, Theorem 3.6, clauses (i) ⇔ (v)):

```lean
theorem isLeastNC_iff_blockCode {X : Set ℕ} :
    (∃ g, IsLeastNC (χ X) g) ↔ ∃ B : Set ℕ, χ X ≡ₙ χ (blockCode B)
```

so `C1` asserts exactly that every function is coarsely equivalent to a block code, and each of
the three counterexamples is a set coarsely equivalent to none.  The forward direction takes
`B` to be the graph of the least representative; the converse is `blockCode_decode` applied to a
normalized description.  Nothing is admitted.

The attainment half of the spectrum identity (synthesis, Theorem 3.1) is
`exists_description_of_degree`: if `B` merely *computes* a coarse description of `X`, then `B`
is the exact degree of one, by implanting a copy of `B` on the markers `{2^k - 1}`.  This is
what turns "some representative is complicated" into a statement about the spectrum; without it
no leastness question could be refuted.

### Theorem 1.4: the dyadic codes

Theorem 1.4 is formalized, and the way around the missing jump operator is to state the
criterion in **limit form**.  `R(A)` is `Rc A = {n : col n ∈ A}`, where `col n` is the exponent
of 2 in `n + 1`, so that the bits of `A` are replicated along the dyadic columns.  The criterion
proved is

```lean
theorem description_iff_limit {B A : Set ℕ} :
    (∃ D : Set ℕ, D ≤ᵀₛ B ∧ SetCoarseEq D (Rc A)) ↔ LimitComputableIn B A
```

— by Shoenfield's limit lemma the right-hand side is `A ≤ᵀ B′`, but no jump operator is needed
to state or to prove it.  The easy direction reads the approximation at stage `n` on the column
of `n`, so each column carries only finitely many errors.  The hard direction is majority
decoding: vote over the first `s` elements of column `k`.  Because column `k` has density
`2^{-k-1} > 0` while the errors have density zero, the errors in it are eventually a minority
(`errCnt_div_tendsto`), so the vote converges to `A(k)`.  Its `B`-computability needs primitive
recursion relative to an oracle for a total base and step, which Mathlib's `RecursiveIn` API
does not expose; `recursiveIn_prec_total` supplies it.

Theorem 1.4(a) is `hcore_Rc : hcore (Rc A) = {X | HypIn A X}`.  The inclusion of the hyper-core
in `Δ¹₁(A)` is proved outright by testing the core against `R(A)` itself; only the reverse
inclusion uses the admitted `HypIn.trans`.  Theorem 1.4(b) is
`hyperarithmetic_compactness_fails`, and the audit confirms it depends on **no** admitted
statement: for non-hyperarithmetic `A` the set `A` lies in the hyper-core of `R(A)`, yet for
every `K` there is a *computable* `Y` — the first `K` bits of `A` replicated along the columns
below `K` — with `|(R(A) △ Y) ∩ [0,N)| ≤ N/2^K` for every `N`.  So the cone-avoiding compactness
theorem (HJKS 2016, Theorem 3.7), equivalently the robust-radius characterization of the core
(synthesis, Theorem 4.8), has no analogue for `≤_h`.

Not formalized from report 10: the relativization of Theorem 1.1 to an oracle `Z` and
Corollary 1.3 (every hyperdegree is an unattained infimum); the spectrum clause of Theorem
1.4(a) and the ordinal invariant of Theorem 1.4(c), which does need `ω₁^A`; Theorem 1.5(a)
(`𝒜` is `Π¹₁`), the uniform cones, and the statement about the Martin measure.

## What is not formalized

The remaining witness theorems of the synthesis are not formalized: the prefix-density metric and
the exact-pair theorems (Section 4), and the reservoir and one-bit-reserve constructions
(Sections 7–8).  Section 3 (the spectrum identity, block recovery, and the characterization of
the classes with a least degree) *is* formalized, in `Block.lean` and `BlockChar.lean`.  The jump-cone spectrum of the dyadic codes (Section 6) *is* formalized, in
`Spectrum.lean`, and `DyadicRoute.lean` makes `¬ C1` independent of HJKS at the cost of one
admitted consequence of Cooper 1973; building the minimal pair in Lean instead would need a
use-bounded model of Turing functionals, which neither Mathlib nor the Lean side of
`C:\ProveIt` provides (`RecursiveIn` takes the oracle as a total function, with no use).
The spectrum identity (synthesis, Theorem 3.1) and the block-code
characterization (Theorem 3.6) are also left for later.  `no_least_of_two_witnesses` (Lemma 2.4)
is proved and is the entry point for any such witness construction.

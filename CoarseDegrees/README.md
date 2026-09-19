# Lean formalization: C1, and report 10

Lean 4 (v4.32.0) + Mathlib (v4.32.0).  The library `CoarseDegrees` formalizes the statement
**C1** of the research plan (`docs/research-plan`) — *every nonuniform coarse-equivalence class
contains a representative of least Turing degree*, the coarse instance of Question 7 of
Gerdes, arXiv:2508.06925v1 — and proves that it is false, together with its analogue for uniform
coarse equivalence:

```lean
theorem CoarseDegrees.not_C1        : ¬ C1
theorem CoarseDegrees.not_C1Uniform : ¬ C1Uniform
```

Turing reducibility is Mathlib's oracle semantics (`Mathlib.Computability.TuringDegree`,
`RecursiveIn`).  Set-level reducibility (`≤ᵀₛ`), characteristic oracles and the finite
oracle-program syntax used for *uniform* coarse reductions come from the sibling repository
`C:\ProveIt` (library `TuringDegrees`, in `Computability/TuringDegrees/Lean`), which is required
by path in `lakefile.toml`.

The library also formalizes research report 10 (`docs/research-reports/10`): coarse classes
with no representative of least *hyperdegree*, and the failure of Martin's cone theorem for the
coarse degrees.  See "Report 10" below.

## Build

```sh
# once: share ProveIt's package cache instead of re-downloading and rebuilding Mathlib
powershell -Command "New-Item -ItemType Junction -Path .lake\packages -Target C:\ProveIt\.lake\packages"
lake build
lake env lean CoarseDegrees/Audit.lean     # prints the axioms behind each main theorem
```

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

The two routes share no admitted statement, so `¬ C1` is obtained twice, once from a single
admitted theorem (HJKS 4.2) and once from two others.  `Audit.lean` confirms that everything
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
```

| File | Content | Status |
|---|---|---|
| `BudgetForcing.lean` | disagreement sets of strings, hybrids; `Budget`, `countingBudget`; the forcing `Cond 𝔅` (copy extensions, padding, one-bit reserve); abstract decision systems `DecSys`; `bridge_step`, `bridge`; Rasiowa–Sikorski chains; `exists_generic_pair` | proved |
| `Hyper.lean` | `Sigma11In`, `HypIn`, `Hyp`, `HRed` (Kleene normal form); `HypIn.of_setTuringReducible` (proved); `not_setCoarseEq_of_ext`; `exists_hyp_minimal_pair`; `tRed_graph`; `exists_no_least_hyperdegree`; the square-root budget forces density zero | proved from **2 admitted** classical facts |
| `Cone.lean` | `LeastClass` and its invariance; density estimates for joins and halves of descriptions; the block code and its computability (`computable_log2`); relatively 1-generic sets exist (`exists_oneGenericRel`); `exists_least_above`, `exists_nonleast_above`, `no_cone_theorem` | proved from **3 admitted** facts |

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
| `blockCode_decode` | every coarse description of `𝓘(A)` computes `A`: HJKS, Section 2 |
| `OneGenericRel.core_le` | HJKS, Theorem 4.2, relativized to an oracle |
| `OneGenericRel.not_coarselyComputableIn` | JS, remark after Proposition 2.15, relativized to an oracle (the unrelativized statement is proved in `GenericDensity.lean`) |

Caveats.  `cohen_forcing_package` is a repackaging, made for this library, of theorems that
the sources state separately and in their own language (ramified formulas, the structures
`𝓜(ω₁^CK, G)`); its docstring says how each clause arises, but the packaging itself has not
been checked against the sources, and the report quotes those facts from memory.  The last two
statements are relativizations of published theorems rather than the published statements
themselves.  Theorem 1.5 is formalized for the nonuniform coarse degrees and with the witness
`𝓘(Z) ⊕ X`, `X` 1-generic relative to `Z`, instead of the report's `J(h) ⊕ A`; the report's
witness needs the relativized minimal-pair theorem of the synthesis, which is not formalized.

Not formalized from report 10: the relativization of Theorem 1.1 to an oracle `Z` and
Corollary 1.3 (every hyperdegree is an unattained infimum); Theorem 1.4 (dyadic codes, failure
of hyperarithmetic compactness, the ordinal invariant), which needs a jump operator and the
relativized Jockusch–Schupp criterion; Theorem 1.5(a) (`𝒜` is `Π¹₁`), the uniform cones, and
the statement about the Martin measure.

## What is not formalized

The stronger witness theorems of the synthesis are not formalized: the prefix-density metric and
the exact-pair theorems (Section 4), the jump-cone spectrum of the dyadic codes (Section 6), and
the reservoir and one-bit-reserve constructions (Sections 7–8), which would make `not_C1`
independent of HJKS.  The cheapest of these is the dyadic-code construction; it needs the
relativized limit lemma and a jump operator, neither of which is available in Mathlib or in the
Lean side of `C:\ProveIt`.  The spectrum identity (synthesis, Theorem 3.1) and the block-code
characterization (Theorem 3.6) are also left for later.  `no_least_of_two_witnesses` (Lemma 2.4)
is proved and is the entry point for any such witness construction.

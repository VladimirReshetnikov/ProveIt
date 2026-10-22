# rho8 by condensed detachment

`rho8 a b c u = ((c → u) → a) → ((a → c) → (b → c))` is Łukasiewicz's single
axiom for the implicational calculus. The dominated calculus grants it only
when `u` is below `a`. One 58-step derivation now supplies both calculi in the
[checked phase-thirteen Lean proof](../verification/k215/simplification/phase13/README.md).

The [generic core](../../../../Lean/BusyBeaver/ZFC/DominatedImplication.lean)
assumes only modus ponens, the restricted rows, reflexivity of `below` and
closure under insertion into either implication operand. It derives every
unrestricted row, composition, lifting, K, Peirce and S, with no Lean axioms.
The [unrestricted adapter](../../../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean)
sets `below` to `True`; its public basis theorems call the same core. Its
Tarski proof remains verbatim, including the original rho6 use for ex falso.
The two files total 18,243 bytes / 401 lines instead of 42,454 bytes / 811 lines.
`DomRho8.lean` remains the exact numeric adapter.

The maintained regeneration route is the
[self-contained producer](../generate_dominated_implication_lean.py). It reads
an [attributed raw Lean proof](../verification/k215/simplification/phase12/upstream-merge/inputs/raw58-DominatedImplication.lean)
as pinned inert data, checks all explicit MP instances and relation guards,
then inlines the two single-use goal lemmas. It does not import or execute the
research renderer. From this directory, check the maintained files with:

```sh
python3 -B ../generate_dominated_implication_lean.py --check
```

The current [ancestry input](derivation_core.txt) is the six-goal derivation
`4141248e…`, introduced with the shared core in `3a7a61ee97`; `49e99c5b7c`
inlines its two goal aliases. The previous three-goal input `f0a2e60d…` is
preserved in Git and the preceding checkpoint. The explicit raw Lean bodies,
rather than an executed search or renderer, are the maintained inference-audit
input. See the [status note](PROVEIT_STATUS.md) for actual checks and boundaries.

The other derivations remain research history:

- [derivation.txt](derivation.txt): 52 steps using the numerical truth code,
  originally proposed for numerical Lean and Rocq renderings.
- [derivation_luk.txt](derivation_luk.txt): a separate 56-step unrestricted
  derivation of K, Peirce, composition and S, superseded by the shared core.
- [rocq-proposal](rocq-proposal/README.md): attributed source proposals and their
  historical focused-build reports. The maintained Rocq checkpoint is unchanged.

Each ancestry row records a formula, its two premises and side conditions.
The [research renderer](generate_domrho8_cd.py) computes unifiers and explicit
instances. The [search](search) contains the original condensed-detachment
prover and hint-deletion tools. They are preserved as source data and were not
executed for the maintained adoption. Their historical command examples remain
recoverable in Git; the checked source and reproduction route are identified
above.

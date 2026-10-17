# Fixed arithmetic graphs for the original numerical constructors

`ArithmeticCode254.lean` extends the exact Cantor adapter with fixed bounded
Sigma0 graphs for the four original base4 constructors and one complete axiom
payload branch. Every graph is a parameter-free arithmetic `Semisentence`,
proved correct in every IOpen model; no standardness or full PA assumption is
added. The actual `Code254` definitions are unchanged.

The generic operation is `tagged(k,a,b)=4*cantor(a,b)+k`. Tags0/1/2/3 give
`wim`/`wel`/`wal`/`weq`. The graph exposes the Cantor value through a witness
bounded by the output. Both inputs are at most their constructor output, so
the same bound supports nested fixed constructor circuits, including zero.
The package also proves the literal polynomial bound

```text
cantor(a,b) <= (a+b)*(a+b+1)+b,
tagged(k,a,b) <= 4*((a+b)*(a+b+1)+b)+k.
```

These bounds are packaged in Foundation's polynomial-bounded function API.
All four generic functions are identified on every natural input with the
live `Code254` functions, with the same fixed graph formulas transferred to
the actual implementation. The truth alias `wim(0,0)=0` is retained.

The implemented axiom circuit is exactly

```text
rho1(a,b) = wim(wal(a,wim(weq(a,b),1)),1).
```

This is the original relative-falsity convention, with F=1. Its three auxiliary
constructor values are bounded by the final formula value. The graph for the
successful checker output adds one to that formula value. `row3Def` further
decodes the literal Cantor payload and represents

```text
rho1(first(payload),second(payload))+1.
```

The all-natural adapter uses the actual recursive `Cantor.ofNat`. This is the
unconditional rho1/tag3 **payload branch**, rather than the whole proof-code
parser: the outer code0 guard, twelve-way selector, remaining eleven branches
and history lookups are not implemented by this module. Payload0 is included;
it is distinct from invalid complete proof code0.

Foundation's ordinary composition API at positive hierarchy levels does not
remove the need for bounded witnesses at Sigma0. Its bounded-composition API
also permits formulas with model parameters. A definability instance alone
does not exhibit the fixed parameter-free blueprint needed by the complete
checker. Here the formulas are explicit and their witness bounds are proved.
In particular, output domination cannot simply be applied to a rejected MP
row whose output is0 while its intermediate formulas may be large. The full
row still needs its exact comparison graphs or independent intermediate bounds.

The197-line module and stored audit pass pinned Lean4.32, with29 named axiom
reports and27 generic/all-natural callers. Only `propext`, `Classical.choice`
and `Quot.sound` occur; the new source has no warnings. The independent
source review confirms the arithmetic/model scope and literal code matching.

This Foundation/Mathlib-dependent module uses the separate arithmetic check
lane, without changing the Std-only core runner or umbrella:

```sh
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_code254.py \
  --dependency-root /path/to/existing/built/ProveIt \
  --core-evidence Computability/BusyBeaver/Research/ZFC/results/code-tuple-order-integration-verification.json
```

The checker imports the maintained Cantor checker helpers. It freshly checks
`ArithmeticCantor` and its stored audit first, then this module and its audit,
serially in one temporary cache. That gives56 named probes and47 callers in
total. The ten project dependencies of the live `Code254` are matched to the
successful core evidence; the pinned Foundation checkout and built Mathlib
providers are explicitly reused. No dependency is rebuilt or downloaded.
`--core-cache` supports a relocated matching core cache; repeated
`--library-path` overrides automatic read-only built-library discovery.

The [verification record](results/arithmetic-code254-verification.json) records
exact sources, objects, commands, reused dependencies and both fresh audit
stages. These are numerical graph theorems, not all11 fixed templates, a
represented12-case row/history evaluator, PA-internal proof/trace correctness,
ZF/ZFC finite-proof transport or a smaller machine. No transition changed.

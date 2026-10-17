# A functional subset-closure alternative: a negative compiler result

The alternative below has a short ordinary calibration to ZF without
Foundation or Choice, but its measured complete theory row is larger in the
retained compiler. It is not a machine improvement. The proof in this note
is ordinary mathematics; no Lean calibration, numeric frontend theorem,
blank initialization certificate, or binary runtime simulation is claimed.

Write `Sub(x,a)` for `∀z (z∈x → z∈a)`. For every first-order matrix
`R(x,y,p̄)`, with any finite tuple of parameters, consider the instance

```text
EB(R) := ∀x ∃b ∀y (R(x,y,p̄) → y=b)

EB(R) → ∀a ∃C [
  ∀x y (((Sub(x,a) ∨ x∈C) ∧ R(x,y,p̄)) → y∈C)
  ∧ ∀y (y∈C → ∃x R(x,y,p̄)) ].
```

On a nonempty domain, `EB(R)` is equivalent to partial functionality of
`R`. An empty fiber can use any object as its bound. The displayed
antecedent writes `R` only once, whereas the usual partial-functionality
formula writes it twice. Let `T` be Extensionality, ordinary Union, and
all these instances. All occurrences of equality here are native logical
equality.

## Ordinary same-model comparison

`T` has the same nonempty models as ZF without Foundation or Choice,
including Power Set and functional Replacement. These are actual
first-order schema instances, rather than a postulate about all external
relations. The forward argument uses only the matrices described below.

For any formula `θ(y,p̄)` whose satisfying objects are subsets of an object
`a`, use `R(x,y) := (x=y ∧ θ(y,p̄))`. This is partial-functional. The
instance at seed `a` produces exactly the `θ` objects: every such `y` is
an active input because `y⊆a`, and the global support clause excludes all
other outputs. This yields an empty object, every literal singleton
`{t}` using bound `t`, and every Power Set using `θ(y) := y⊆a`.

For Pairing use
`R(x,y) := (x=a ∧ y=b) ∨ (x=b ∧ y=a)` at seed `a`. The input `a` is
active by reflexivity of `Sub`, so `b∈C`; closure then gives `a∈C`.
Every supported output is either `a` or `b`. The relation remains
partial-functional when `a=b`.

For partial Replacement on `A`, let `ρ(x,y,p̄)` be partial-functional
on `A` and use

```text
R(s,y) := ∃x (Sing(s,x) ∧ x∈A ∧ ρ(x,y,p̄)),
Sing(s,x) := ∀z (z∈s ↔ z=x).
```

Any singleton input has only one decoded member; hence this `R` is
partial-functional. For every `x∈A`, its existing singleton is a subset
of `A` and is therefore an active input at seed `A`. Closure and support
give exactly `{y : ∃x∈A ρ(x,y,p̄)}`. Taking
`ρ(x,y) := x=y ∧ ψ(x,p̄)` gives full Separation. This derivation neither
collects arbitrary witnesses nor infers Collection from Replacement.

Pairing and the explicit Union axiom form every successor
`s(x)=x∪{x}`. Extensionality makes this a total functional relation. Its
closure instance at an empty seed gives `s(∅)∈C` and closes `C` under
successor. The set `C∪{∅}`, formed by Pairing and Union, is inductive.
This is ordinary Infinity, without using recursion to obtain it.

Conversely, `EB(R)` implies the usual subset bound: if an output equals
`b`, it is a subset of `b`. The existing ordinary ZF proof of
subset-seeded positive supported closure therefore supplies every
displayed instance. The current Lean theorem
[`PSCCalibration.psc_of_zfAxioms`](../../Lean/BusyBeaver/ZFC/PSCCalibration.lean)
already proves that stronger subset-bound schema for actual `Form`
matrices. Extensionality and Union are present in the comparison theory.
This identifies the ordinary theory; it does not discharge the separate
Foundation/Choice consistency comparisons or a coded proof translation.

## Fixed compiler measurement

The driver
[`functional_subset_closure_experiment.py`](functional_subset_closure_experiment.py)
reuses the public Wade backend at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3` through the existing attributed
recovery and theory-emission tools. It retains the full original GEN and
eight logical/equality rows, base-four formula constructors, both atomic
vacuity rows, the local fresh-label gate, and the original gate tail.
It does not remove equality logic or compare fragments of different
logical engines.

| Theory row | Theory constructor macros | Decision states | Framework states | Total working states |
|---|---:|---:|---:|---:|
| Ext + point-seeded subset-bound PSC control | 76 | 255 | 62 | 317 |
| Ext + subset-seeded subset-bound PSC | 82 | 258 | 62 | 320 |
| Ext + Union + equality-bound subset PSC | 110 | 284 | 63 | 347 |

Each variant additionally retains the same 88 logical-prefix and 19
vacuity macros. Symbolic execution checks that its constructor word
rebuilds the exact intended theory AST. The measured controls have
633, 639, and 693 named transition rows respectively; they have not been
turned into complete literal blank-start machines or given initialization
and runtime certificates. The fixed-slot emitter's uniform freshness,
matrix-renaming, and calibration obligations remain separate.

The driver also exhaustively compares each theory AST with its direct
finite semantic specification on every irreflexive relation of domain
size one or two, for every relation truth matrix: 66 cases per variant,
198 total. It checks `EB` against partial functionality in those cases.
These are capture and formula-construction regressions, not finite
evidence for consistency strength.

Reproduce without writing generated tables into the repository:

```sh
uv run --no-project python -B \
  Computability/BusyBeaver/Research/ZFC/functional_subset_closure_experiment.py \
  --output /tmp/zfc-functional-subset-closure
```

The recorded run is in
[`results/functional-subset-closure.json`](results/functional-subset-closure.json).
It establishes that this direct whole-row encoding loses 27 states to the
subset-bound subset-seeded control in this fixed layout. It gives no
lower bound for other encodings, grammar searches, or theory choices.

# Integration contract and proposed call sites

## Scope of the delivered code

The package is standalone. It has not been applied as a patch to the repository
and has not been tested with the entire current upstream environment.
Only the `WordArena.rules` protocol was inspected and mirrored in an exporter.
The corresponding adapter test uses the independent compatible local arena;
it is **not** a run of the production `WordArena` implementation.

The generic formula reduction is complete mathematically, but the package does
not contain a general singly exponential existential-real solver. Exact
`Resolve` queries are provided as reference input, not as a certified complexity
implementation or a proof-carrying UNSAT interface.

## A. Fixed-seed Wirtinger entry point

1. Validate the original PD and that it represents one classical knot, using the
   maintained trusted front end. Construct signed crossing relations
   `(over, under_in, under_out, sign)` with consistent orientation conventions.
   The local braid fixtures do not supply a complete PD parser.
2. Run `find_small_seeds(n, crossings, max_attempts=...)`. A found certificate is
   checked with `verify_profile`. Exhaustion is inconclusive; `NOT_FOUND` also
   has no knot-type implication. The theorem uses an exhaustive allowance of
   at least `n*(n+1)//2`, not the default cap of 10,000 for arbitrary n.
3. Call `compile_seeds`. It retains every original crossing relation, substitutes
   every derived generator, and leaves precisely the original seed meridians.
   Duplicate seed declarations and tampered degree witnesses are rejected.
4. With one seed, the verified knot group is cyclic, giving an unknot certificate.
   With two seeds, invoke `dihedral.solve`, then `dihedral.verify`. Convert
   `EXISTS` to nontrivial and `NONE` to unknot only at this verified call site.
5. Share the caller's deadline and work policy. A timeout or cap must preserve
   the old fallback. Do not refill a budget after converting representations.

The search can be prototyped before a costly homology fallback. Its placement
relative to the existing group search is a measurement question. Run paired
complete-query ablations, including failed searches and replay.

## B. Existing compressed group-search endpoint

The inspected WordArena exposes:

```python
arena.rules[0] is None
arena.rules[node] == ('t', signed_generator)
# or
arena.rules[node] == ('c', earlier_left_node, earlier_right_node)
```

The public research exporter can be called after **independent upstream replay**:

```python
from su2budget.slp import export_word_arena
from su2budget.degrees import greedy_cap
from su2budget.multivariate import compile_formula

presentation = export_word_arena(
    arena, relator_roots, surviving_generators,
    meridians=False,  # SAFE DEFAULT after unrestricted generator changes
    label="verified compressed group endpoint",
)
choice = greedy_cap(presentation, cap=16)
formula = compile_formula(presentation, choice.checkpoints)
query_text = formula.wolfram()
```

These names `relator_roots` and `surviving_generators` are caller-owned values;
no uninspected production function or event API is presumed here. The exporter
checks and renumbers live terminals but cannot establish that the producer's
transformations preserved the original knot group.

For a verified endpoint with two actual meridian generators, use the integer
backend instead. A Whitehead-transformed generator having exponent sum +1 or -1
is **not**, on that basis alone, a meridian. Supply and replay an explicit
meridian-conjugacy proof, or keep this branch disabled.

## C. Before production promotion

Run the full upstream suite, with the optional topology dependencies actually
used by that suite. Test PD orientation conventions, multi-component rejection,
certificate/input binding, deadline propagation, and combined old/new resource
caps. Include the two unsafe integration counterexamples from the article.

For general real feasibility, accept only an exact Boolean or a verified exact
certificate; an unevaluated symbolic expression, a floating-point residual,
or `UNKNOWN` is not an answer. Do not assume a general CAS command has the
singly exponential complexity of the theorem's specific existential algorithm.

Test the old/old control and old/new complete recognition pipelines on identical
inputs and resources. Count earlier-stage successes separately. Never advertise
the algebraic microbenchmark ratios as whole-recognizer speedups.

# A bounded affine-port and local-rewrite scout on complete86

No lower operation count was found. The declared family produces **874 distinct complete DAGs**; its minimum is **86=48M+38A**, with the same polynomial, exact degree179, nineteen positive witnesses and ordinary positive input as the authenticated [first-root parent](complete86_factored_first_root.md). This is a finite negative result, not a lower bound for arbitrary circuits, coordinate changes or universal representations.

The [standalone checker](complete86_affine_port_scout.py) and [deterministic receipt](complete86_affine_port_scout.json) read pinned bytes and execute no imported compiler. The parent is the actual normalized first form of `complete86_factored_first_root.json`, not the separate87-operation ordinary-strong form. All compiler-numeral restrictions and the complete positive-domain theorem remain those of that parent. There is no new external horizon or input decoder.

## What was already covered

Before selecting this family, the following earlier notes were read: the multiplication-only shared-coefficient census; the joint main/input norm scout; discriminant shears; strong-norm compositions; auxiliary-ordinate translations; the independent-gamma period analysis; and the joint strong/auxiliary factoring census. Their note bytes are pinned in this receipt. In particular, `complete86_joint_strong_auxiliary_scout` was already committed at `dd496b9b6`; its `/tmp` source, receipt and note match the repository copies. Its292,320-choice family is not rerun here.

The present new target is the shared affine evaluation of the main and input roots, followed by one explicitly specified local algebraic move anywhere in each resulting complete source. Some individual local identities also occur in earlier families; this packet does not describe every enumerated schedule as a novel mathematical identity.

## Six paid joint-root schedules

Use the actual source ports

```
H = a4m5 = 4a+3,
A0 = D1 = X+ac,
B0 = exponent_partial = W+a*kappa,
u = rho*H, v = sigma*H, w = (rho+sigma)*H.
```

Here `A0` is not the discriminant, which the source calls `A`. These are explanatory computed ports: their entire prerequisites are retained and paid whenever live. The required roots are

```
D = A0+u+v = A0+w,
mu = B0+u.
```

The six seeds are exactly the following schedules. Brackets specify paid evaluation order; multiplication of any nontrivial fixed coefficient is charged.

| Seed | Main root | Input root | Complete cost |
|---|---|---|---:|
| original | `A0+w` | `B0+u` |86=48M+38A|
| distributed left | `(A0+u)+v` | `B0+u` |86=48M+38A|
| distributed right | `A0+(u+v)` | `B0+u` |86=48M+38A|
| through input, left | `(mu+(A0−B0))+v` | `B0+u` |87=48M+39A|
| through input, right | `mu+((A0−B0)+v)` | `B0+u` |87=48M+39A|
| recover rho product | `A0+w` | `B0+(w−v)` |87=48M+39A|

Thus sharing `rho*H` explicitly ties the parent's2M+3A joint block. Recovering that product from `w−v`, or expressing the main root through the input root, introduces an additional addition in these schedules.

## Exact finite local grammar and full accounting

From each seed, the helper includes the seed itself and applies **one** of these moves at one reachable gate:

- Reassociate a two-level addition/subtraction tree. Its three signed terms are permuted, and both bracketings are generated when the first term has positive sign; the signs are implemented by binary addition/subtraction, with no free unary negation.
- Reassociate a two-level product among its three operands.
- Distribute multiplication over a binary sum or difference.
- Factor a sum/difference whose two immediate terms have an identical multiplicative operand; a lone term may use the already-constant factor1.
- Replace a difference of two literal squares by the product of their sum and difference, or replace an immediate conjugate product by the difference of squares.

There is no repeated rewrite search, arbitrary linear-circuit enumeration, unit-premise substitution, new coordinate, or uncharged intermediate. Exact commutative common-subexpression reuse, integer constant folding, zero/one identities and dead-gate pruning are applied to the **whole** source. The same pass leaves the original at86. Binary `0−x` remains a paid subtraction. Every candidate is checked for literal closure, the complete free-port set, live gates, M/A counts and the final eight-factor product-minus-one evaluation.

| Seed | Distinct complete sources within seed |86 gates|87 gates|88 gates|89 gates|
|---|---:|---:|---:|---:|---:|
| original |142|43|77|22|0|
| distributed left |143|44|77|22|0|
| distributed right |144|45|77|22|0|
| through input, left |153|0|48|83|22|
| through input, right |153|0|48|83|22|
| recover rho product |147|0|48|77|22|

The882 within-seed records reduce to874 distinct complete sources across all seeds. The generator emits1,300 local move instances before duplicate complete sources are removed. There are127 distinct best sources, all48M+38A. The receipt saves all six complete seeds, the ordered census hashes, hashes of all127 best sources, and one complete best source. Replaying the helper regenerates every candidate.

## Polynomial proof and domain preservation

Each seed's two root substitutions is expanded exactly at its computed-port cuts. Each local move is also checked by exact sparse coefficient expansion. When two proposed cut ports overlap structurally, the helper expands the dependent port as needed rather than pretending they are independent. There are295 checked cut identities in total, including the twelve seed-root identities.

Substitution of an identical polynomial into a DAG preserves every downstream expression. The emitter performs only the stated constant and commutative identities. Consequently every one of these874 complete outputs is exactly the parent's entire polynomial over the integers, rationals, or any commutative ring. This proof preserves each original norm factor and the complete finalizer; no sign-recovery or positivity argument is added. The parent's uniform exact degree179 and complete positive zero set transfer immediately.

As supplementary checks, each within-seed source is evaluated on four positive integer, four signed integer and four rational assignments. Together with the two separate transformations below, the receipt records10,608 complete output comparisons. These are off-zero algebra checks, not constructed universal halting witnesses. Twelve private source-byte mutations are rejected by the strict provenance reader.

The exact gap identity

```
(q−1)*u+(u−Z) = q*u−Z
```

is separately checked after expanding the actual `q=repunit+1` port. Its complete source still costs86 because the shared `u−Z` port remains needed elsewhere. Its complete source is included in the receipt.

## The unproved complement coordinate is not a new bound

The original supplied `F` has exactly one literal consumer, `q_minus_F=q−F`. Replacing `F` by a supplied positive `complement_u` and aliasing that consumer removes one addition, producing a syntactic85-gate expression with nineteen coordinates. The receipt includes that expression **only as an unproved lead** and checks the all-value signed graph identity

```
F = (Bm1*Jrep+1)−complement_u.
```

To transfer the parent's positive zero theorem, one must prove `complement_u<q` at every complete new positive zero before invoking that theorem. This scout establishes no such result and no full-zero counterexample. Its positive off-zero example restores `F=−1`, demonstrating only that positivity is not an unconditional property of the coordinate map. The old positive-F packing inequalities cannot simply be reused after removing their hypothesis. Thus neither85 operations nor a new represented input language is certified here.

Supplying an independent `gamma=rho+sigma` instead of `sigma` is a different previously studied unproved lead; the [period analysis](complete75_independent_gamma87_period.md) already identifies the missing reverse positivity condition. It is not promoted or rerun by this scout.

## Reproduction

Python's standard library is sufficient; no historical author suite is invoked. Run from any directory, using the directory containing the pinned WIP dependencies:

```sh
python3 complete86_affine_port_scout.py \
  --root /path/to/native-stream-queue \
  --expect complete86_affine_port_scout.json
```

`--output /path/to/new.json` writes a fresh deterministic receipt. Optimized `-O` execution is rejected, and saved JSON comparison is recursively type-sensitive. This is a standalone research CLI, not a general hostile-packet compiler API. The existing86/179 bound and all other established frontier points remain unchanged.

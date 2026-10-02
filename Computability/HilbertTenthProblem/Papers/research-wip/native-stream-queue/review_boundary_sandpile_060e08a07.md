# Independent review: linear boundary transport and no borrowed firings

**The mathematical claims are sound within their stated polynomial/field witness domains. One concrete mode-validation defect in the linear compiler was reproduced and repaired in a separate patch. No semantic or high-level domain defect was found in the sandpile compiler.** Both reports carefully distinguish their unbounded finite-support witnesses from the fixed finite scalar tuples required for an ordinary universal Diophantine equation.

The complete TeX articles, source-audit notes, READMEs, all four Python files, supplied exports and manifests were read. Original archives remain unchanged. Safe extraction used relative, nonduplicate, nonsymlink archive entries into private directories. No repository or Git changes were made by this review.

## Pins and replay evidence

| Archive from intake `060e08a07` | SHA256 | Files |
|---|---|---:|
| `Linear_Boundary_Transport_Research.zip` | `7b2b3505fe36d9f01777bd198742cc1206f1232e0951964d1ee30681c6c5e096` | 11 |
| `no_borrowed_firings.zip` | `390c4c9a6dbe9a7701de8e0b6689a21d60b35c577aa11a9977989c088a8d0d45` | 16 |

Every original member hash is recorded in `review_boundary_sandpile_060e08a07_members.json`. The linear TeX hash is `f775a0baef8a2df4d8880bc757fd9b36c3fce620bbbe8c39d9528e90a6ab4105`; the sandpile TeX hash is `38a539137d4a2decbebf3c973c21d6576ddcc6d36ba91f9b0c59cdc2f8aa1d2f`. The independent helper pins the following four source members before any imports:

| Source | SHA256 |
|---|---|
| Linear `code/boundary_transport.py` | `6e35bbf8d574651d644bd0de728d02cd5569b668bf4bcb23d12f10ba4438f248` |
| Linear `code/verify.py` | `85b9fab3229edae30fea94b66e01ad95762d3286939d51f7706657e3b99cbb96` |
| Sandpile `sandpile_certificates.py` | `2e1d8c20678a1bfcec352c9dc047cc1ab8afb3dd93b3559f0ddad2977baf0519` |
| Sandpile `verify.py` | `c8bbf4ceb38e484f1fbfa9d912201cdc562aab1e83a05bc5eea20c3e7c77c7ea` |

After reading the code, I ran these four entrypoints from their private package roots:

```sh
python code/verify.py
python code/boundary_transport.py
# In the sandpile package:
python verify.py
python sandpile_certificates.py
```

All passed. Linear replay reproduced exactly 32,502 checks, including 169 programs, 3,042 simulation instances and 1,352 finite-box systems. All eleven original member bytes were unchanged, including the regenerated report and three exports.

Sandpile replay reproduced 43 dissipative graphs, 4,855 inputs, 305,620 candidate odometers, 3,839 stable-balance candidates, 290 compiled witnesses and 6,865 rank assignments. The complete example remains 34 variables, 40 residuals and a degree-four polynomial with 201 monomials. The 3D avalanche remains 19 fired sites, 49 total topplings, maximal odometer 19, maximal rank 2, and 57 normalized exceptional field sites. All original members were unchanged except `verification/results.json` and `verification/results.txt`, where only `python` and `elapsed_seconds` differ. These two metadata fields must be removed for portable report comparisons. All supplied `SHA256SUMS` entries match the immutable archive.

## Actionable linear compiler finding and repair

`code/boundary_transport.py:161`, `:171`, and `:233` accept arbitrary `clocked` values. The history constructor uses truthiness, but the compiler and residual function also use `int(clocked)`. This produces incompatible semantics outside exact Booleans.

For `p = Program((Instruction('HALT'), Instruction('TEST', 0, 0, 1)))`, compile source `(0,0,0)` with `clocked=0.5`. The returned system has a truthy `clocked` attribute and permits Z in its declared sorts, but `int(0.5)=0` removes the clock from its transition equations. Both main witnesses `(1,0)` and `(1,7*Y^3)` extend to accepted certificates: the second adds a disconnected cycle. Thus a truthy advertised clock mode has lost uniqueness. Separately, `clocked=2` rejects the halting transfer witness returned by `history(..., clocked=2)`, because the compiler advances Z by two and the history constructor advances it by one.

This is an API validation defect, not a counterexample to the article's correctly stated True/False theorems. The repair `linear_boundary_exact_boolean_guards.patch` adds explicit exact-Boolean checks to `history`, `residual`, `compile_system`, and the analogous `enforce_sorts` switch in `LinearSystem.evaluate`. It changes no arithmetic construction for supported modes.

Patch SHA256: `6c566f21fe7e37c7cd5d6dd78a3bccd3c072d166856b31cac5741dc272ffb3be`. Patched compiler SHA256: `a77ae4cf4412435f06d5fe331bca2d46f655d00c1c5bc0abed8d91b2ad1b03b1`. Apply only to a private extracted copy:

```sh
patch -p1 < /path/to/linear_boundary_exact_boolean_guards.patch
python code/verify.py
```

The patched author suite still passes all 32,502 checks and regenerates byte-identical examples and validation JSON. Independent regression tests reject 36 malformed mode calls and preserve both legitimate Boolean modes. The same 36 bad-mode calls are rejected under `python -O`, because the guards use explicit exceptions.

## Linear boundary transport: theorem and scope audit

The unclocked finite-support transport theorem is valid over any nonzero commutative coefficient ring. A component-sum functional excludes a one-basis source in a nonhalting component. A nonzero kernel coefficient has a nonzero predecessor in finite support; tracing predecessors forces a directed cycle, and determinism prevents a path from leaving that cycle. This gives exactly the reported cycle-constant kernel, even with negative coefficients or zero divisors.

Clocking makes the full operator injective by coefficient recursion, and a one-monomial coefficient-one source has the forced binary history. Infinite power series always admit the formal history; finite support supplies the halting condition. The unique boundary split uses injectivity of multiplication by an indeterminate, which remains valid over rings with zero divisors. The actual compiler has q+d equations in q+2d polynomial unknowns, with the claimed omitted-coordinate sorts and at most two signed monomial occurrences per unknown. Scalar row tagging requires every witness to omit W; dropping that condition would change the problem.

The energy and Hilbert-space claims also check out: integer nonzero residuals give the exact gap one; the finite rational taper has energy 1/(N+2); clock layers force any exact Hilbert solution for a nonhalting basis source to have infinite squared norm. The operator has bounded indegree, dense range, and nonclosed range when a nonhalting source exists. No finite-dimensional convex optimization undecidability follows. The one-counter excursion/cycle argument is a valid decision procedure for the stated machine-generated subclass.

The instruction set really includes the CM2 convention: successful decrements may jump, zero branches can advance, and out-of-range halting can be replaced by an explicit terminal state. The primary source distinguishes this convention from weaker decidable two-counter variants. The fixed universal interpreter is an existence-level dependency here; neither its numerical table nor an ordinary scalar input loader is provided. [Dudenhefner, Definition 2 and Theorem 6](https://drops.dagstuhl.de/storage/00lipics/lipics-vol228-fscd2022/LIPIcs.FSCD.2022.16/LIPIcs.FSCD.2022.16.pdf).

The transferable point is a unique finite-support history representation and an explicit account of its boundary restrictions. Its q+2d count does not pay for scalar encoding of polynomial coefficients, exponents, support, or those restrictions. The support is exactly runtime-sized before compression, and no computable input-only bound exists for a fixed universal source family. No numerical ordinary Diophantine operation saving is established.

## Sandpile certificate: theorem, domain and universality audit

The support-burning converse correctly uses the maximal positive layer of `u-u*`, together with integrality and row dominance of the undirected Laplacian. It excludes borrowed firings without requiring a chronological firing sequence. Necessity correctly permits negative intermediate balances in the upper-stabilizer subtraction argument. Restricting the burning set to the proposed fired support is essential. The second local rank inequality forces earliest parallel burning and removes arbitrary delays, making all ranks and gadget helpers unique.

All natural-domain signs in NZ, GE and masked inequalities are correct, including comparisons with `r-1=-1` at inactive vertices. The full compiler counts distinct unordered adjacent pairs, not edge multiplicity: 11n+12m natural witnesses and 12n+16m residuals. Its exact degree is four since the quartic top part is a nonzero sum of squares. The signed false root using negative masked slacks is correctly disclosed and rejected by `Certificate.vector`/`evaluate`. `Poly.evaluate` is intentionally an unrestricted algebraic evaluator and is not advertised as that domain guard.

The no-firing exterior halo proves an actual global finite stabilization when all input defects lie in the cube and the remaining exterior is stable. An unsuccessful small cube proves neither nontermination nor lack of a larger witness. `compile_periodic_cube` enforces this input class; the lower-level arbitrary callback explicitly puts the infinite exterior obligation on its caller. The normalized field verifier checks all possible affected sites: exceptions, their neighbors and input defects. Outside this finite set, the prescribed tails solve the local equations identically. It checks natural values and rejects redundant whole-tail rows. The radius is absent from the normalized witness, so padding does not produce multiple field witnesses.

The radius/cardinality noncomputability arguments and the conditional quadratic height barrier are valid. The 47-field/60-residual theorem in 3D is a difference-polynomial statement on finite deviations from specified periodic tails. It uses 59 local scalar witness slots, whose neighbor copies are linked by the field interpretation. It is not a 47-variable ordinary polynomial, nor a single-fold MRDP result.

The primary sandpile source supports the correct yes/no orientation: finite total activity occurs precisely for a halting simulated machine, using lazy initialization. Its circuit background uses stable 4/5-chip gates and wires, with finite added inputs; the periodic-plus-finite stable-background class in this report is appropriate. This is the global finite-activity theorem, not merely vertex prediction or local activity. No end-to-end numerical universal sandpile layout is included. [Cairns, Sections 2, 5.2.3 and Theorem 3](https://arxiv.org/html/1508.00161v2).

## Verified canonical projection available for follow-up

The review helper performs an exact substitution into every residual of the actual emitted finite-graph compiler:

```text
u_v = z_v + alpha_v
k_v = e_v + beta_v
r_v = z_v + e_v + beta_v.
```

Delete the three residuals labeled `active.value`, `later.value`, and `rank` at each vertex. On this restoration graph, `rank` is the zero polynomial, while `active.value` and `later.value` become exactly the respective retained inactive-slack residuals. Conversely, those inactive equations in any parent zero force these linear definitions. The retained coordinates therefore give a complete zero-set bijection, over integers and over naturals; in the natural case all three restored coordinates are automatically nonnegative.

The resulting counts are **8n+12m witnesses and 9n+16m quadratic residuals**. The analogous field schema has **44 fields and 57 local residuals in 3D**. On arbitrary supplied tuples on the restoration graph, the parent SOS equals the new SOS plus

```text
sum_v [((1-z_v)*alpha_v)^2 + ((1-e_v)*beta_v)^2].
```

Thus this is zero-set equivalence, not an off-zero polynomial identity. The sparse-source checker states the independent section/inverse proof explicitly and verifies all 292 duplicated-row identities and 146 zero-row identities across 51 actual compiled graphs, 306 complete off-zero corrections, and 43 natural-zero section/inverse round trips. It retains degree at most two for every residual and preserves the parent's canonical uniqueness. A maintained transfer would still need strict packet guards, formal public interfaces, and an explicit charged arithmetic schedule. Fewer field variables do not guarantee fewer operations: removing u and r causes neighboring field expressions to read additional z/alpha/e/beta fields. No gate saving or improvement to the 87-operation bound is claimed here.

An independent additional row linearization is also available: NZ value differs from `x-a-z` by the retained inactive residual; GE difference differs from `x-y-p+q+1-B` by `(1-B)p-Bq`. This preserves complete zero sets while retaining those inactive rows, but shared-expression gate accounting must be done before calling it an operation saving.

## Portable independent checker

`review_boundary_sandpile_060e08a07.py` exposes `verify(linear_root, sandpile_root, patched_linear_root=None)` and restores its temporary import names afterward. It has no permanent scratch-source dependency. The receipt is `review_boundary_sandpile_060e08a07.json`.

```sh
python review_boundary_sandpile_060e08a07.py \
  --linear-root /path/to/original-linear-package \
  --sandpile-root /path/to/original-sandpile-package \
  --patched-linear-root /path/to/patched-linear-package \
  --output /tmp/review_boundary_sandpile_060e08a07.json
```

Independent checks pass for 398 literal arity/sparsity forms and signed monomial-transport identities, 1,194 modular identities, 20 rational taper cases and five nonhalting spill rejections. The two malformed-clock failures are reproduced on the original source. Sandpile checks cover 51 graphs including closed components, 1,263 independent single-firing simulations with 165 detected state cycles, 78,492 candidate odometers, 1,653 stable-candidate support checks, 306 complete source comparisons, the projection checks above, the complete expanded quartic export, 113 scalar/interface guard rejections, 188 field-coordinate rejections, and three nonconstant periodic empty-field cases. The optional patched-source branch adds 36 mode guard rejections and both supported Boolean modes.

Finite tests supplement the reviewed all-value arguments. None of these results is a Lean proof, a materialized universal sandpile instance, or an ordinary fixed-arity scalar compression of polynomial/field witnesses.

## Repository replay

The [archive replay wrapper](replay_boundary_sandpile_060e08a07.py) authenticates
all27 members, extracts temporary copies, runs all four original author entry
points and both patched linear entry points, compares preserved exports and the
independent receipt. It recovers missing incoming archives from the pinned Git
arrival. Run `python replay_boundary_sandpile_060e08a07.py` with assertions enabled.
Only Python version and elapsed-time metadata are ignored in the two sandpile
validation reports; mathematical data and all other original bytes are checked.

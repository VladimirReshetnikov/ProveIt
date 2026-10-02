# Fewer residuals for the bounded one-fallback reaction certificate

The trace quartic in Part XIII of [Canonical Diophantine certificates](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex) can retain every natural witness and its complete natural zero set while reducing the residual count from

\[
(5d+5R+1)T+d+1
\quad\text{to}\quad
(3d+R+2)T+d+1.
\]

Here `d` is the number of species, `R` the number of reactions (exactly one of priority zero and all others of priority one, each with two distinct unit reactants), and `T` an externally fixed horizon. The universal source network has `d=61`, `R=62`, giving **247T+62 residuals instead of 616T+62**, with the same **308T+61 natural witnesses**. All retained residuals have degree at most two; the final sum of their squares has degree at most four.

This is a bounded compiler improvement in a different cost measure. It gives no new straight-line operation count, no uniform fixed-arity polynomial in variable `T`, and no improvement to the project's 87-operation universal polynomial.

The [executable](reaction_priority_residual_projection.py) imports the delivered [reaction compiler](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/11-reaction-fallback-reaction_compiler.py) without editing it. Its complete SHA-256 is pinned. The [receipt](reaction_priority_residual_projection.json) includes all generated ledgers and source hashes. This packet supplies ordinary mathematical proofs and finite exact checks, not proof-assistant verification.

## 1. Exact parent and coordinate scope

The parent is the actual `trace_certificate` function in the delivered compiler, including its initialization equations, zero helpers, enabling flags, selector equations, priority and idle checks, all species updates, and the final halt-species equation. Its source hash is

```text
f9c0e8730fd9f0a712c476e18c8d70bb9758e0d4d3fc9b26e1afdcfc8d42cbc3
```

Every variable ranges over `N={0,1,...}`. For source checking, each initial species count is an independent natural parameter `in_species`, and the final halt-species count is the natural parameter `eta`. This interface includes every legal compiled initialization by specialization. Equality of the complete natural zero sets holds even for arbitrary initial markings; inherited deterministic simulation and unique-trace claims apply only to the report's legal invariant markings. For acceptance, specialize `eta=1` as in the parent.

All witness coordinates are retained. There is no projection that forgets a coordinate, existential choice of a replacement tuple, or change in the supplied witness values. The filename's “projection” refers to reducing the residual list.

The executable has five explicit source-machine fixtures: the report's literal universal and doubling machines, immediate halt, one increment followed by halt, and the report's fabricated-zero-branch example. It also reorders the reactions so the unique low-priority rule may occur at a different index. The proof applies to any network with the parent interface; the guarded public builder accepts these source-derived fixtures. `checked` compares the entire packet, parent and new polynomials, witnesses, parameters, network data, and metadata against its canonical build. Mutation of an uninspected metadata field is rejected as well. The comparison is recursive and type-sensitive: replacing integer coefficients by numerically equal floats or booleans, or lists by tuples, is rejected. The guard suite includes the false floating-point equality of `2^100+1` and `2^100`.

## 2. Two equations suffice for the natural zero indicator

At a marking coordinate `x`, the report introduces `z,b` and four equations:

\[
z(z-1)=0,\quad xz=0,\quad x-(1-z)(b+1)=0,\quad zb=0.
\]

Keep only

\[
x-(1-z)(b+1)=0,\qquad zb=0.\tag{1}
\]

If `z≥2`, the first equation makes the natural number `x` negative, because `b+1>0`. Thus `z∈{0,1}` follows without an explicit Boolean residual. If `z=0`, the equations force `x=b+1>0`, with the unique `b=x-1`. If `z=1`, they force `x=0` and `b=0`. Hence (1) has precisely the same natural solutions as the four parent equations, and both deleted equations follow.

An optional equal-count variant keeps instead

\[
x-b+z-1=0,\qquad zb=0.\tag{2}
\]

The first residual in (1) is the first residual in (2) plus `zb`. Therefore the two systems are equivalent whenever their shared second residual vanishes, even over integers. Their common equivalence to the four-row parent requires the natural domain. For example, `(x,z,b)=(-1,2,0)` satisfies both reduced systems but violates the parent's Boolean residual.

The optional variant is selected by `linear_zero=True`. It makes one residual affine but changes neither the number of witnesses nor the number of residuals. No circuit-operation saving is asserted for it here.

## 3. Natural selector sums already enforce one-hot choice

At each time, retain

\[
\sum_{j=0}^{R}s_j=1,
\]

where `s_R` is the idle selector. Every `s_j` is natural, so exactly one is one and the rest are zero. Delete the `R+1` separate Boolean equations `s_j(s_j-1)=0`. This inference is false over unrestricted integers and is not used there.

## 4. One guarded nonnegative sum enforces all firing conditions

Retain every enabling equation

\[
e_j=(1-z_{u_j})(1-z_{v_j}).
\]

The reactant species are distinct and have unit multiplicity in the parent network. Section 2 has already restored the exact zero indicators, so `e_j` is Boolean and equals the actual enabling predicate.

Let `l` be the unique low-priority index. Replace the `R` eligibility, `R-1` priority, and `R` idle residuals by the single quadratic residual

\[
F=\sum_{j<R}s_j(1-e_j)
  +s_l\sum_{j\ne l}e_j
  +s_R\sum_{j<R}e_j.\tag{3}
\]

Every term in (3) is nonnegative on the retained natural zero locus: selectors are natural, and the enabling variables are Boolean. Therefore `F=0` holds exactly when every original firing-condition residual is zero.

More explicitly, if an ordinary reaction is selected, the first sum requires it to be enabled. If the selected reaction is low priority, the second sum excludes every enabled high-priority reaction. If idle is selected, the third sum excludes every enabled reaction. These are precisely the parent permitted-reaction semantics, including deadlock padding. Multiple high reactions may be permitted at an arbitrary marking; each actual selector remains a distinct witness. The optimization adds no uniqueness claim outside the simulation invariant.

For `R=1`, the high-priority sum is empty and equals zero; the same proof applies. At `T=0` there are no firing rows to change.

The final polynomial retains **the square `F²`**. It is not valid to add `F` unsquared to the other squared residuals using this proof. For example, `s_j=1,e_j=2` makes an eligibility summand negative away from the enabling zero locus. We use conditional nonnegativity only after all retained equations have been established. The executable checks a complete counterexample: take the one-step immediate-halt network (its only rule is the fallback), all initial species counts equal to one, and its canonical one-step witness; then change the enabling flag from one to two. Every retained residual stays zero except the enabling residual, which is one, and `F`, which is minus one. The correct sum of squares is two. Replacing `F²` by `F` would make the polynomial zero on this false natural witness. This fixture was supplied during independent root review.

## 5. Complete zero-set equivalence and exact count

Let `P_old` be the parent sum of squares and `P_new` the sum of squares after the changes above. At a natural zero of `P_new`, each retained residual vanishes. In order:

1. Section 2 restores all four parent zero-gadget equations.
2. Retained enabling equations give the original Boolean enabling flags.
3. The selector sum restores the deleted selector Boolean equations.
4. Section 4 restores every parent eligibility, priority and idle equation.
5. Initialization, species updates and the final halt-species equation were retained verbatim.

Thus `P_old=0` on the identical complete supplied tuple. Conversely, every natural zero of `P_old` satisfies the reduced zero gadgets and has each old firing penalty zero, so it satisfies (3), every retained equation, and `P_new=0`. These identity maps preserve every fibre over the parameters, including its full cardinality.

The new time row consists of:

| Residual family | Count per time |
|---|---:|
| Two zero-indicator equations per species | `2d` |
| Original enabling equations | `R` |
| Selector sum | `1` |
| Combined firing condition (3) | `1` |
| Original species updates | `d` |
| Total | `3d+R+2` |

Add `d` initialization equations and one endpoint equation. The exact saving is `(2d+4R-1)T` rows. The witness count is unchanged at `(3d+2R+1)T+d`; it includes the original marking, zero-helper, enabling and selector variables.

For the universal network the saving is `369T` rows. At `T=0`, both have 61 witnesses and 62 affine residuals. For positive `T`, both variants have quadratic residuals and quartic sum-of-squares bounds. No equality of the two polynomials away from zero is claimed; the executable checks an explicit natural assignment where their values differ.

## 6. Validation

Run from the repository with an ordinary Python 3 interpreter:

```text
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/reaction_priority_residual_projection.py
```

`--output PATH` writes a receipt to the selected path. It does not rewrite the imported report or its delivered data.

The checks include all 72 generated source/metadata/ledger variants: five machines, relevant first/middle/last low-priority positions, horizons 0,1,2, and both zero-gadget versions. Further tests use actual source polynomials at horizons 0,1,3,8, including initial halts, blocked increments, final halt padding, wrong endpoint values and fabricated zero branches. The local guard audit exhausts every Boolean enabling vector, every selected/idle choice and every low index for 1–8 reactions. Full source-polynomial adversaries include arbitrary markings outside the invariant and mutations of zero helpers, positive-part helpers, enabling flags and selectors.

The generated receipt records exact case counts. Its finite checks supplement Sections 2–5; they do not prove the inherited universal-machine theorem or remove the external horizon.

Independent review, 2 October 2026: the proof, source and counts passed without an unresolved finding. A fresh replay exactly matched the committed receipt. Separate checks covered 312 source forms, every low-priority position, 14,580 arbitrary-marking/selector cases (5,103 accepted and 9,477 rejected), 1,000 local natural tuples, 4,092 firing-condition cases and 36 malformed numeric-type inputs. The reviewer verified that the full zero-set argument restores zero indicators and enabling bits before using nonnegativity, and that the finalizer retains the square of (3). These checks have the bounded scope stated above.

## 7. Arithmetic-complexity consequence

This reduction removes redundant equations and combines a family of nonnegative conditions once their local semantics have been restored. It is a reusable compiler simplification, with an explicit domain and dependency order. Residual count is not the project's straight-line addition/multiplication objective; a combined residual can have many terms. A straight-line compiler, degree/operation tradeoff, and global unbounded-history encoding would all require separate accounting.

The current universal 87-operation unit-product construction is unchanged. The finite conservative reaction network also still requires existentially unbounded fuel to recognize universal halting, and the bounded trace family's arity grows with `T`.

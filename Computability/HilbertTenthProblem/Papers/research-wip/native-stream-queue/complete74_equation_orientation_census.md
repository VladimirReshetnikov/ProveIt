# Equation orientations of the three complete74 comparison sources

The actual raw30, positive22 and signed20 sources have complete SOS realizations of exact degrees **20,48,64**, respectively, without changing their74-operation comparison costs, supplied witness counts or number of equations. Their SOS costs remain **130,106,100**. These are degree improvements for the specified comparison interfaces; the established universal74 comparison/86 polynomial operation bounds remain unchanged.

The [standalone helper](complete74_equation_orientation_census.py) emits all56 full comparison and SOS DAGs in the [receipt](complete74_equation_orientation_census.json). It reads authenticated source/proof artifacts and imports no historical Python. The family combines the actual [symmetric74 sources](complete74_factored_first_norm.md), their proved [asymmetric74 transfer](complete74_asymmetric_scale_transfer.md), three available defining-equation reversals, and the protected auxiliary substitutions already described in the older [complete75 degree note](complete75_auxiliary_degree_tradeoffs.md). Applying those substitutions to these actual74 interfaces is checked here; the auxiliary identity itself is not new.

| Source | Positive witnesses | Equations | Complete SOS operations | Symmetric minimum degree | Asymmetric minimum degree |
|---|---:|---:|---:|---:|---:|
| raw30 |30|19|130=59M+71A|20|20|
| positive22 |22|11|106=51M+55A|56|48|
| signed20 |20|9|100=49M+51A|84|64|

Every comparison DAG costs40M+34A=74. These minima concern exactly the56 sources defined below. They are not unrestricted arithmetic or degree lower bounds, a maintained universal compiler API, or replacements for the separate19-witness operation/degree catalogue.

## 1. Scope and unchanged positive coordinates

Fix one of the three actual parent interfaces. Write X=wq³ for its symmetric scale or X=wq for its asymmetric scale, and Y=sq³ in both cases. Fixed compiler numeral ports have degree0; the ordinary input and each supplied witness have degree1. All supplied witnesses are strictly positive, including in the source named signed20. Computed intermediates may be signed.

Within either scale, every rewrite below keeps exactly the same supplied coordinates. Its defining comparisons remain present and its full SOS pays every residual subtraction, square and final addition. The parent and child have the same comparison zero set over any commutative ring. Consequently their SOS zero sets agree over the reals, and in particular on the entire positive integer grid. No new positivity restoration lemma is required for these orientations.

Between scales, the separate asymmetric74 theorem supplies the positive-zero bijection w_new=q²*w_old on valid fixed compiler slices. Its native proof establishes inverse divisibility before invoking the symmetric parent theorem. We do not infer that inverse from these local equation rewrites or from off-zero numerical tests.

## 2. Reverse the available defining equations

In raw30, a,c,k are independent supplied coordinates. Two independent switches reverse their existing defining rows without changing the residual polynomials:

| Binding | Original paid rows and comparison | Reoriented paid rows and comparison |
|---|---|---|
| E=XY=a−Y | E=X*Y; a_rhs=E+Y; a=a_rhs | E=a−Y; a_rhs=X*Y; E=a_rhs |
| kY=c−eta | kY=k*Y; c_rhs=kY+eta; c=c_rhs | kY=c−eta; c_rhs=k*Y; kY=c_rhs |

Each switch exchanges one multiplication and one addition/subtraction. Both private right-hand endpoints have no source consumers in raw30. Every downstream use of E or kY takes the new computed value. The exact defining residual identities are

```
a-(XY+Y)=(a-Y)-XY,
c-(kY+eta)=(c-eta)-kY.
```

On either retained equality, the changed value agrees with its original producer. The raw k port remains supplied k throughout; k=eta+zeta is not imposed off zero. Reversal of the E binding changes its uses in the first norm and first-index equation, not just a selected occurrence.

In positive22, c is computed and the positive witness phi remains. Reverse the input-gap comparison:

```
old: pell_gap=index_rhs+phi; compare c=pell_gap;
     use index_rhs for kappa in the input norm/root.
new: pell_gap=c-phi; compare pell_gap=index_rhs;
     use pell_gap for kappa in the input norm/root.
```

The retained index_rhs=u+delta*Delta stays paid. Its only other consumers are difference_multiple and kappa2, and both are redirected. The binding residual is again identically unchanged: c−(index_rhs+phi)=(c−phi)−index_rhs. This reversal is unavailable in signed20 because that supplied gap and its comparison were removed in its parent. We do not reintroduce phi or use a hidden equation there.

## 3. Two protected auxiliary substitutions

For each source retain both comparisons

```
T2=K,      U=V,
T2=(i*c²)², K=Delta*(f²-1), U=j*c-r, V=o*f-c.
```

The auxiliary residual is originally

```
Raux=T2*(U²-y²)-(1-y²).
```

Choose independently whether its coefficient is T2 or K and whether its root is U or V. The source already computes all four quantities for the retained strong and linear comparisons. Reordering their rows topologically costs nothing; no gate is silently removed or added. This is the same protected substitution mechanism as the older complete75 note, now applied to the literal74 comparison schedules.

The exact change D in this one residual is

```
root only:       -T2*(U-V)*(U+V),
coefficient only:-(T2-K)*(U²-y²),
both:            -(T2-K)*(V²-y²)-T2*(U-V)*(U+V).
```

The resulting change of its square is D*(2Raux+D), not zero identically. Sparse integer coefficient expansion checks all three formulas. Retaining both protection equations is essential to the zero-set conclusion.

For the whole source, the checker first proves that every chosen protecting residual is identical before any substitutions. It then substitutes the monic defining equalities from Section2 and the two retained auxiliary equalities, and proves equality of every residual and the complete SOS. Each auxiliary right-hand side is independent of both auxiliary cuts. Thus the protected locus is the same in both directions, and all remaining residuals agree on it. This proves two-way zero equivalence; it does not assume that one source already vanishes in order to justify a converse.

## 4. Exact degrees, uniformly in the compiler

The source guards authenticate all relevant producers. Gate propagation supplies upper bounds; the main and input Pell norm cancellations are expanded explicitly. The receipt records every residual bound and the nonzero templates for all dominant residuals. A real sum of squares cannot cancel its maximal homogeneous pieces, so twice the largest attained residual degree is the exact SOS degree.

In raw30, Y has degree4. Original E has degree8 symmetric or6 asymmetric; reversed E=a−Y has degree4 and leader −Y. Original kY has degree5; reversed c−eta has degree1 and is a nonzero linear form. With L=E*(kY), the first norm residual is L(L+k)−tau²+1 and has degree twice that of L. The four choices have these residual degrees:

| E reversed | kY reversed | Symmetric first residual | Asymmetric first residual |
|---|---|---:|---:|
| no | no |26|22|
| no | yes |18|14|
| yes | no |18|18|
| yes | yes |10|10|

The original auxiliary coefficient T2 has degree6; K has degree4. Both roots U,V have degree2. Its residual degree is therefore10 with T2 or8 with K. Other raw residuals have upper degree at most10 when both bindings are reversed. The first norm supplies a nonzero degree10 leader in every such case, including the tie with T2. This proves the raw20 minimum in both scales.

For positive22 and signed20, let c_* denote the leading form of c:

```
c_*=(eta+zeta)*s*Bm1³*Jrep³.
```

Thus c has degree5. The computed a has degree8 symmetric or6 asymmetric, with nonzero leading form a_*=w*s*q_*⁶ or w*s*q_*⁴, where q_*=Bm1*Jrep. These are nonzero for every admissible Bm1>0, independently of the other fixed compiler numerals. The auxiliary roots U,V have degrees6,5 and leaders j*c_* and −c_*. T2 has degree22 and leader i²*c_*⁴; K has degree18 symmetric or14 asymmetric and leader a_*²*f². Hence:

| Coefficient | Root | Symmetric auxiliary residual | Asymmetric auxiliary residual |
|---|---|---:|---:|
| T2 | U |34|34|
| T2 | V |32|32|
| K | U |30|26|
| K | V |28|24|

The leader in each case is the indicated nonzero coefficient leader times the square of the root leader. Terms involving y have lower degree. The retained strong residual has degree22, since T2 dominates K.

Write H=4a+3, Delta=a²+H, G=gamma*H. The complete main residual expands to

```
X²+2Xac+2XG+2acG+G²-Hc²-1.
```

Its upper degree is22 symmetric or18 asymmetric. In the actual input cone, with computed root mu=W+a*kappa+rho*H, the entire norm residual expands to

```
W²+2aW*kappa+2rho*W*H+2a*rho*kappa*H
  +rho²H²-H*kappa²-1.
```

The helper proves both identities by exact coefficients in independent formal atoms and verifies their actual source producers. With the old kappa=u+delta*Delta, the input residual has exact degree42 symmetric or32 asymmetric, with unique leader −4delta²*a_*⁵. With reversed kappa=c−phi, available only in positive22, it has exact degree22 symmetric or18 asymmetric, with unique leader8rho*a_*²*c_*.

The first norm in both projected forms has degree26 symmetric or22 asymmetric. With reversed kappa and both auxiliary choices on their right-hand sides, the positive22 auxiliary residual dominates at28 symmetric or24 asymmetric. This gives exact SOS degrees56/48. Signed20 retains old kappa, so the input residual forces degree84 symmetric; at asymmetric scale the original auxiliary residual gives68, and either auxiliary switch lowers the maximum to32, giving64. In the root-only asymmetric switch, auxiliary and input residuals tie at32; their squared leading forms cannot cancel.

These arguments establish the exact degrees for every admissible fixed compiler slice. The additional56 modular univariate expansions execute each entire finalized polynomial and attain its claimed degree. Those deliberately chosen scalar constants are algebra diagnostics, not valid compiler witnesses and not the basis for uniformity.

## 5. Finite inventory, provenance and replay

For each scale the raw30 family has2 E choices ×2 kY choices ×2 auxiliary roots ×2 auxiliary coefficients=16 sources. Positive22 has2 kappa choices ×2 roots ×2 coefficients=8. Signed20 has2 roots ×2 coefficients=4. Both scales give56 sources in total, with6,656 live complete-polynomial gates and856 retained residual identities. Every supplied input and paid instruction is live.

The helper compares the asymmetric baseline literally with the separately proved asymmetric74 packet. It retains the parent interface, reconstructs every finalizer, recounts M/A operations and saves all sources. Parent-only transformation and exact-degree metadata are removed from the current packets; their orientation and degree records describe the new source. No new mutable-packet evaluator or compiler API is advertised. The command-line interface authenticates all ten declared dependencies each time; it supports deterministic receipt output and exact saved-receipt replay, and rejects optimized Python execution.

```
python3 complete74_equation_orientation_census.py \
  --root /path/to/native-stream-queue \
  --expect complete74_equation_orientation_census.json
```

Only Python's standard library is needed. The fixed-source family and the mathematical arguments above are the scope of this result. Arbitrary equation orientations, product finalizers, new witness projections and interactions with other substrate compilers remain outside the census.

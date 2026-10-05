# Independent review of the hierarchical U9 history250 successor

**PASS. No correction requested.** The source and proof support the
claimed complete alternative universal polynomial on the inherited valid
shifted U9 program slices:250=130M+120A operations,43 strictly positive
witnesses, ordinary positive input, four fixed program parameters in the
default interface, and unbounded existential computation time. The second
interface retains the separate fifth fixed duration-bound parameter.
The degree claim is an upper bound926, not an exact degree or optimum.

I read the complete author proof and helper inertly, both complete
250-row source definitions, and their parent-relative changes. I also
read the complete tail-quotient253, product-scale253, initial-bound254,
history-units260, shifted-offset258 and actual U9 program/input notes.
The older slope-class and four-tile theorem files were authenticated as
dependencies; their full proofs were not freshly audited here. The
earlier lane128 proof had been read fully in my preceding scoped audit.
This review checks transfer of the accepted compiler and native theorem,
not external machine-simulation literature or formal proof-assistant
verification from first principles.

## 1. The signed mask has the required pretyping bounds

Write G=S1+S2, G'=S0+S3 and pstar=(b−1)J. The five paid mask rows
give exactly J+P(J+pstar G). Under the still-signed equation
P=pstar+epsilon, this becomes

    J+P*(G'+(1−epsilon)G)+P^2*G.

The extra2G at epsilon=−1 is real. The author's numbered Remark1
retains the false unconditional simplification and its961 versus901
counterexample. I independently checked that the proof never substitutes
epsilon=1 during native pretyping or degree estimation.

From the positive global sum, b>=32 and either unit sign,
P>=6, J>=1 and J<=P/6. Every controller coefficient is at most3J,
hence at mostP−2. Thus Mtree+2<P^3; together with Mb<2P^3 this
absorbs all possible physical-mask carries before any binary semantics.
The unchanged range expression remains nonnegative at height1 and less
thanP. Combining the three regions gives H0,M0,Z<P^8 and the required
positive truth-field margins. No history transport or dyadic assumption
is used to establish these bounds.

These verified scalar hypotheses suffice for the retained local
tail-quotient253 native argument. The normalized strong equation supplies
its ordinary strong hypothesis through the proof-only Delta*i map;
both positive ratios, index and coupled-linear factors remain present.
The tail bound yields XY>2r+3 before X>r is known. The later population
argument excludes the negative joint index. I checked the native source
interfaces and this dependency order; no earlier complete compiler theorem
requiring already typed history lanes is invoked prematurely.

## 2. Dyadic recovery precedes the tree and chronology

The actual paid scale is q=q0*b*P^8. Once the local native theorem makes
q dyadic, all positive integer factors, including b and P, are dyadic.
The inherited Mersenne argument excludes the negative history repunit
sign, yielding P=b^t with t>=1. The low/high split and the top tags2AND1=0
are now legitimate, followed by the physical, controller and range splits.

The three controller relations give successive borrow-free complements:
G subset J, S0 subset J−G and S1 subset G. Since the four nonnegative
selectors sum to J, their complements are exactly S3 and S2. Thus the
four original one-hot selectors are recovered. The same three-selector
pack already occurs in the physical slope mask, so its reuse is paid
in the actual source rather than assumed as a free interface.

**Review remark 1 (retained invalid flat-selector deletion).** Merely
deleting the fourth flat test is false: J=5, S0=S1=1, S2=0, S3=3
has the required sum, and the first three selectors are subsets of J,
but S3 is not. The proposed tree correctly rejects it because S0=1
is not a subset of G03=4. This is the explicit counterexample retained
in the frozen author's Section7; the present numbered remark makes the
rejected shortcut's status explicit. It is separate from the author's
numbered Remark1 about the signed mask's off-zero identity failure.

All remaining chronology premises are then exactly those of the parent:
bounded digit updates, the positive upper transport sign, bounded zero
runs of the true shifted input sentinel and its minus-two alternative,
the recovered initial bound, terminal bound and forbidden101 exclusion.
Height1 is allowed in pretyping and ruled out only by the typed initial
digit. The physical counter remains128n because the unchanged shifted
program parameter E'=E−1 still bounds the fixed tape length.

The forward and reverse completion arguments are therefore sound on
the same valid program slices. They preserve31 supplied witnesses and
forget precisely the12 private joint `and__` witnesses, rebuilding those
by the full prescribed native extension at the changed scale. Canonical
X=2^(2r+1), q<r and Z0<S<r ensure positivity of the tail bound. This is
equality of existential projections, not a complete-witness bijection or
an off-zero identity of the two output polynomials.

The inherited U9 ordinary-input theorem consequently supplies every
recursively enumerable positive-input set using fixed effective program
parameters. Neither a bounded-horizon simulation nor the nonuniversal
shortcut-Collatz example is used to infer this universality. Malformed
positive program tuples retain the parent's explicitly limited scope.

## 3. Complete static source and manual degree checks

My newly written checker reconstructs both full250-row sequences from
the pinned253-row parents using independently specified edits. Each
contains238 literal parent rows, seven edited rows and five new rows,
after eight parent rows are removed. All500 resulting rows match the
author exactly. Every operation and supplied port is live; all11 fixed
numeral roles,43 witnesses, program interfaces,16 factor definitions and
the complete18-row finalizer tail are retained. Both source ledgers are
130M+120A; removing the final subtraction leaves249=130M+119A and one
comparison. Private joint-witness consumer checks support the projection
claim above.

I derived the degree bounds directly from the displayed producer cones,
without evaluating or propagating degrees through a saved array. In the
joint core q,F3,X,Y,a,c,Delta have upper degrees14,13,41,15,56,16,112.
The all-ring cancellation with D0=X+ga(4a+3), degree57, gives main-norm
degree129. The other joint factors have bounds322,73,178,57,57.
Crucially, the emitted Mtree has degree4; its degree is not reduced by
substituting the on-zero repunit relation.

The unchanged geometry factors independently give14,40,9,24,6,6,
total99. The remaining mask and history factors give4,2,2,3, total11.
Thus the full product-minus-one degree is at most

    129+322+73+178+57+57+99+11=926.

## 4. Fresh evidence and frozen pins

The fresh reviewer compares52,360 nonnegative selector compositions
through J=31 with an independent per-bit occupancy oracle, obtaining
3,125 partitions. It also checks8,280 handwritten scalar pretyping
contexts, including4,140 negative-sign and2,760 height-one cases.
Those diagnostics supplement the all-size proofs above; they are not
full U9 inputs or native Pell witnesses. Normal and optimized reviewer
runs produced byte-identical receipts before freeze.

Author files:

- MD `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330`
- PY `ba178e2a17ab8f9d05dcb7db7fdf903b9a6f71926df1d44e92e40898f337912f`
- JSON `d2f1ae7870cb8ec295d4401a8e9c951047f0e92cf2b6e6f4bb723c6b483f1ebf`

Reviewer evidence, under the distinct stem
`review_neary_woods_hierarchical_history250_pascal`:

- PY `9fe5014aabd2bf591745cbd3a5153c6c1b62c29bf7274c1f830b52714bf05b43`
- JSON `8aced8adad6dcb2536b390d9e9375a1c540f423853d27e6b1fa0fafb22f91c8f`

The reviewer JSON authenticates all ten declared author dependencies and
both source canonical hashes. Only my newly handwritten structural and
scalar checker was executed. No author, archived, committed or frozen
predecessor helper was executed or imported; no saved source array was
numerically evaluated, symbolically expanded or degree-propagated.
All new files were written under `/tmp`; repository and Git state were
left to root.

# Wave11 structural and direct-source review

Reviewed the complete ZIP trees at arrival commit`9a33342a03`, authenticated
against their retained inventories. No Lean compiler was invoked or repository
Lean source edited. The accompanying receipt is
`data/wave11-review-structural.json`; the read-only count fold is
`tools/review_wave11_structural.py`.

The completed `lucas_h1868/integer10.json` is a useful new unrestricted-integer
point: **10 variables,480 live binary operations, exact degree1,245,324**.
Its unchanged-prefix companion has481 operations and degree1,248,364.
These improve the preceding ten-integer480/481-operation family in degree;
they have a different domain from our440-operation positive-nine equation.
The direct proof-flow proposals are useful source reductions, but neither
archive supplies a measured final ordinary consistency polynomial for them.

## Lucas saturation: the new proof obligation is addressed

The new certificate replaces the factor`D²` in its old auxiliary square by
`D`, while preserving the larger interpolation modulus. With
`D=(A²-4)C²+4`, it uses

```text
E0=C²*xi, E=D*E0, E2=E0*E
F=4(A²-4)*E2+1
G=(A/2-1)*(F-1)-1, Omega=16*E
H=C+F*(B-C+Omega*y), I=(G²-1)*H²+1.
```

Here`A/2` is a supplied integer polynomial, not division in the equation.
The central identities are exact:

```text
2G=(A-2)F-A
(F-1)/(Omega*xi)=(A²-4)C²/4
(2G+2)/(Omega*xi)=(A+2)(A-2)²C²/4.
```

Evenness of`A` makes the right sides integral. Separating the pairwise
coprime positive factors`D,F,I` gives a proof-only root`d²=D`; no new
Diophantine variable is introduced. The resulting Lucas coordinate is
`4C²d*xi`. The index-separation and rank-divisibility hypotheses match the
primary external inputs: [Sun, Lemmas2.1–2.2 and Corollary2.1](https://arxiv.org/html/2609.01594v1).
The required index exceeds3,`C` is odd, and`C²` divides that Lucas coordinate.

The standalone reliability theorem **needs`|C|>1`**. The archive includes a
false-index example at`A=72,B=31,C=-1` if this hypothesis is removed.
The full equation does discharge it first: its positive guard yields
`4(C-KL)²<K²`, while the recovered source gives`|L|>=Y>256` and`K!=0`.
Hence`|C|>|K|(|L|-1/2)>1`. The subsequent Lucas-growth and residue argument
therefore uses the strengthened theorem legally. This order of implication
is essential and is present in the proof.

The completeness proof also supplies the altered residue-class interpolation;
it does not assume that rescaling an old witness preserves all classes.
Choose a matrix period modulo`4NC²d` and set`xi=u_n(A)/(4C²d)`. Then
`Omega=4d*u_n(A)`. Every prime dividing`xi` has its part of the auxiliary
period absorbed by`Omega`, so the remaining period is coprime to`xi`.
This establishes the prescribed second-witness residue classes needed by
the existing divisibility merger. I found no new mathematical gap in this
argument. Its native calibration remains an explicitly inherited ordinary
proof dependency, not a new proof-assistant or internal-ZFC certificate.

The exact480-operation count includes the certified H1868 target placement
and a retained78-step shared-power schedule. Degree attainment is checked
using the actual fixed coefficient leaves modulo primes, rather than treating
the leaves as independent symbols. Neither addition-chain optimality nor a
global simplicity minimum follows.

## Two coefficient-budget sources

The structural archive keeps the affine factors`1+jX`, with label0 a unit.
It adds a height register with multiplier
`D_i=(1+p_i)(1+q_i)+c_i`, starts it at2, and chooses the evaluation point
one larger than its final value. Its ordinary proof is sound: coefficient
bounds recover a polynomial identity, distinct linear roots recover flow,
and single-conclusion Horn flow recovers derivability. The proposed local
tradeoffs are20 witnesses/degree50,21/20,23/14, each with one bounded block.
The selector variants preserve nonnegativity and enforce a genuinely active
branch; the unused Boolean group has value1 and cannot certify a zero.

The budget-and-centering archive instead uses monic factors`X+j`, so label0
is an actual obligation discharged by its truth axiom. It respects actual
rule arity, uses`T_0=1`, the same multiplier, and`M=T_N+1`. Its coefficient
lemma correctly observes that adjacent coefficients of`(X+1)Q` sum to at
most`Q(1)`. Thus the budget bounds the signed difference by`T_N`, not
`2T_N`. The two accumulators are chosen without circular bounds: first
the finite rule list and budget, then`M`, then the obligation products.
The active binary branch reuses two scratch slots absent from its inherited
rule rows. The other branches keep their original scratch values. The
20-natural-witness degree52 local polynomial and its finite fixtures pass.

The same sharper adjacent-coefficient argument also applies to the
structural archive's affine factors. Its height register can start at1
instead of2, with the corresponding changed endpoint. This is a valid
additional mathematical refinement; it has not been applied to the archive.
It reduces witness *values*, without by itself removing a variable or gate.

Both sources remove the separate common-multiple bounded block. Neither
removes the cost of the remaining bounded universal elimination. Their four
beta outputs per step must be counted. A smaller local witness number or
degree does not settle the size of the compiled global equation.

## Actual constructor comparison with our large carrier

Our [large-carrier candidate](candidates/direct-flow-large-carrier/README.md)
instead keeps one accumulator and label bound`m`, and uses`M=(m+1)^t`.
A degree comparison first limits the actual number of nonconstant premise
factors; a strict signed-coefficient bound then makes evaluation injective.
It needs one fixed111-witness power relation, with two beta outputs per
step. It keeps the three label-bound slacks, avoiding the second trace.

The new archives are right to avoid claiming final size records. In fact,
folding the **literal delivered constructors** through the existing exact
metadata gives the following representation counts before quartic flattening:

| Whole constructor | Closed representation witnesses |
|---|---:|
| Package68,23-local degree50 source |140,639,095,370|
| Wave11 height20-local degree50 source |2,709,263,730,874|
| Wave11 selected21-local degree20 source |2,713,517,479,360|
| Wave11 Boolean23-local degree14 source |2,779,184,958,028|
| Our quartic local source with shared beta equations and power carrier |47,439,839|

These figures measure the specified existing expression-tree constructors,
not an inherent lower bound for any architecture. Four independently nested
beta graphs dominate the new height constructors; their source signed split
sizes drop from34,389,398 to8,547,454 to4,348,286, but the composed body sizes
remain about8.9billion. Consequently the local degree14 variant actually
has the largest representation count among those three literal recipes.
Our explicit quadratic remainder equations avoid those duplicated graph
trees. They can also be adapted to either two-accumulator proposal, so the
table does not establish that a power carrier is inherently better.

The practical recommendation is to retain the480-operation ten-integer
equation as a completed domain-specific improvement, and retain the budget
theorem as a promising direct-source alternative. Before selecting a new
complete direct equation, normalize its local source and share the actual
remainder equations, then count the entire finite constructor. A local20/52
number is not comparable with the finished nine-variable frontier.

## Replay scope

Full structural replay **PASS**:365 file hashes authenticated, all30 declared
commands passed in each of normal and optimized Python, and46 rebuilt
artifacts were byte-identical in each mode. Budget direct normal/optimized
checks and byte-identical local rebuilds also **PASS**. The original archive
trees were reauthenticated after these scratch-only replays.

The structural release driver authenticates its exhaustive inventory and
runs its full declared Python allowlist in isolated copies in both normal
and optimized modes, comparing all specified rebuilt bytes. The emitters
only regenerate inert, uncompiled proposal text in those scratch copies;
they never invoke Lean. The original archive trees are preserved.
The budget direct checks run normally and under`-O`; its local builder
regenerates the same literal JSON bytes. Its replay covers60,880 small rule
lists,178 exact natural branch fixtures and their budget corruptions,
46 malformed numeric certificates, four toy proof trees, and the empty,
cyclic, repeated-premise and large-base false-balance controls.
An independent additional20,440-list affine-factor test confirms the
start-at1 height refinement on labels0,1,2 through trace length3.
These finite results support the transcriptions and metadata. Universal
correctness relies on the mathematical proofs reviewed above.

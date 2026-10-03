# Independent review of the paid beta-membership interface

**PASS, no correction requested.** The frozen
[author source](eager_tree_beta_membership_interface.py),
[receipt](eager_tree_beta_membership_interface.json), and
[report](eager_tree_beta_membership_interface.md) correctly provide a local
16-gate natural suffix-membership polynomial, its 17-gate active version,
and an explicit obstruction to dropping row-code coherence. They do not
claim a complete fixed-arity Tree polynomial or a new universal operation
bound.

This review's [checker](review_eager_tree_beta_membership_interface.py) and
[receipt](review_eager_tree_beta_membership_interface.json) authenticate the
following author bytes, plus all ten literal predecessor pins:

| Artifact | SHA-256 |
|---|---|
| Author Python | `bdb27b56b8701a1e392e799e742d135a4c0f107abc987982c5eb59efe947be34` |
| Author receipt | `de8da8729d5167aa1196d374d4603dec865a9b6ae4529747afc632576dd83f7b` |
| Author report | `b7f3ef7c12f0ae0ff14cd49ec57802b06d6842bd5b30bc044397d02866a115e3` |

I read the complete new source and report, the relevant imported Tree
loader/arity passages, the actual factorial/product and bounded-universal
proof in `MRDPCore.lean`, the separate cipher-based closure wrapper in
`DiophantineTrace.lean`, and the cited 52-operation exponent component's
input contract. This is a review of the specific interface and its use of
those results, not a new Lean build or a complete audit of the surrounding
repository. The author has a bounded CLI checker and a local `build(active)`
function; there is no advertised hostile-packet compiler API to certify.

## Local source and theorem

Put `j=i+h+1` and `m=1+(j+1)b`. The three residuals emitted by the literal
source are

\[
A-D-qm,\qquad m-1-D-s,\qquad N-j-1-k.
\]

At a natural zero of their sum of squares, all three are zero. Hence
`i<j<N`, `0<=D<m`, and `A=qm+D`; this is precisely the canonical remainder
condition `beta(A,b,j)=D`. Conversely any such suffix member gives the
natural witnesses

\[
h=j-i-1,\quad k=N-j-1,\quad
q=\lfloor A/m\rfloor,\quad s=m-1-D.
\]

The modulus is positive even for `b=0`. Empty suffixes, including `N=0`
and `i>=N-1`, have no natural zero. There is no implicit assumption that
all supplied naturals are positive.

The independent checker expands every coefficient in both entire emitted
polynomials and compares all three residuals with these handwritten
formulas. Every supplied coordinate and paid gate is live. The residual
schedule costs `2M+9A`; its three squares and two additions cost `3M+2A`.
Thus the full ungated polynomial costs **16=5M+11A**. Multiplying once by a
supplied natural active port costs **17=6M+11A**. Its zero condition is
exactly `active=0` or local membership, and the term is nonnegative on
natural tuples, so it may join a sum of nonnegative terms directly.

The ungated highest homogeneous part is

\[
b^2q^2(i+h)^2,
\]

so its exact degree is six; the active version multiplies this expression
by the independent active port and has exact degree seven. The author's
claimed degree-eleven substituted local upper bound, for a degree-five
Tree target and a degree-one active expression, is consistent. It is not
a degree for the unfinished global sequence compiler. Computing Tree
codes, targets, active expressions, or the table itself is not included in
the local count.

Both domain failures are real and accurately scoped. Signed quotient and
slack values can imitate a noncanonical remainder. Even nonnegative real
witnesses can do so by taking a fractional quotient. The checker evaluates
the two exact counterexamples using integers and rational arithmetic;
neither is a theorem over the natural integers.

## Coherence and the complete Tree counterexample

The actual authenticated `N=3` pointer-product packet has eighteen retained
local/root residuals. With the supplied root `(x,y,z)=(4,0,0)`, tag three,
`u=v=1`, and two later leaf rows `(0,0,1)`, all eighteen vanish. Independent
execution of the literal parent source gives true row codes `[400,2,2]`
and root target codes `[2,2,25]`. The third forward membership fails, and
the complete parent polynomial evaluates to **279841**.

A separately encoded column `[400,2,25]` admits natural witnesses for all
nine active beta queries, including the target `25` falsely attributed to
the final row. I reconstructed that CRT column using a direct product
formula, and the actual active and target ports from the parent source;
I did not reuse the author's saved lookup assignments. Yet the five Tree
rules give

\[
\operatorname{app}(4,0)
=\operatorname{app}(\operatorname{app}(0,0),\operatorname{app}(0,0))
=\operatorname{app}(1,1)=6.
\]

The new column thus produces the claimed false result when coherence is
omitted. This is an actual failure of that shortcut, not merely an absent
proof. The separate composite-divisibility example, `(6-2)(6-3)=12` divisible
by six with no zero target, is also correct.

The general intermediate formula is well scoped. A common factorial scale
can simultaneously CRT-encode all thirteen natural row-field columns and
the fourteenth code column. Canonical remainders make the decoded rows
unique for fixed outer codes. Requiring every row's local equations and
its code equality, together with the three guarded suffix queries, recovers
actual strictly later row triples by injectivity of the natural code.
Conversely a genuine finite certificate can be encoded at a common scale.
Root accesses bind the ordinary triple. This supplies the stated bounded
universal formula; it does not itself eliminate that quantifier into a
fully counted existential polynomial.

## Existing closure results and remaining paid work

The original imported Tree report already distinguishes the external-size
family from a fixed-arity polynomial and explicitly charges the unresolved
ordinary-input translation. The cited memory-log and `N[X]` constructions
do not silently supply a scalar fixed-variable sequence lookup.

The actual `MRDPCore.boundedForall_dioph` proof uses factorial scale,
CRT-coded row witnesses and index, falling-factorial divisibility bounds,
and polynomial congruences. Its displayed encoded product expression agrees
with the new report, including the variable base and exponent. The proof
uses prime divisors of the moduli and factorial bounds to recover equalities
from congruences; the report correctly preserves these requirements.
The separate cipher wrapper also proves an existence/closure theorem.
Neither file is an exported paid Tree circuit, and no such export or Lean
rebuild is claimed here.

Likewise, the pinned 52-operation component certifies the specific positive
relation `Q=8^(32x)`. It is not a generic variable-base, variable-exponent
power primitive. The report's warning against using it as one is necessary
and correct. Compiling the whole bounded-universal row condition and the
ordinary integer loader remains additional work; the local 16/17 counts
cannot be reported as a complete universal count.

## Reproducibility and finite scope

The independent receipt records two exact full coefficient identities,
six residual identities, all 33 paid live gates, 23,328 natural assignments,
26 natural zeros with uniquely recovered index/quotient/slacks at those
assignments, 42 explicit member lifts, 864 active checks, and 27 independently
constructed CRT sequences of lengths zero through eight. It also records
the complete literal Tree counterexample and its nine counterfeit queries,
both domain counterexamples, the divisibility obstruction, exact active
flag rejection, a fresh-source copy check, and optimized-Python rejection.
These finite checks supplement the general arithmetic argument, not an
unbounded compilation theorem.

The checker authenticates all predecessor files itself and loads only the
small author helper from its authenticated source bytes to compare its two
actual local `build` outputs. It does not call author `verify`, execute a
historical compiler, reuse the author's symbolic engine, or invoke external
arithmetic libraries. Its coefficient representation, whole-polynomial
expansion, liveness accounting, CRT construction, and Tree fixture are
independently implemented.

```sh
python /path/review_eager_tree_beta_membership_interface.py \
  --repo /path/to/Proofs \
  --artifacts /path/to/author-trio \
  --expect /path/review_eager_tree_beta_membership_interface.json
```

`--artifacts` defaults to the checker directory; installed author files can
instead be read from the research directory. Only the Python standard
library is required. `--output FILE` writes a deterministic receipt, and
`--expect` compares its complete JSON contents recursively with exact types.

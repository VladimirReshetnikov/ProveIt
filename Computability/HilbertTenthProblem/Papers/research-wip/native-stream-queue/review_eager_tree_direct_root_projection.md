# Independent review of direct root-input projection

**PASS, no requested author change.** This review covers the complete
frozen [author source](eager_tree_direct_root_projection.py),
[receipt](eager_tree_direct_root_projection.json), and
[proof](eager_tree_direct_root_projection.md), with these exact pins:

| Artifact | SHA-256 |
|---|---|
| Python | `1c2b52002c04ada2187c1ef4f1e28b5d5648a8bfc7f93e540f18c86543ecbb84` |
| JSON | `31cd205ca1faed80d20e3db68e8288884243f0f1c43c5d319a4f6cfe94810c7d` |
| Markdown | `4ad2b339b67a75ce7941437a3b3edd4d70c00a35e8269daf0a340b307fa267f6` |

The independent [review helper](review_eager_tree_direct_root_projection.py)
and [receipt](review_eager_tree_direct_root_projection.json) separately pin
the complete leaf-tag parent trio. They read saved parent JSON without
executing historical Python and load only the current helper directly from
authenticated source bytes to test its APIs. The author verifier and proof
helpers are not called. My preceding leaf-tag review supplies context;
reviewer arithmetic routines are copied into this standalone checker rather
than imported from another review artifact.

The root-input substitution identifies `r0_x,r0_y,r0_z` with the existing
ordinary ports `program,argument,output`. All three ordinary ports remain
supplied. This is a local coordinate projection inside each complete finite
Tree certificate, not a new ordinary-integer loader or an elimination of
the external size parameter.

The parent has exactly three binding residuals

\[
r0_x-program,\qquad r0_y-argument,\qquad r0_z-output.
\]

Their output registers have no certificate consumers; they are individually
squared by the mixed finalizer. Substitution makes these three residuals
identically zero. Replacing each root coordinate in every remaining source
operand and deleting those three residual occurrences gives the complete
polynomial identity

\[
F_{child}(r)=F_{leaf}(R(r)),
\]

where `R` restores the three root coordinates from the ordinary ports. This
identity is all-value algebra, valid over any commutative ring. It does not
use a tag, membership, or zero hypothesis.

Restoration is unconditionally natural on every natural child assignment.
At a complete natural parent zero, every squared residual and every
integer guard `s_i(s_i-1)` is nonnegative. Therefore each binding square
vanishes, and the root coordinates equal the three corresponding ordinary
ports. Projection and restoration are inverse on the full natural zero
sets of these two immediate sources. There is no need to invoke the Tree
semantic theorem before establishing this restoration. Earlier projections
to pointer, flow, or other sources retain their original fiber restrictions.
No real-domain zero-set extension is inferred from the graph identity alone.

The certificate loses exactly three subtractions. Its finalizer loses three
squares and three accumulator additions. Thus the complete saving is
**9=3M+6A**, with three fewer witnesses. Every remaining arithmetic gate and
supplied coordinate is still paid and live. There are `N` unsquared integer
guards and `7N-3` squared residuals, hence `8N-3` accumulated terms. For
cleanup flag `epsilon`, the complete formula is

\[
M=(3N^2+81N-52)/2,\qquad
A=(3N^2+(127-2\epsilon)N-88)/2,
\]

with `12N-8` natural witnesses besides the three ordinary ports. The clean
eight-row case is **946=394M+552A**, with 88 witnesses; the clean one-row
case is **36=16M+20A**, with four witnesses.

Variable identification cannot increase total degree. In addition, setting
all remaining supplied coordinates to one indeterminate gives exactly the
same complete univariate polynomial as setting all parent coordinates to
that indeterminate: the identified ports were already equal there, and
the binding residuals were zero. Thus the parent's attained degree survives.
The actual complete specialization has degree six and highest coefficient
17 at `N=1`, and degree `10N-8` with coefficient
`8*2^(10(N-1))+2^(8(N-1))` for `N>=2`. These are exact polynomial degrees,
not degrees modulo computation equations.


The independent literal reconstruction substitutes the three aliases in
every source operand and deletes only the three identified subtraction
rows. It confirms each ordinary parent input previously had only its
binding consumer and each binding port was private to the finalizer.
It independently emits the complete mixed finalizer in the retained term
order, rather than trusting the saved ledger. A ring-expression engine
then compares every actual retained gate and both complete outputs after
the root substitution, with no residual equality cuts. The three removed
expressions cancel directly. Separate exact coefficient propagation proves
the equality of the entire univariate diagonal polynomials, not merely
agreement of their leading terms.

Handwritten complete natural zeros exercise all five Tree rules. These
include the recursive examples `app(4,0)=6` and `app(8,0)=2`, their actual
later-row triples, and dummy padding. Projection and restoration recover
each exact immediate-parent tuple. Arbitrary natural off-zero assignments
also restore naturally and preserve the complete polynomial value. Signed
integer and rational evaluations check the algebraic graph identity without
extending the computational domain theorem.

The inherited rational-witness failure remains: at one row, with
`program=1,argument=output=0,t2=1/2,a=b=t1=0`, both the child and its restored
leaf-tag parent have value zero. Actual Tree application `app(1,0)` is two.
The public integer APIs correctly reject this rational tuple. The graph
substitution preserves the parent's algebraic expression, not a new
real-witness computation theorem.

The review checks all public canonical packet APIs and both assignment maps.
The saved sizes and cleanup/signed options require exact types. Modified
sources, aliases, term kinds, metadata, wrong containers, absent/surplus
coordinates, Boolean/floating/fractional values, and negative coordinates
in natural mode are rejected. The natural parent projection requires a
complete zero and validates the forced root bindings; arbitrary off-zero
projection is not advertised as an inverse. All mutable fields and map
returns are independent copies. Every parent source/receipt/note mismatch
is rejected after a successful warmed call through all eight documented
public entry points. Optimized Python is explicitly rejected.

The saved independent run passes sixteen literal complete schedules and
sixteen whole graph identities, all 6,588 retained certificate expressions,
456 retained squared-residual identities, 72 guard identities, 48 zero
bindings, and all 7,556 paid live gates. It verifies sixteen full diagonal
polynomial identities and exact degrees; 128 whole numeric identities,
including sixteen rational cases; 48 unconditional natural restorations;
44 complete natural-zero bijections; the inherited rational boundary;
143 malformed-call rejections including 24 strict warm-pin failures; and
eighteen defensive-copy checks. These finite checks supplement the general
source identity and natural-zero argument.

Standard-library replay from any working directory:

```sh
python /path/review_eager_tree_direct_root_projection.py \
  --root /path/to/leaf-tag-parent-trio \
  --artifacts /path/to/direct-root-author-trio \
  --expect /path/review_eager_tree_direct_root_projection.json
```

Both directories default to the review helper's directory and may be the
same installed research directory. `--output FILE` writes a deterministic
receipt; saved JSON is compared recursively with exact types. No historical
suite, Lean build, unbounded array compiler or universal loader is run.
The maintained source scope is exactly the sixteen saved external
`N=1,...,8` forms, with both inherited cleanup settings. There is no global
optimality or fixed-arity universal operation claim.

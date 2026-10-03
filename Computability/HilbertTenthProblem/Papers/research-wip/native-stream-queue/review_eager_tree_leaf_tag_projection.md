# Independent complete-source review of the Tree leaf-tag projection

**PASS, no requested author change.** The frozen
[source](eager_tree_leaf_tag_projection.py),
[receipt](eager_tree_leaf_tag_projection.json), and
[proof](eager_tree_leaf_tag_projection.md) correctly eliminate the leaf tag
from all sixteen saved terminal-parent circuits. The result is a mixed
nonnegative integer finalizer, with a natural-zero bijection and an exact
polynomial correction. It is not equality of the old and new polynomials,
not an unconditional natural graph map, and not a fixed-arity universal
compiler.

The independent [checker](review_eager_tree_leaf_tag_projection.py) and
[receipt](review_eager_tree_leaf_tag_projection.json) pin these author files:

| Artifact | SHA-256 |
|---|---|
| Python | `e491a2dd852fca307d1c5f7138b078a0b815a0cea271ef05000cf001be1f6015` |
| JSON | `1f786cd77987db5892ac40b4329f7bce1b6ad3ff26aa7cf15e0a25dde21114eb` |
| Markdown | `9f6e8d07accec6eb33ee402427e7fd795ff91487174fc47248653e855447ea8f` |

The terminal parent Python/receipt/note are independently authenticated
against their existing frozen pins. The reviewer reads parent JSON and
executes no historical Python. It loads the current author module directly
from authenticated bytes to exercise its public interface, without calling
its `verify` or local proof helpers. My earlier terminal review supplies
context; no separate review or math helper is imported at runtime.

## Full correction from actual source expressions

At nonterminal row `i`, let `s_i=t1+t2+t3+t4`; at the final row use `t1+t2`,
since that parent's `t3,t4` are already absent. The old leaf tag is used only
in its private one-hot chain and its leaf-output residual. The checker
independently identifies these exact consumers and the complete additive
chains in the parent source. It also verifies the existing paid `t3+t4`
port and its evaluation order in every nonterminal row.

The child removes `t0`, reuses the active port, replaces the leaf residual
by `(s_i-1)*(z-S(y))`, and uses the unsquared guard `s_i*(s_i-1)`. All other
source rows remain literal. There are `7N` residual squares and `N` integer
guards, not `8N` squares. Their accumulation order and every multiplication
are independently reconstructed.

Define the integer substitution `R(r)` by `t0_i=1-s_i`. The independent
ring-expression engine normalizes additive coefficients and extracts scalar
signs from products; it does not expand the large membership polynomials.
It proves directly from the actual expressions that every old one-hot row
cancels, each old leaf residual is the negative of the child residual, and
all other retained residuals agree. It then proves the complete identity

\[
F_{child}(r)=F_{terminal}(R(r))+
\sum_i s_i(s_i-1).
\]

No author-supplied equality cuts, assumed tag equations, or zero hypotheses
are inserted into this proof. The identity holds over any commutative ring.
Each actual emitted guard is also matched to the displayed polynomial.

## Natural zeros, restoration, and domain boundaries

For every natural child tuple, `s_i` is an integer and `s_i(s_i-1)>=0`.
The substituted parent expression remains a sum of squares even when the
restored tag is negative. A child zero therefore forces every guard zero,
so each `s_i` is zero or one. Only then do the restored tags become natural,
and the substitution gives a complete natural parent zero.

Conversely, at a natural parent zero its one-hot equation is `t0_i+s_i=1`.
Both quantities are natural; hence `s_i` is zero or one, its guard vanishes,
and `t0_i=1-s_i` uniquely. Projection and restoration are inverse on the
full natural zero sets of these two specified sources. This does not add
unique lifts through the terminal parent's earlier existential projections.

Assigning every retained tag one makes at least one restored tag negative.
The natural restoration API correctly requires a complete child zero;
`integer_pullback` deliberately exposes the signed algebra without claiming
naturalness. Independent handwritten complete zeros cover all five Tree
rules and verify both map directions. The nontrivial examples use
`app(4,0)=6` and `app(8,0)=2`, with their complete later rows, rather than
reusing the author's evaluator fixtures.

Two complete polynomial checks confirm the precise domain restriction:

- The signed one-row parent tuple with `t0=-1,t2=2,b=1,z=1,x=program=12`,
  remaining row fields zero, `argument=0,output=1`, is an old zero; its child
  projection has value `2`.
- The nonnegative rational child with `t2=1/2`, `x=program=1`, and all other
  fields zero has output zero, whereas its restored parent has value `1/4`.

Thus nonnegativity of the integer guards does not supply a reverse bijection
for arbitrary signed parent zeros, and those guards are not nonnegative on
all nonnegative real tuples. The author note states both limits correctly.

## Complete ledger and exact degree

Each nonterminal five-addition one-hot chain is replaced by three additions
and one guard multiplication; the terminal three-addition chain becomes
two additions and one guard multiplication. The leaf multiplier stays paid.
The certificate therefore gains `N` multiplications and saves `2N-1`
additions. Removing the `N` old one-hot squares cancels that multiplication
increase in the full polynomial. There remain `8N` accumulated terms, so
all finalizer additions are unchanged.

Independent counts and liveness checks give

\[
M=(3N^2+81N-46)/2,\qquad
A=(3N^2+(127-2\epsilon)N-76)/2,
\]

where `epsilon` is the inherited cleanup flag. The natural witness count is
`12N-5`, besides the three ordinary ports. Clean `N=8` has
**955=397M+558A**, `91` witnesses, `56` residual squares and `8` guards.
Clean `N=1` has **45=19M+26A**, seven witnesses, seven squares and one guard.
Every supplied port and every paid gate remains live. No global CSE,
implicit constant cleanup, uncharged restoration, or free target-code
computation is used in the count.

Formal source propagation gives degree at most six at `N=1` and `10N-8`
otherwise. Independent exact integer coefficient propagation through each
entire emitted polynomial, with all supplied coordinates equal to `t`,
attains the upper bound. Its leading coefficient is `17` at `N=1` and
`8*2^(10(N-1))+2^(8(N-1))` otherwise. This proves exact total degrees for all
sixteen sources. The author's leading-form argument agrees: altered leaf
squares have degree at most four and new guards degree two, below the
unchanged leading squared terms. No reduction modulo tag equations enters
the degree certificate.

## Maintained interface and replay

The public source family is exactly `N=1,...,8` with Boolean cleanup.
The review checks full canonical packet guards, entire source and provenance
metadata, separate squared/unsquared term counts, assignment types and
natural/signed modes, and the zero requirements of both natural map APIs.
Missing/surplus coordinates, Boolean/float/fraction coordinates, forged
finalizer kinds, altered source rows, and wrong option/container types are
rejected. Every mutable accessor and map is independently copied. All three
parent pins are rechecked through all nine documented public entry points,
including warmed calls. Optimized Python is rejected.

The independent receipt records sixteen literal full schedules and sixteen
whole ring corrections; 504 retained residual identities; 72 actual tag
cancellations, leaf sign identities and guard identities; all 7,700 paid
live gates; sixteen exact degrees; 128 complete numeric corrections,
including sixteen rational cases; 44 complete natural zero bijections;
sixteen off-zero negative pullbacks; both domain counterexamples; 147
malformed-call rejections including 27 strict warm pins; and eighteen
copy checks. These finite checks supplement the quantified ring identity
and natural-zero argument. No historical author suite or Lean build is run.

```sh
python /path/review_eager_tree_leaf_tag_projection.py \
  --root /path/to/terminal-parent-trio \
  --artifacts /path/to/leaf-tag-author-trio \
  --expect /path/review_eager_tree_leaf_tag_projection.json
```

Both directories default to the checker directory and may be the same
installed research directory. The helper requires only the Python standard
library, writes a fresh receipt with `--output FILE`, and compares complete
saved JSON recursively with exact types. No general optimality, unbounded
array compiler, ordinary-input decoder, or fixed-arity universal bound is
claimed by this review.

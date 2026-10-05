# Endpoint-only certificates for coprime residue itineraries

A fixed finite residue itinerary can be certified without supplying any
intermediate states or division quotients: a single denominator-cleared
endpoint equality forces all intermediate residue guards when the branch
numerators are coprime to the radix. The branch selectors themselves remain
paid. This gives a fixed-horizon polynomial with 2T positive witnesses.

The simplest common-numerator specialization is cheaper and has degree
independent of T, but its point-target orbit problem is decidable. Dropping
coprimality makes even the endpoint assertion false. Consequently neither
specialization currently replaces the complete native/Pell history kernel.
This note contains a new bounded arithmetic interface, not a universal bound.

## 1. A denominator-clearing lemma, including varying denominators

Fix a word of integer affine branches

    x_(j+1)=(a_j*x_j+c_j)/b_j, 0<=j<T,

with positive integers a_j,b_j, integers c_j, and intended congruence
`x_j=r_j mod b_j`, where `c_j=-a_j*r_j mod b_j`. Assume

    gcd(a_k,b_j)=1 whenever 0<=j<=k<T.                 (1)

For integer endpoints x,y, the single equality

    (product b_j)*y=(product a_j)*x
       +sum_j c_j*(product_(k<j)b_k)*(product_(k>j)a_k) (2)

is equivalent to a chain of integer intermediate states satisfying every
displayed branch equation and congruence. No positivity claim is needed
for this algebraic lemma.

Indeed, modulo b_0 the right side is
`(product_(k>0)a_k)*(a_0*x+c_0)`. Condition (1) makes both the suffix
product and a_0 invertible modulo b_0. Thus x has the intended residue,
and x_1 is integral. Substitute `a_0*x+c_0=b_0*x_1` in (2), cancel b_0,
and apply induction to the remaining word. The converse is telescoping.
This proof covers b_j=1 and T=1; T=0 means simply x=y.

For one common radix b, it is enough that each selected a_j is a unit
modulo b. In variable-denominator systems, reducing each fraction separately
is insufficient: (1) also prohibits later numerator factors from cancelling
earlier unfulfilled denominators. Priority among overlapping branches is a
separate obligation; the lemma by itself is not a FRACTRAN first-enabled test.

## 2. A complete fixed-horizon positive polynomial

Fix b>=2 and integer tables a_r,d_r, 0<=r<b, with a_r>0,
`gcd(a_r,b)=1`, and a total positive map

    f(n)=a_r*floor(n/b)+d_r, r=n mod b, n>=1.

Put c_r=b*d_r-a_r*r. Then f(n)=(a_r*n+c_r)/b on residue r.
Fix an external horizon T>=1. Supply exactly the 2T positive witnesses
`s_0,v_0,...,s_(T-1),v_(T-1)`. The T equations

    s_j+v_j=b+1                                       (3)

force r_j=s_j-1 into {0,...,b-1}, including both endpoints.
There are no intermediate configuration or quotient witnesses.

Interpolate the a_r and c_r tables at s=r+1. Clear denominators with a
fixed positive numeral L, yielding integer polynomials P,C of degree at
most b-1 with P(r+1)=L*a_r and C(r+1)=L*c_r. Evaluate, as computed
signed registers rather than additional witnesses,

    N_0=x,
    N_(j+1)=P(s_j)*N_j+(bL)^j*C(s_j),
    N_T=(bL)^T*y.                                    (4)

On (3), N_j is L^j times the ordinary denominator-cleared numerator
after j steps. Cancelling L^T in (4) recovers (2). The lemma reconstructs
every guard. Since the actual map is total positive, all reconstructed
states are positive automatically, starting from positive x. Conversely
an actual T-step orbit supplies its unique selector pairs and satisfies
(3)–(4). The positive zero set therefore projects exactly to f^T(x)=y,
with one selector tuple for each successful pair x,y.

Let F_T be the sum of the T squared residuals in (3) and the squared
endpoint residual in (4). It has the same complete positive zero set.
The variable count is 2T witnesses, plus the two external positive inputs
x,y. Its generic degree is at most 2[T(b-1)+1].

The following literal source charges all additions, subtractions and
multiplications, including fixed-coefficient multiplications. It uses two
padded degree-(b-1) Horner evaluations per time. It omits multiplication
by (bL)^0=1 in the first update, and charges the final numeral multiple
of y. Horner zero or unit coefficients are not specially optimized.

| Complete source | M | A | Total |
|---|---:|---:|---:|
| T+1-equation graph | 2bT | 2bT | 4bT |
| Single SOS polynomial F_T | (2b+1)T+1 | (2b+2)T+1 | (4b+3)T+2 |

For the graph, an equation compares already computed registers for free.
For the SOS, each of its T+1 residuals costs a subtraction, each square
costs one multiplication, and the sum costs T additions. The source is
a family indexed by fixed b, table and T. Its numeral powers and number
of rows depend on T; these are not supplied free POWER values for a
variable-duration compiler. No bit-complexity bound is asserted.

## 3. Common numerator: a low-degree weighted selector identity

If all a_r equal one a>=2, the endpoint identity simplifies to

    L*b^T*y=L*a^T*x
             +sum_(j<T) a^(T-1-j)*b^j*C(s_j).        (5)

Here only C is interpolated. Every weight in the sum is a fixed numeral
for this externally fixed T. Their multiplications are charged; (5) is
not a promise that a variable-length weighted-digit loader is free.

Evaluate each C(s_j) by padded Horner, multiply by its displayed weight,
and accumulate from L*a^T*x. Along with (3) and the endpoint comparison,
this is a complete source. For T>=2 every weight is greater than one,
so its literal costs are

| Common-numerator source, T>=2 | M | A | Total |
|---|---:|---:|---:|
| T+1-equation graph | bT+2 | (b+1)T | (2b+1)T+2 |
| Single SOS | (b+1)T+3 | (b+3)T+1 | (2b+4)T+4 |

For T=1 omit its sole unit-weight multiplication: the graph costs
2b+2 and the SOS costs 2b+7. Both retain exactly 2T positive witnesses.
The SOS degree is at most 2*max(b-1,1), independent of T. For example,
radix two gives a quadratic fixed-horizon polynomial. No optimality of
these padded schedules is claimed.

## 4. Two limits of the apparent history simplification

**Remark 1 (nonunit cancellation gives a false endpoint).** Consider the
total positive map f(n)=n/2 for even n and f(n)=2n+1 for odd n. Its
radix-two table is (a_0,d_0)=(1,0), (a_1,d_1)=(4,3), hence
c_0=0,c_1=2. The proposed itinerary [even,odd] takes x=1 formally to
1/2 and then y=2. The cleared equation `4y=4x+4` holds, but its first
guard is false. The actual orbit is 1,3,7,15,... and never reaches 2.
Thus an endpoint-only claim without condition (1) fails as both a
witness statement and a projected orbit statement. The existing
prime-payload counter compiler has nonunit branch numerators; this
simplification cannot simply be transferred to that universal substrate.

**Remark 2 (common slope does not provide arbitrary point-target
computation).** More generally, let a,b be any fixed positive integers
and let a total positive residue-affine map have the single slope a/b:
`f(n)=(a*n+c_(n mod b))/b`. Coprimality is not required for this remark.
Its point-target orbit relation is decidable, including the case a=b.

Put C=max_r |c_r|. If a<b, choose
`H=max(x,y,1,ceil(C/(b-a)))`. The interval [1,H] is forward invariant,
so finite simulation detects y or repeats a state. If a>b, choose
`H=max(y,C+1)`. Every n>H strictly increases on every later step and
can never return to y. Simulate until y, a repeated state in [1,H], or
escape above H. These are terminating procedures, not assertions based
on a finite search cutoff.

If a=b, integrality makes every c_r divisible by b. Write
`e_r=c_r/b`, so f(n)=n+e_r. The residue evolves under the fixed finite
map r -> r+e_r mod b. Follow its finite transient and eventual cycle.
At each cycle position, the visited integers are `u+k*S`, k>=0, where
S is the net increment around that cycle. Membership of y is decided
by one linear equation for k at each position (with S=0 handled by
equality). Total positivity ensures these are the actual iterates; it
does not invalidate the finite residue decomposition. This handles
translation and periodic residue classes without a growth assumption.

The claim is specifically decidability of reaching a specified integer
target, not decidability for arbitrary acceptance predicates supplied
from outside the scalar system. Composing with a computable input loader
preserves this point-target decidability. Thus the cheap common-numerator
interface cannot by itself realize all recursively enumerable languages
with that acceptance convention.

## 5. Comparison and exact remaining obligation

The earlier generic factored one-step graph costs 4b+3, with three
positive witnesses per step. Joining T such steps using T-1 supplied
intermediate states gives 4T-1 positive witnesses; its direct common
SOS schedule costs (4b+12)T-1. The current coprime endpoint graph uses
2T witnesses and (4b+3)T+2 operations. These compare explicit schedules,
not minimal circuits; a common-numerator local table can also be optimized.

The existing `residue_affine_packed_history` packet instead already pays
an unbounded finite orbit with fixed arity, using native AND/Pell typing,
bounded digits, selected products and chronological transport. Its stated
shortcut-Collatz instance is 134 operations with 21 positive witnesses.
The current construction does not improve that fixed-arity result:
T new selector pairs and T-dependent coefficients remain. Encoding their
weighted itinerary sum in a fixed number of integer coordinates, while
certifying every selector digit and its weight, is the precise missing
loader. Ordinary multiplication of packed words introduces cross terms;
the endpoint lemma has not supplied that coefficientwise operation.

Prior-art reads were inert: complete `residue_affine_factored_counter_step.md`
(325 lines), complete `fractran_divisibility_residual_projection.md`
(230 lines), and `residue_affine_packed_history.md` lines 1–175. The
ancestor-pumping note was read at lines 1–81 for its model and stated
distinct affine-input obstruction. No prior helper, builder or saved source
array was executed or imported; no repository or Git mutation was made.

## 6. Exact pins and fresh bounded evidence

All four dependencies below are in the existing native-stream-queue WIP
directory. The hashes bind complete file bytes, while Section 5 states
the precise mathematical read scope; a whole-file hash is not a claim
to have reread every proof in that file.

| Dependency | SHA-256 |
|---|---|
| `residue_affine_factored_counter_step.md` | `60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f` |
| `residue_affine_packed_history.md` | `0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882` |
| `residue_affine_ancestor_pumping.md` | `d9d2da9a30f9d52a61ceba283e2564dcf162fbac78d685d25e29ef5e67c060e2` |
| `fractran_divisibility_residual_projection.md` | `42e9c3689e748b04c464d52ba4e55e300333d7b2f1673ab16eda3b4a979c094d` |

The separately authored standard-library helper
`residue_affine_endpoint_history_tesla_checks.py`, SHA-256
`c1d37709b691d0ac38a6ef782438f7e8343694c5bb754147ef94893381b7812e`,
builds only fresh fixed-horizon sources from the formulas in this note.
It never loads any predecessor program or source array. Its receipt,
`residue_affine_endpoint_history_tesla_checks.json`, SHA-256
`3e68460b9ad5a370a3dbddc69756024f4bd5dd653888d3dd49243baf919e1477`,
records ten complete arrays with 255 total rows, their exact ledgers,
symbolically expanded whole SOS outputs and degrees. Checks include
936 complete residue-word cases, 120 positive zeros, 160 positive
selector corruptions and 468 varying-denominator word cases. These are
synthetic component checks, not actual universal-compiler histories.

The fresh helper's writer, normal replay and optimized-Python replay all
passed from `/` before freezing, with byte-identical receipts. Explicit
guards are used rather than optimization-removable assertions. Finite
checks supplement the induction and decidability proofs; they do not
prove an unbounded compiler or a global operation optimum. The established
universal arithmetic bound remains 84 operations.

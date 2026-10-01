# A complete 440-operation universal equation through Tseytin's semigroup

There is one fixed integer polynomial `F(x,A,z1,...,z65)`, evaluated by
**440=200M+240A** binary additions, subtractions and multiplications, with
the following property. From an enumerator of any computably enumerable
set `T` of positive integers, one can effectively obtain a positive
integer `A_T` such that

\[
 x\in T\quad\Longleftrightarrow\quad
 \exists z_1,\ldots,z_{65}>0:\ F(x,A_T,z_1,\ldots,z_{65})=0
 \qquad(x>0).
\]

The input is the ordinary integer `x`. There is **one positive program
parameter, 65 positive existential coordinates**, and a guarded total
degree bound **5868**, counting the program parameter as a variable.
The certificate source has420 paid gates and7 comparisons. A separate
442-operation construction keeps the two unit products separate and has
degree at most5814, with the same65 witnesses. These bounds are for the
actual fixed Tseytin C2 table, including its input loader and chronological
history. They leave the overall75-certificate/87-polynomial record
unchanged.

The [literal source](tseytin_universal440.py) and
[receipt](tseytin_universal440.json) compose three complete or explicitly
conditional components:

| Component | Paid certificate gates | Comparisons | Positive auxiliaries |
|---|---:|---:|---:|
| [C2 encoded-word history](tseytin_c2_word_history.md) |357|6|52|
| [Exact affine exponent](pell_fixed_affine_exponent.md) |52|1|12|
| [Query loader](tseytin_affine_power_query_loader.md) |10|1|0|

The loader's `word` parameter becomes one more positive existential
coordinate. Its `Q` parameter is replaced by the exponent component's
computed register, with no new supplied coordinate or omitted equality.
The merge below saves two operations only because the paid loader rules
out the exponent component's negative signed-unit branch.

## 1. Effective programs and the fixed semigroup

Use `[g,h]=ghg^-1h^-1`, `a_x=b^-x a b^x`, and `r_x=[a_x,a]`.
Sections1--2 of the [commutator substrate proof](group_commutator_universal_substrate.md)
give an effective finite group presentation `H_T` with distinct named
letters `a,b` such that `r_x=1 in H_T` exactly when `x in T`, for every
positive `x`. The recursive presentation starts with precisely the
relators `r_n` for enumerated `n in T`. Its graph-group semidirect model
proves both directions: a missing edge retracts onto a free group of
rank two. Effective Higman embedding and adjoining fresh named letters
then give the finite presentation without changing those answers.

The external effective theorem is
[Mikaelian, Algorithm1.1 and Section2.1](https://arxiv.org/html/2507.04347v8).
Its recursively enumerable relations need not have a decidable word
problem. This packet uses that mathematical algorithm as a dependency;
it does not implement or materialize its enormous output. The later
fibre-product and matrix constructions in the substrate note are not
needed here. No bound on presentation rank, number of relators or their
lengths enters this circuit count.

Convert the finite group presentation to a special monoid presentation
by supplying a letter for each signed generator and both inverse
cancellation relators. Use the [primary Tseytin reduction](tseytin_group_completion_obstruction.md)
with codes

    alpha:1, beta:0, a:2, a^-1:3, b:31, b^-1:63,
    all other signed generators: distinct integers at least64.

Section2 of [Tseytin's translated paper](https://arxiv.org/pdf/2401.11757)
allows distinct nonnegative codes. Take `i=1,j=0` in its Sections3 and7.
The finite relator list determines a word `S` over `c,d`, independent of
`x`. Section7, Lemma9 then gives

    r_x=1 in H_T  iff  S phi(beta r_x beta) = aaa in C2.        (1)

The nine relations of this same fixed C2 are

    ac=ca, ad=da, bc=cb, bd=db, eca=ce, edb=de,
    cdca=cdcae, caaa=aaa, daaa=aaa.

The word component uses exactly their18 orientations and six copying
tiles, including a history delimiter. Its complete theorem recognizes
`enc8(u)` exactly when `u=aaa in C2`; invalid positive codes have no zero.
This is the noninvertible semigroup relation. Its universal group remains
trivial, so the earlier group-completion obstruction remains correct.

## 2. All loading arithmetic is paid

Write `B=8^32=2^96`, `d=B²−1`, and `enc8` for the sentinel base-eight
encoding with letter digits1 through5. The query's literal tail is

    a (ab^63)^x abb (ab^31)^x abb (ab^63)^x abbb (ab^31)^x abbb aa.

Its length is `192x+17`. The loader proves the polynomial identity

    d enc8(S phi(beta r_x beta))
      = A Q^6+h4 Q^4+h3 Q^3+h1 Q+h0,             Q=B^x,        (2)
    A=d 8^17 enc8(S)+h6.                                      (3)

The coefficients are fixed integers:

    h6=8^15(65B²−72)/7,
    h4=−8^12(B²+B−512),
    h3=−8^9(B²−512B−512),
    h1=−8^5(B²+B−4096),
    h0=(−65B²+229376B+229441)/7.

Here `B=1 mod7`, so the displayed divisions specify integer constants
at construction time. The source performs no division or exponentiation.
It computes `Q²` and a reused-power Horner numerator, and multiplies the
positive word coordinate by `d`: ten paid gates, with their equality
retained as an ordinary comparison. All numeral multiplications count.
Equation(3) supplies one positive program constant; no claim about an
arbitrary positive value of `A` is required for universality.

The exponent component supplies twelve positive coordinates and computes

    r=48x+15, Q=x+delta, X=2^31 Q, Y=s.

At every positive solution of its six-factor equation `P=1`, the proved
output projection is `Q=B^x`; a positive extension exists for every `x>0`. More
precisely, the necessary signed-unit projection in its proof says

    P in {−1,1}  implies
      P=+1 and Q=B^x,  or  P=−1 and Q=B^x/16.                  (4)

The four norm signs are individually positive modulo4, and the local
rank and ratio argument forces the linear factor positive before the
remaining index sign is resolved. This signed conclusion holds without
assuming the standalone equation `P=1`. It is the conclusion needed
for the merged construction.

## 3. The loader excludes the negative signed-unit branch

Let `W` be the word component's seven-factor product. Let `R1,...,R5`
be its five ordinary residuals, and let `R6` be the difference of the
two sides of the paid query comparison. The composed polynomial is

    F=W P (1+R1²+...+R6²)−1.                                 (5)

At an integer zero, `WP` and the positive integer `1+sum Rj²`
multiply to1. Therefore all six residuals vanish and `WP=1`. Every
individual factor of `W` and `P` is an integer unit. In particular
`P=+1 or−1`, so(4) applies. We must rule out its second branch before
using either parent's complete unit-product theorem.

The program recipe gives `A=h6 mod d`. Also `B²=1 mod d`, and16 is
invertible modulo the odd integer `d`. If `Q=B^x/16`, then the query
numerator in(2) has the following least residues:

| Parity of x | Q modulo d | Numerator modulo d |
|---|---|---|
| even |16^-1|`15759360 B+558888960`|
| odd |`B 16^-1`|`24115200 B+550533120`|

Both displayed residues lie strictly between0 and `d` at `B=2^96`.
For exact integer certificates of this calculation, put

    C_e=h6+16² h4+16³ B^e h3+16⁵ B^e h1+16⁶ h0.

Then the fixed coefficients satisfy

    C_0=308535569154048 d+16⁶(15759360 B+558888960),
    C_1=(590560301678592−584115552256 B)d
           +16⁶(24115200 B+550533120).                        (6)

These are exact integer identities, checked independently of residue
sampling. Reducing `16^6` times the numerator uses `B²=1 mod d`
to give `C_e`. Invertibility of16 proves the table. But `R6=0`
says that this numerator equals `d word`, whose residue is zero.
This contradiction excludes the negative branch for every positive x.
Consequently `P=1`, `Q=B^x`, and `W=1`.

Blindly multiplying two signed-unit equations would not justify this
step. The fixed coefficients, valid program recipe, and retained query
comparison are essential hypotheses of the merge.

## 4. Soundness and positive completeness

Suppose all supplied coordinates are positive and(5) is zero with
`A=A_T`. Section3 gives both original products equal1 and all original
ordinary comparisons. The power theorem supplies `Q=B^x`. The paid
loader identity then forces

    word=enc8(S phi(beta r_x beta)).

The full C2 word-history theorem applies with this positive parameter
and its own52 positive coordinates. It concludes that the literal query
word equals `aaa` in C2. Equation(1) gives `x in T`. No part of this
argument assumes an unproved length, selection, padding or chronology
predicate: those are inside the word component's complete native
certificate.

Conversely, suppose `x in T`. Choose the positive exponent extension
proved for this input, and set `word` to the literal query encoding.
The query equality follows from(2). Equation(1) gives a finite actual
C2 derivation. The word component's completeness theorem encodes its
chronological tile history and supplies all52 positive native and outer
coordinates, with a sufficiently large paid height slack and freshly
chosen canonical native auxiliaries. The two sets of auxiliaries are
disjoint; the shared values are just the computed `Q` and supplied
`word`. Thus `P=W=1` and every `Rj=0`, so(5) is zero. This constructs
all65 positive existential coordinates as a mathematical existence
proof. The enormous full Pell tuples need not be numerically printed.

For comparison, the separate form is

    F_sep=W(1+R1²+...+R6²+(P−1)²)−1.                          (7)

Its soundness and completeness follow directly from the two parent
theorems and the loader, without the signed merge. It remains a useful
independent interface and has the slightly smaller degree bound below.

## 5. Literal ledger, degree bounds and source guards

The separate certificate has `357+52+10=419` gates and8 comparisons.
Its anchored finalizer adds23 gates, for **442=200M+242A**. Merging
adds one multiplication to the certificate and removes one comparison:
`420+20=440`, comprising **200M+240A**. Every gate is an ancestor of
the final output. No aliases or program preparation are counted as
variable-time arithmetic, and no arithmetic in the actual source is
treated as a free alias.

The C2 factor degree bounds are

    931,2158,503,72,1154,429,429,    sum5676.

The power factor degrees are exactly

    5,7,14,22,3,3,                  sum54.

The former ordinary residual degree bound is69; the new query comparison
has degree7, since the computed `Q=x+delta` has degree1. Thus the merged
product has degree at most5730 and(5) has degree at most

    5676+54+2*69=5868.

For(7), `max(69,54)=69`, so its degree bound is `5676+2*69=5814`.
Each parent uses its own all-integer cancellation in the main Pell
norm; neither cancellation depends on being at a solution. These are
guarded upper bounds for the full universal polynomial, not claims of
exact expanded degree. The ordinary SOS forms also have440 and442
operations, with respective degree bounds11460 and11352.

The source prefixes every exponent coordinate and register except its
input `x` with `exp__`. The loader reads the computed `exp__Q`. The
word component's graph is unchanged and its former input is now among
the positive witnesses. Public `polynomial_source` and `degree_bound`
accept only a full canonical composition packet, including its exact
comparisons, domains and interface names. A topological closure audit
checks every arithmetic operand and that every paid row reaches output.

The receipt contains all four full source schedules, counts, degree
bounds, hashes, and the fixed sign certificates(6). Its author audit
checks512 complete outputs on128 assignments, half signed, using
separate parent executions, a direct six-factor power oracle and a
separate six-degree query formula. It also checks96 literal program/input
queries and their rejected negative power branches. These query fixtures
use placeholder native/Pell auxiliaries and are expressly not full
zeros. Source guards reject ten mutated callers. The complete universality
theorem is the parametric proof above and its identified dependencies,
not an inference from finite tests or an implemented Higman compiler.

Run `python tseytin_universal440.py` for a fresh receipt comparison;
`--write` regenerates it. Author generation and a separate fresh replay
passed. An independent full proof/source/dependency review and fresh replay
passed without findings. Its separate executor checks384 complete manual
thirteen-factor, query and finalizer identities, including192 signed
assignments, plus12 zero-selector assignments. It checks all four complete
degree/opcode/liveness dictionaries and rejects24 additional changed
metadata packets. Its own derivation verifies both identities(6)
symbolically in an indeterminate B, independently of the fixed integer
evaluation in the receipt.

A second independent source audit checks all four degree bounds and
ledgers, both symbolic main-norm cancellations under renaming, all65 live
witnesses and all live gates. A third review verifies the effective
group-to-C2 handoff against the primary embedding algorithm and Tseytin's
code permission and Lemma9. All seven local links resolve. These reviews
do not claim a formal proof-assistant verification or a numerically
materialized full Pell solution.

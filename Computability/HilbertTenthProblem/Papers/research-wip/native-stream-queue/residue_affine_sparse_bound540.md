# Removing dominated bounds in the sparse universal compiler

The [complete source](residue_affine_sparse_bound540.py) lowers the
[551-operation compiler](residue_affine_sparse_factored.md) to
**540 = 193M + 347A**, with **67 positive witnesses**, **8 comparisons**
and product degree at most **10052**. Its certificate has **517 operations**.
The [receipt](residue_affine_sparse_bound540.json) includes the complete
default polynomial schedule, its digest and all five literal ledgers.
The change removes eleven additions from one bound; it adds no unit-sign
relaxation and changes no machine or input convention.

The fixed U21 table, primes (5,3,2,7,11,13,17,19), paid chronological
loader and ordinary positive input x are inherited unchanged. For every
recursively enumerable set of positive integers, a fixed positive parameter
E=3^e makes positive zeros exist exactly at its members. The primary
universality theorem and its exact input convention remain those recorded
in the [complete prime-payload parent](residue_affine_sparse_universal.md).
This is an improvement to that independent universal route; it does not
improve the separate U9 or Korec bounds.

## 1. The reduced positive bound

Use the notation and literal local graph of the 551 parent. There are b
edge-selector words E_e=edge_hat_e−1>=0, and J=sum E_e. The quotient and
two remainder words W,R,S are positive hats minus one. For each occurring
prime p>2, Z_p is the similarly represented selected quotient word. There
are k such primes and g=k+2 selected words after including the two action
words Y_I,Y_D. Define the already paid words

    U=W+J,
    V=U+sum_(p>2) (p−2)Z_p.                              (1)

All coefficients in (1) are nonnegative, and p−2>=1. Thus, before any
equations or bit typing,

    V>=U>=W,J,     V>=Z_p for every p>2.                 (2)

The unchanged scale definitions are

    h=E+x+F+eta,       B=C_B*h,
    P=(B−1)J+1,       range_mask=(h−1)J.                 (3)

All four summands defining h are positive, so h>=4. The dyadic fixed
multiplier C_B is at least max(4,b+1,m+2,3*p_max+1), where m is the
body-state count and p_max is the largest supplied register prime. The
default has C_B=64, b=36, k=7 and g=9.

Replace the parent's first comparison

    J+V+W_hat+R_hat+S_hat+sum Zhat_p
          +Y_I_hat+Y_D_hat+beta_old=P                    (4)

by

    V+Y_I_hat+Y_D_hat+beta_new=P.                        (5)

Every other source row, variable domain and comparison is retained. In
particular, the exact remainder comparison is still paid:

    R+S=sum_(zero edges e) (p_e−2)E_e.                   (6)

The removed sum has k+4 terms: J, three quotient/remainder hats, and k
prime-selected hats. The old bound used k+7 additions; (5) uses three.
This saves exactly k+4 additions, eleven in the actual U21 instance.

## 2. Bounds before native typing

At a positive zero, (5) has two positive action hats and a positive slack.
Consequently P>=3 and V<=P−3. If J=0, definition (3) would instead give
P=1. Hence J>=1 and P>=B. Equations (2) and (5) imply

    0<=W,J,U,Z_p,V<P,        0<=Y_I,Y_D<P.               (7)

The removed remainder bounds follow from the still untyped scalar
equation (6), not from the native AND:

    0<=R,S<=R+S<=(p_max−2)J<(B−1)J=P−1.               (8)

This uses only E_e>=0, sum E_e=J and B>p_max. It also bounds the
positive remainder hats strictly below P. Each edge or class selector
lies between 0 and J. Its full mask is therefore at most (B−1)J=P−1;
the range mask is strictly smaller than P because h−1<B−1.

Thus every coefficient in the joined AND lanes lies in [0,P):

    (E_e,J,E_e)                          for every edge,
    (U,(B−1)G_p,Z_p)                     for each p>2,
    (V,(B−1)I_sel,Y_I), (V,(B−1)D_sel,Y_D),
    (W,range_mask,W), (R,range_mask,R), (S,range_mask,S).

There are L=b+g+3 lanes. The unchanged paid native scale is Q=B*P^a,
where a is the least power of two at least L. Every packed word is less
than P^L<=P^a<Q. The padded ports are therefore legitimate positive
ports for the same complete native theorem, with no prior dyadic or
Boolean assumption. The folded prescribed ports remain 16Q,16H+12,
16M+10,16A+8.

The inherited theorem for each native form now yields dyadic B,P,h,
P=B^T and J=1+B+...+B^(T−1), for T>=1. The rest of the parent's proof
applies in its original order: selector typing, W/R/S ranges, carry-free
U, prime selections and V, action selections, the row remainder equation,
positive current/following payload digits, and finally chronological
control/payload transport. In particular, the loader is a nonempty
contiguous prefix. Its growth and the retained range give length ell<B−1,
while x<h<B−1. The paid count congruence then forces ell=x. Neither
input loading nor chronological adjacency has been removed.

## 3. An exact positive-zero bijection for each form

Define the scalar expression, independent of either slack,

    Delta=J+W_hat+R_hat+S_hat+sum Zhat_p.                  (9)

Use the affine maps

    beta_new=beta_old+Delta,
    beta_old=beta_new−Delta.                            (10)

For arbitrary integer assignments, the final bound expressions in (4)
and (5) agree under (10). Every other row is unchanged except the private
partial sums inside that bound. All comparisons, unit factors and both
complete finalizer outputs agree exactly. This identity also holds for
the inherited rational off-zero lifts used by native normalization.

The forward map preserves positivity on every positive assignment,
because Delta>0. The inverse can be nonpositive off zero. To prove its
positivity at every positive zero, use only the typed consequences from
Section 2. The prime classes are disjoint, and the increment and decrement
classes are disjoint, so

    sum Z_p<=U,     Y_I+Y_D<=V,
    U+V<=p_max*h*J,     R+S<=(p_max−2)J.                 (11)

The inverse slack is exactly the old bound's required value. Combining
(3) and (11) gives

    beta_old
      =P−J−V−W−R−S−sum Z_p−Y_I−Y_D−g−3
      >=(B−2*p_max*h−p_max+1)J−g−2
      >=2*p_max+3>0.                                   (12)

For the last step, C_B>=3*p_max+1 and h>=4 give a coefficient at least
3*p_max+5, while J>=1 and g<=p_max. The latter follows because the
distinct supplied primes include 2 and there are at most p_max−1 integers
from 2 through p_max.

Crucially, (12) holds for every typed zero: it uses disjoint selections
and the remainder equation, not a specially chosen padded run, a chosen
height slack, or even the transport equations. Thus (10) gives inverse
bijections between the complete positive zero sets of each new form and
the corresponding fixed 551 form, retaining every other coordinate.
This includes arbitrary positive E; the universal represented-set claim
uses the valid recipes E=3^e. Bijections between different native forms
are not asserted: those inherited conversions may reconstruct private
witnesses.

Completeness can also be read directly. A genuine accepted run has the
positive parent extension proved in the 551 note; add Delta to its slack.
All other coordinates remain positive and every new comparison holds.
Conversely, Section 2 recovers that run, and (12) gives its unique positive
parent slack with all native coordinates unchanged.

## 4. Source guards and literal ledgers

`rewrite(old)` accepts only the canonical raw 551 packet, rebuilding and
comparing its complete source, parameters, witnesses, comparisons and
metadata. It also checks the literal private bound chain, its sole slack
consumer, all intermediate consumers and interface exports. It retains
the last bound register and its comparison, rewrites the last three rows,
and deletes the preceding k+4 rows. Rewriting a finalized or already
rewritten packet is rejected.

`build(table, form, primes, shared)` applies this raw rewrite before the
same frozen positive-scale, computed-field, norm-unit and coupled-index
helpers. Their ancestry therefore contains the actual reduced bound.
The helpers `lift_to_parent`, `project_from_parent`, `direct_outer` and
`pack_path` expose the exact maps and outer oracle. The raw table, prime
assignment, all native row guards and the original degree audit remain
in force. There is no new fixed numeral or uncharged constant scaling.

|Form|Certificate|Comparisons|Witnesses|Final polynomial|Degree bound|
|---|---:|---:|---:|---:|---:|
|raw SOS|509=178M+331A|21|74|571=199M+372A|1564|
|positive-scale SOS|509=178M+331A|20|73|568=198M+370A|1564|
|six-field SOS|509=178M+331A|14|67|550=192M+358A|3488|
|normalized norm product|514=183M+331A|10|67|543=193M+350A|10562|
|coupled-index product|517=185M+332A|8|67|540=193M+347A|10052|

The default factor bounds remain 1614,3752,873,129,2008,742,742. Their
sum is 9860 and the maximum retained residual bound is 96, giving
9860+2*96=10052. The same-cost coupled SOS has bound 19720. These are
propagated upper bounds, not claims of exact degree or circuit optimality.
All retained gates reach the final output. The savings hold equally for
the shared and unshared parent packing recipes.

## 5. Verification and scope

Run `python3 residue_affine_sparse_bound540.py` to replay the receipt;
`--write` regenerates it. The author writer and fresh default replay pass
on the saved source.
The checks cover 25 ledgers across all five forms and five tables,
including the case with no exceptional prime. They include 1,120 complete
source/residual/finalizer identities from 800 assignments, 400 signed;
160 independent raw/native-oracle SOS identities, 80 signed; positive
parent projections and deliberately nonpositive off-zero inverse slacks;
and the inherited native correction audits.

There are 512 positive untyped bound/remainder fixtures, all with
nondyadic scales, including 443 nonpositive inverse slacks before typing.
Another 498 arbitrary typed row-word fixtures verify (12) without assuming
chronology. Differential execution across 31 tables checks 184 halted
histories and 792 chronological rows, with 172 wrong-input rejections.
Eleven malformed or duplicate callers are rejected. These are finite
algebra and outer-history checks; no full native Pell witness tuple is
materialized by these fixtures.

Root's independent full proof/source/dependency review and fresh replay
pass without findings. A separate executor and manual slack transformation
check672 complete outputs and retained-register identities across30
additional contexts and all five forms, with240 signed assignments and306
nonpositive algebraic inverse slacks. These complement the all-zero-set
positivity proof; the signed assignments are not asserted positive zeros.

Native's independent full proof/source/dependency review and fresh default
replay pass with no findings. A separate executor and manual slack maps
check 448 complete source/residual/output identities, 224 signed, across
40 contexts covering both packing recipes, all five forms and four
tables. These include 224 positive off-zero assignments with nonpositive
parent slacks, plus 56 positive projection identities. A further 1,152
independent typed-margin cases include primes through 31, heights through
17 and durations through four. All four local links resolve. These are
finite algebra and typed-row checks, with no full Pell tuple claim.

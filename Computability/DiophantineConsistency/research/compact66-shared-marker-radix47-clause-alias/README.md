# A radix47 alias of the isolated shared-marker clause test

This is a CODE-FREE ordinary obstruction to one proposed proof step.
It concerns the unchanged shared-marker coefficients and clause mask
from the pinned conditional49 proposal, read at rho=2^47. It is not
an actual cyclic transport witness, a native word, a P66 zero, an
unsoundness proof for a whole encoding, or an impossibility result at47.
The frozen49 proposal and every maintained source remain unchanged.

The exact construction below passes one clean clause, or two clean
clauses with the same allowed incoming carry, with more than one
selected tile. It even permits the incoming and outgoing carries to
obey the valid nonminimal bound93. Thus a sound47 proof must add an
argument connecting the actual predecessor carries or other native
tests; the current isolated-clause inference does not suffice.

## 1. Exact inherited parameters and scope

Keep the actual943 ordered tile labels of the conditional49 packet.
For i=0,...,942 write

    u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i, 0<=u_i<2^34,
    c_i=1+2^10*(2^34-u_i).

The34 independent Boolean label-copy bits encode an arbitrary integer
W in[0,2^34). Seven Boolean markers at physical positions

    M_mark={992,1011,1022,1031,1095,2195,3296}

all have clause weight2^44. If their sum is m, then0<=m<=7.
For Boolean selectors x_i put n=sum_i x_i and

    A=sum_i(2^34-u_i)*x_i,
    Q=A+W+2^34*m,
    Acl=n+2^10*Q.

Here rho=2^47 and mu=2^47-2=rho-2. A clean clause with incoming
carry k passes exactly when the representative of Acl+k modulo rho
has bitwise AND0 with mu. Only its low bit may then be nonzero.

The local variables are Boolean selectors, labels and markers plus a
bounded incoming carry. The actual convolution/predecessor equations,
rotation/phase, copy/anchor/padding tests, cyclic carry fixed point,
population/rank/source equations and positive P66 witnesses are NOT
included in this local interface. No claim below supplies them.

## 2. A valid nonminimal carry93 comparison

Let C_old and C_new denote the full formal coefficient sums before
and after the seven-marker reweighting. The retained exact threshold is

    Theta=118788496120850159560
         =4*988*(2*C_old+6)+8=7904*C_old+23720.

The new coefficient sum satisfies C_old-C_new=2^51-2^47=15*rho.
The elementary integer comparison

    Theta<107*7904*2^47=119025634551774838784

therefore gives C_old<107*rho-3 and C_new<92*rho-3. No new
coefficient sum or tuple has been evaluated. This is a comparison with
the exact previously recorded threshold and formal identity.

The same unchanged-support estimate used in the conditional49 proof
then bounds the entire predecoded convolution, including the possible
extra2 at the low dummy, by

    U=C_new+5+2*(1+2^44)<(369/4)*rho+4.

A fractional temporal rotation contributes at most3*rho/4; at its
last phase its sharper bound is rho/2+1. Thus every raw digit a obeys
a<93*rho+4, and a+93<94*rho. The monotone cyclic carry map takes
{0,...,93} into itself coordinatewise. This is a sufficient bound,
not an assertion that93 is the smallest valid bound or an observed
actual carry. Further sharpening this estimate alone is not a proof
that every clause's incoming carry is at most80 or81.

The bound would give n+k<=943+93=1036. The first ten tested bits
can therefore admit n+k=1024 or1025, as well as0 or1. The following
construction realizes the1024 branch in the complete local aggregate.

## 3. Whole parametric alias construction

Choose ANY integer n with931<=n<=943 and ANY set I of n distinct
actual tile indices. Set x_i=1 exactly on I and define

    k=1024-n,                  so81<=k<=93,
    A=sum_(i in I)(2^34-u_i),
    V=(-1-A) mod2^37,          with0<=V<2^37,
    W=V mod2^34,
    m=floor(V/2^34).

These are explicit finite arithmetic formulas using the retained tile
labels. They hide no new coefficient table, program or integer choice.
Since V<8*2^34, one has0<=m<=7 and0<=W<2^34. Realize W by
the34 independent Boolean label bits and realize m by setting any m
of the seven Boolean markers to1 and all remaining markers to0.
Set both dummy bits0.

Then W+2^34*m=V and Q=A+V=-1 modulo2^37. Since each selected
term2^34-u_i is positive, A>0. Consequently

    Q+1=h*2^37 for some positive integer h,
    Acl+k=n+2^10*Q+(1024-n)
          =2^10*(Q+1)=h*rho.

The actual tested representative is exactly0, so its AND with mu is0.
Every selector, label and marker is Boolean, every retained coefficient
is the prescribed actual coefficient, and n>1. No assumption that the
seven markers are equal was used or obtained.

Moreover Acl is a sum of a subset of ALL nonnegative coefficients:
the selected selector coefficients, the selected34 label controls and
the selected seven marker controls. Thus Acl<=C_new<92*rho-3.
Together with k<=93 this implies0<h<93, hence1<=h<=92. Therefore
the outgoing carry h also lies in the same allowed0..93 range. The
alias is not caused by silently permitting an oversized outgoing carry.

## 4. Start and Forbidden restrictions, and two clean clauses

For every931<=n<=942 take the explicit index set

    I={0} union {2,3,...,n}.

It has n members, contains Start0 and omits Forbidden1. Thus the
alias family does not require selecting the forbidden selector or
omitting Start. Its incoming carry ranges82..93. The n=943 endpoint
of the unrestricted local family necessarily uses all943 selectors;
that endpoint is not asserted to respect the Forbidden restriction.
No further Start tile labels, occupied propagation or origin transport
conditions have been inferred from the mere presence of selector0.

If both clause sites are clean and are supplied the same permitted
incoming k, the same Acl gives representative0 and outgoing h at BOTH
sites. Two copies of the isolated clean-clause test therefore do not
remove the alias. The actual two predecessor carries are not free in
a native word; no claim that the prescribed equal k can arise from
their full convolution or cyclic predecessor equations is made.

For a hypothetical stronger bound K with81<=K<=93, the unrestricted
local family remains available for max(931,1024-K)<=n<=943. If
Forbidden1 is excluded, use the same interval with upper endpoint942,
which is nonempty for K>=82. A bound k<=80 suffices to prevent this
low-ten-bit wrap under n<=943; with Forbidden excluded, k<=81 suffices
under n<=942. These are arithmetic sufficient conditions, not newly
proved bounds for the actual native carries.

## 5. Exactly what this obstructs

At rho49 the prior proof uses n+k<=967<1024 to infer n<=1 before
recovering W and all seven markers. At rho47 that guard cannot simply
be dropped or replaced by the bound93. The full payload test does not
repair the inference: W plus the marker count ranges over the complete
interval0..2^37-1 and supplies exactly the compensating residue above.

This refutes the isolated local implication from Boolean inputs,
incoming/outgoing carry bounds93 and a clean mask to n<=1. It also
refutes that implication after adding a second identical clean test,
or merely requiring Start selected and Forbidden absent in its stated
subfamily. It does not refute a stronger implication that imposes the
actual predecessor equations, copy/anchor tests or whole source.

In particular this is not a finite refutation of Con(ZFC), a positive
solution of an actual consistency equation, or evidence that the full
radix47 encoding is unsound. No full coherent47 masks/controller/P66
adapter or complete soundness/completeness theorem is supplied here.
An additional ordinary argument or a changed encoding remains possible.

## 6. Boundaries and reproducibility

The full frozen49 packet supplies the exact shared-marker aggregate,
the support geometry and formal coefficient-sum identity. The existing
indexed certificate supplies its exact retained old threshold. Their
four exact byte records and the whole49 manifest are in SOURCE_PINS.
That catalogue is direct ordinary provenance; it is not a fresh
transitive compiler/native/kernel audit or certificate replay.

All mathematics above is hand derivation. Only inert existing text,
JSON, hash and inventory reads were used. No application, math helper,
import, AST, coefficient/residue/Pell calculation, numeric search,
compiler, collector, Lean, TeX or PDF process was run. No coefficient
data, numerical tuple, main page, frozen parent or Lean file changed;
no commit was made. The note is a bounded author proposal for full
independent ordinary review and carries no endpoint or minimum claim.

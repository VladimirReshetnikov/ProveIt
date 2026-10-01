# A complete explicit U9 universal polynomial in 303 operations

Combining input recoding and selected history in one native bitwise-AND
certificate leaves just two native Pell cores: one population geometry
core and one joint AND core. Applying the existing positive unit maps
and normalizing both strong witnesses gives **303=144M+159A polynomial
operations**, **51 positive existential witnesses**, **16 comparisons**
and four positive program parameters besides the ordinary positive
input x. The certificate costs **256=128M+128A** and the total degree
is **at most2285**, including every program coordinate.

The [source](neary_woods_universal_joint_and_units.py) and
[receipt](neary_woods_universal_joint_and_units.json) give the complete
literal DAG. This improves the explicit U9/tag route from
[377 operations](neary_woods_universal_population377.md); the separate
best established bounds remain75 certificate operations and
[87 polynomial operations](complete75_normalized_strong87.md).
No exact degree or optimality is claimed.

## 1. The complete raw parent and the fused AND contract

The [raw joint-AND proof](neary_woods_universal_joint_and.md) supplies a
complete246-operation certificate with37 comparisons and64 positive
witnesses; its SOS polynomial costs356 operations. Here is the exact
interface used by the present unit construction.

Put S=qP, L=BS, and let ell be the recoder duration. The low words are

    Hr=B*xJ+ell, Mr=B*K+ell-1, Zr=B*(Ahat-1).

The retained repunits P=(B-1)J+1 and S=(2B-1)K+1, ordinary input bound
x<q, and duration bound0<ell<B imply Hr,Mr<L before either old AND is
typed. One additional paid comparison Ahat+beta=S, with beta>0, gives
Zr<L. Its converse is strict: every genuine parent recoder has
Ahat-1<=xJ and hence

    S-Ahat >= [q(B-2)+1]J+q-1 > 0.

The high words Hh,Mh,Zh are the same nonnegative selected-history
packings as before, with positive scale Th=Ph^11. Their nonnegativity
and Ph>=1 hold on every positive supplied tuple, before the history
is decoded. One prescribed-scale native AND now certifies

    (Hr+L*Hh) AND (Mr+L*Mh) = Zr+L*Zh,
    L*Th is dyadic,
    0<=Hr+L*Hh, Mr+L*Mh<L*Th.

Since the positive integer factors L and Th are then dyadic, unique
binary splitting at L recovers both original AND graphs and their
ranges. Conversely the two old AND graphs and positive beta give the
joined graph, which admits a fresh positive native extension. The
raw proof preserves all remaining outer and geometry coordinates;
it does not identify old and new native witness tuples.

The literal source keeps the four-bit low padding and extends its
three old ports by q0 times the high words, where q0=16L. It multiplies
the old native scale by Th. These seven packing gates and the one
output-bound addition replace the separate64-gate history AND core.
The result has exactly two native cores, named `geo__` and `and__`.
The historical child history packet is no longer a separately embedded
native certificate; the actual full source and explicit fusion metadata
are authoritative.

## 2. Positive unit projection of the two remaining cores

Apply the existing guarded
[two-core unit rewrite](native_binary_input_dilation_unit179.md)
to the actual fused raw DAG. Its literal native norm and positive
coordinate definitions match; its proof does not require the old
separate recoder-only AND port formulas. The joined native scale and
joined output field are positive on all positive supplied tuples.

For each core write X=w*q_native, Y=s*q_native and E=XY; this native
E is distinct from the program coefficient program_E. The main and
auxiliary norms become sign-safe unit factors. The first Pell root is
replaced by its positive gap g:

    N0=g^2+4*E*(kY)*(g-k),
    tau=E*kY+(g-1)/2.

At a unit zero, modulo4 gives odd g and positive integer tau. The
inverse from an old first norm gives positive g. The auxiliary norm's
coefficient is replaced by its retained full strong right-hand side;
the verifier includes the resulting off-zero correction.

The rewrite projects13 positive definitions: the outer q and P;
five native coordinates s,k,c,a,d in each core; and the packed index r
of the joint AND. Positivity is unconditional on the new positive
domain, using q=x+input_slack, P=(B-1)J+1, the positive native scales
and positive joint F3. The stored projected J and Ahat remain the
already-paid positive expressions of the raw parent.

There are six norm factors and one joint checksum. The six norms
exclude -1 modulo4 before native typing. A product equal to one
therefore makes every norm and the single checksum equal to+1. Every
retained outer comparison is kept in the safe finalizer

    U*(1+sum of outer residual squares)-1.

Its vanishing forces all outer residuals zero and U=1. The old raw
positive coordinates and equations are therefore restored. Conversely
an old raw zero maps to a positive unit zero. These maps are inverse
on positive zero sets. The fusion theorem itself still uses fresh
native extensions when compared with the earlier two-AND construction.

This first unit stage adds six product multiplications, removes19
comparisons and13 witnesses. It costs252 certificate operations,
18 comparisons and51 witnesses; the polynomial costs305 operations.
There is now only one checksum, so the earlier separate-history
checksum sign theorem is not needed by this finalizer.

## 3. Two full strong normalizations

Use the [single-core normalization](pcp_normalized_strong_history_units.md)
independently in each remaining core. Write Delta=(a+2)^2-1. The
retained strong comparison is

    (i_old*c^2)^2=Delta*(f^2-1).

With a new positive coordinate i, put t=i*c^2 and use the factor

    Ns=f^2-Delta*t^2.

It cannot be -1 modulo4. The auxiliary coefficient uses Delta^2*t^2,
and Ns is appended to the same unit product. Each core adds two
multiplications and removes one comparison, saving one polynomial
operation. Thus305 becomes303.

At a normalized zero, all eight norm factors are+1 by their independent
sign exclusions, then the sole checksum is+1. The positive lift

    i_old=Delta*i

restores both full strong comparisons and auxiliary coefficients.
The first-stage positive maps then restore the complete raw source.

For completeness, an old accepted outer tuple supplies the main native
indices and parameters for both cores. In each core separately, the
existing canonical construction at m=2cR supplies fresh positive
f,i,j,o,y_aux and the required c^2 divisibility. Here R=2r+1 is that
core's main Pell index: r is the geometry index in the first core and
the newly packed joint index in the second. The source checks that
these ten rebuilt coordinates occur only in their respective private
native blocks. Apart from each core's strong comparison, auxiliary
congruence and auxiliary factor, no retained comparison or unit factor
depends on them. Therefore both canonical
extensions can be made simultaneously with every ordinary-input,
duration, concatenated word, history and geometry interface fixed.

The normalized and unit forms have the same accepted outer relation.
This converse reconstructs native auxiliaries; it is not a bijection
between arbitrary normalized and unnormalized supplied tuples.

## 4. Universal ordinary inputs and exact arithmetic bounds

The actual fixed machine is the original1968-state U9-derived binary
clockwise table. Its production, all eleven fixed-numeral recipes,
positive program slice, exact least-dyadic counter128n and valid
U9 simulation slice with at least six A symbols remain unchanged.
The raw fusion proof retains the paid ordinary-input loader and the
entire chronological selected-history relation. Applying Sections2--3
therefore gives one fixed polynomial F such that, for every recursively
enumerable positive set S, four fixed positive values A_S,B_S,T_S,E_S
satisfy

    x in S iff exists y_1,...,y_51>0:
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_51)=0.

Program values are fixed per set, not existential witnesses. The
optional independent fifth duration-bound parameter remains available.
Both parameter interfaces have the same counts and degree bounds.

| Form | Certificate | Comparisons | Positive witnesses | Polynomial | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Raw SOS |246=118M+128A|37|64|356=155M+201A|580|
| Native units |252=124M+128A|18|51|305=142M+163A|1475|
| Two normalized strong units |256=128M+128A|16|51|**303=144M+159A**|**2285**|

Degree is propagated over the actual complete DAG, assigning degree
one to all input, program and witness coordinates and zero to fixed
numerals. For both unit forms, the two main-norm cancellation identities
are applied only after checking every literal defining row. There is
no invocation of a three-core or fixed-exponent degree formula.

The normalized native scale degrees are1 and49. Its nine factor bounds
are12,38,8,252,976,152,49,22,406, totaling1915. The largest retained
outer residual has degree at most185, giving1915+2*185=2285. For the
305-operation form the product bound1063 and residual bound206 give
1475. For the raw SOS, the largest residual bound290 gives580. These
are conservative upper bounds; no nonzero leading coefficient or
exact-degree statement is inferred.

## 5. Verification and evidence limits

The writer and fresh default cover both parameter interfaces and all
three finalizers. There are256 complete two-core unit corrections,
128 signed, and128 additional complete normalization corrections.
The checker restores normalized i coordinates, then explicitly restores
all projected raw coordinates and first roots, including rational
first-root values where an off-zero tuple requires them. It checks
all residuals, norm factors and complete finalizer formulas against
the actual saved parent sources.

The normalized correction for each core is the retained strong residual
times its auxiliary square difference. This distinguishes an equality
on restored zeros from an off-zero polynomial identity. The complete
polynomial is not asserted identical to the old unfused377 source.
The raw parent's separate canonical-AND and packing checks support the
fusion algebra; the proofs supply the actual positive witness maps.

Fixed-numeral roles receive consistent finite integer substitutions
throughout an audit. Those substitutions need not satisfy every
cross-role relationship of the actual huge coefficients. Positive
cases use recoder radix4 and divisor7 and check the positivity of the
restored coordinates. Neither the huge universal coefficients nor
full numerical Pell witnesses are expanded.

```sh
python3 neary_woods_universal_joint_and_units.py
```

Final review passed. The author writer and fresh default replay passed,
as did the root source integration, degree audit and fresh replay. Every
gate in the303-operation source is an ancestor of its final output.
Two independent reviewers checked the full proof, literal source and
fresh default replay without findings. One additionally checked192
complete output identities, including96 signed cases and276 half-integral
off-zero first-root coordinates. The other checked128 complete restored
raw-factor/output corrections, including64 signed cases and86 half-integral
off-zero first-root lifts. All13 local links in this note and its raw
parent note resolve. These algebraic checks supplement the positive
witness proofs above; they do not stand in for numerical Pell extensions.

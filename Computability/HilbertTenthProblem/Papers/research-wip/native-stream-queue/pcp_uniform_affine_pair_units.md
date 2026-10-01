# Twenty-four fewer operations for the complete affine-pair history

The [complete fixed-table affine-pair history](pcp_uniform_affine_pair_history.md)
has a successor with the same positive nonempty-word relation, **10
comparisons** and **3s+20 positive witnesses** for `s` fixed tiles. If its
parent certificate costs `C=M+A`, the new certificate costs `C+3`, and
the final polynomial costs **C+32=(M+13)M+(A+19)A**, exactly 24 operations
below the parent's `C+56` polynomial. All tile selection, radix, range,
transport, duration, and global bound obligations remain paid.

The illustrative three-tile interleaved source has **164=80M+84A**
certificate operations, **193=90M+103A** polynomial operations, 29 positive
witnesses, and degree **956**. The parent 217-operation degree-400 SOS
remains a lower-degree alternative. The contiguous successor costs
166/195 and has degree 782. Neither example is an instantiated universal
PCP alphabet or a new universal 75/88 bound.

The [source](pcp_uniform_affine_pair_units.py) is a distinct rewrite of
the frozen parent. It uses the same norm-unit and positive-definition
argument as the [recoder unit packet](native_binary_input_dilation_unit179.md),
on the history's single native AND kernel. It does not merge the
unrestricted checksums of two independent kernels into one product.

## 1. Three sign-safe norms and one checksum

Use native names without the `and__` prefix in this proof. Put

    q=16P^N, X=wq, Y=s_native*q, E=XY, V=XY^2,
    Delta=a^2+4a+3, T=i*c^2, U=j*c-(2r+1),
    Kaux=Delta*(f^2-1).

The full strong comparison `T^2=Kaux` is retained. Replace the main and
auxiliary right-side registers at their existing cost by

    N1=d^2-Delta*c^2;
    N3=Kaux*(U^2-y^2)+y^2.                              (1)

The auxiliary coefficient replacement agrees with the parent's `T^2`
coefficient on the retained strong equation; it is not an off-zero
polynomial identity. The exact difference is the strong residual times
`U^2-y^2`, and the checker includes that correction.

For every integer assignment `Delta` is 0 or 3 modulo four. Thus `N1`
is a square or a sum of two squares modulo four and cannot be -1.
Also `f^2-1` is 0 or 3, so `Kaux` is 0 or 1 modulo four. Accordingly
`N3` is `y^2` or `U^2` modulo four and cannot be -1. These exclusions
precede all positivity and native typing arguments.

Change the supplied positive first-root coordinate `tau` to a supplied
positive `g` and replace its six private gates by

    root_base=E*(kY);
    N0=g^2+4*root_base*(g-k).                            (2)

The literal schedule has four multiplications and two additions or
subtractions, including the fixed multiplication by four, just as in the
parent. `N0` is `g^2` modulo four and cannot be -1. Its positive zero
set is in bijection with the old triangular equation through

    g=2tau+1-2Vk;
    tau=Vk+(g-1)/2.                                     (3)

Indeed the old equation gives
`(2tau+1)^2=1+4V(V+1)k^2>(2Vk)^2`, so the first expression is positive.
Conversely `N0=1` makes `g` odd, and the second expression is a strictly
positive integer satisfying the old equation. The ratio equations and
both positive ratio slacks remain unchanged.

Finally replace the paid `sum F+1` checksum register by

    Qc=q-(F0+F1+F2+F3).                                 (4)

The three private right-side/checksum gates have no other consumers,
as checked against the actual source. Form

    W=N1*N3*N0*Qc.                                      (5)

This costs three additional multiplications. The single equation `W=1`
forces every factor to be an integer unit. The three unconditional
modulo-four exclusions force `N0=N1=N3=1`, and hence `Qc=1`. Restoring
the strong coefficient and (3) then restores all four old comparisons.
The reverse implication is immediate. No sign assumption about `Qc`
away from the zero set has been introduced.

## 2. Six positive definitions before kernel use

The parent already pays these definitions:

    s_native=2*odd_half+1;
    k=eta+zeta;
    c=kY+eta;
    a=E+Y;
    d=X+a*c+ga*(4a+3);
    r=F0+q*F1+q^2*F2+q^3*F3.                           (6)

Alias each supplied left side to its paid right-side register and
remove the six defining comparisons. No gate is removed or added for
this projection; a checked topological sort reorders dependencies.

Positivity here does not await the desired history interpretation.
For every positive supplied tuple, the parent wrapper computes
`J=sum Shat_i-s>=0`, `P=(B-1)J+1>=1`, and all decoded masks and selected
words are nonnegative. Thus its joined `Z>=0`, `F3=16Z+8>=8`, and
`q=16P^N>=16`. All expressions in (6) are consequently strictly
positive, including the packed index. This uses no AND equation, global
bound comparison, or Pell classification.

At a new positive zero, restore (6), use (5) to recover the norm signs
and oddness of `g`, and restore `tau` by (3). Every old coordinate is
positive and every old comparison holds. Conversely, an old positive
zero already has the values (6), and its positive root gap from (3)
gives a new zero. These maps are inverse. In particular all outer
history coordinates, all three relation parameters, and the selected
tile word relation are unchanged. Fresh native witnesses in the
parent's completeness proof are projected by this explicit bijection.

## 3. Literal polynomial and count

Let `R_1,...,R_9` be the remaining comparison residuals after replacing
the four old unit equations by (5) and removing (6). These include the
strong equation, both affine transports, the global positive bound,
and the remaining native index, linear, bound, and input-port equations.
The default output is the integer polynomial

    W*(1+sum_j R_j^2)-1.                                (7)

Its zero set is exactly `W=1` and `R_j=0`: the second factor is a
positive integer, so a product of it with the integer `W` can be one
only when both factors equal one. This final argument also does not
assume `W` positive on arbitrary assignments.

The operation ledger is

| Stage | Operations | Comparisons | Positive witnesses |
|---|---:|---:|---:|
|Complete raw parent|C|19|3s+26|
|Four-factor unit and six definitions|C+3|10|3s+20|
|Integer-product finalizer|C+32|one polynomial|3s+20|

Finalizing (7) costs ten multiplications and nineteen additions or
subtractions. The source also exposes the ordinary SOS of all ten
remaining comparisons, at exactly the same operation count. These two
outputs have the same integer zero set on the new coordinates, but are
different polynomials. Their equivalence with the raw parent uses the
positive coordinate bijection, not a claim of polynomial identity.

`rewrite(old,prefix=...)` checks the literal native gate patterns and
private consumers before applying the rewrite. `lift` and `project`
expose the two coordinate maps. `polynomial_source` exposes both paid
finalizers. A consumer composing several such kernels must retain
enough independent checksum equations; multiplying unrestricted
checksum factors from separate kernels would require a new sign proof.

## 4. Exact degree and verification

Retain the parent's scale exponent `N=3s+4` or `4s+4`, and set `d0=2N`.
Each supplied parameter and witness has degree one. With a star
denoting a highest homogeneous part, the positive definitions give

    q*=16(P*)^N,                    deg(q)=d0;
    a*=w*s_native* q*^2,            deg(a)=2d0+2;
    c*=k*s_native*q*,               deg(c)=d0+2;
    r*=q*^3*F3*,                    deg(r)=4d0-5.

Here `k=eta+zeta`, `s_native=2odd_half+1`, and `F3*=16Z*` are actual
computed forms. The native root `d` has highest part `a*c`, but the
leading squares in `N1` cancel. Expanding its next terms gives the
nonzero highest form `8*ga*a*^2*c*` of degree `5d0+7`.
The four factor degrees and highest forms are

| Factor | Degree | Highest homogeneous form |
|---|---:|---|
|N1|5d0+7|8 ga a*^2 c*|
|N3|12d0-4|4 a*^2 f^2 r*^2|
|N0|3d0+5|4 w s_native*^2 k (g-k) q*^3|
|Qc|d0|q*|

All these forms are nonzero polynomials on independent supplied
coordinates. In particular `g-(eta+zeta)` is not eliminated by a zero-set
equation. The product has degree `21d0+8`.

The retained strong residual `T^2-Kaux` uniquely has the greatest outer
degree `4d0+10`, with highest form `i^2*c*^4`. The packed-index bound
and auxiliary linear residuals have degree at most `4d0-5`; the index
equation has degree at most `max(4d0-5,2d0+3)`; input ports have degree
at most `d0-3`; the history residuals have degree at most three. Since
`d0>=14`, all are strictly below the strong residual.

Consequently (7) has exact degree

    (21d0+8)+2(4d0+10)=58N+28,                        (8)

and highest form `W* * i^4*c*^8`. The alternative SOS has exact degree
`2(21d0+8)=84N+16`. These are degrees of the literal polynomials without
substituting any comparison equation.

The [receipt](pcp_uniform_affine_pair_units.json) contains eight complete
ledgers and one full source. The author writer checks 512 full factor,
residual, integer-product, and SOS identities: 384 use positive integer
restorations with odd supplied gaps, and 128 use arbitrary signed
assignments, allowing a half-integral old root away from the equations.
All six omitted definition residuals are checked to vanish under the
literal substitution. Six independent weighted univariate audits check
the exact factor degrees and leading coefficient; they do not expand
the unnecessarily large final polynomial. These finite identities are
not claimed to instantiate full numerical Pell zeros.

Independent final proof/source/default reviews by `reduce_complete75`
and `substrates` both passed without findings. The former additionally
checked 256 signed complete restoration/output identities on separate
singleton and nondyadic two-tile tables. The latter checked 192 complete
outputs against direct scalar norm formulas with positive even gaps,
explicitly allowing half-integral restored roots away from the zero
set. Both reviews verified the retained strong equation, pretyping
positivity, unit signs, literal ledger, and highest-degree forms.

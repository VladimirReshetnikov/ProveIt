# Two positive-gap shears and exact operation/degree tradeoffs

This note certifies arithmetic and coordinate changes on the authentic
Start-only compiler slice. The ordinary-strong transfer theorem is a
separate dependency; no arbitrary fixed coefficient values are licensed.

## Ordinary baseline

Keep the fifteen positive variables and the main/outer definitions of
Start-only67. Write V=c(Tf-1)-Rf^2. Replace normalized auxiliary/strong
factors by

    I=ic^2, Qordinary=Delta(f^2-1),
    NA=Qordinary(V^2-y^2)+y^2,
    NS=1+I^2-Qordinary.

Then Pordinary=N1 N2 NA NI NT NS-1 uses 69=39M+30A operations and has
exact factor degrees 22,18,28,7,2,22, summing to99. This is the ordinary
strong variant, whose rank theorem does not assume Delta divides i.

## Two gap coordinates

Let L=E(kY). Replace the supplied first root tau and auxiliary root y
by new positive variables t and e respectively, with proof maps

    tau=L+t, y=V+e.

Use these exact substitutions in all factors, leaving all other supplied
coordinates unchanged. They add one binary addition each, hence the
complete ordinary circuit has 71=39M+32A operations.
The resulting first factor and auxiliary factor simplify algebraically to

    N1=t^2+L(2t-k),
    NA=Qordinary(-2Ve-e^2)+(V+e)^2.

The literal circuit retains the cheaper shared-square schedule: it does
not expand the latter displayed expression operation by operation.

## Positive zero-set bijection

For an old positive zero, first and auxiliary factors are1. Thus

    tau^2-L^2=Lk+1>0,
    y^2-V^2=(V^2-1)/(Qordinary-1)>0.

The old positive theorem gives V>1 and Qordinary=I^2>1. Consequently
t=tau-L>0 and e=y-V>0. The exact substituted polynomial vanishes.

Conversely, take a positive sheared zero. Restored tau=L+t is positive,
but it would be wrong to assume restored y=V+e positive off zeros.
The integer-unit argument first gives NS=1, since Qordinary is0 or1
modulo4 and NS cannot be-1. Therefore Qordinary=I^2>1.
The auxiliary factor also cannot be-1 modulo4. If V+e=0, NA=1 would
force Qordinary V^2=1, impossible. Thus |V+e| is positive. Because the
old source uses y only through y^2, tau=L+t and y=|V+e| restore a full
old positive zero. Its theorem gives V>1. Hence V+e>0 after all, so the
absolute value is unnecessary on the zero set.

The inverse substitutions are consequently genuine inverse bijections
between complete positive integer zero sets, not just canonical examples.
This proof uses the old theorem only after all of its positive witnesses
have been restored.

## Exact degrees and a nonzero leading form

Let Q0=beta J, k0=eta+zeta,
T2=w(Q0-F-alpha)-zQ0. The sheared factor degrees are

    12,18,22,7,2,22.

Their sum is83. The main factor's degree18 uses its standard leading
cancellation. The first leading form is
w k0 s^2 Q0^7 (2t-k0), and the auxiliary leading form is
-2w^2 k0 s^3 Q0^11 T f^3 e.
Thus the complete product has leading homogeneous form

    16 h gamma i^2 w^6 s^13 k0^7 Q0^45
       T f^3 e (2t-k0) T2.

Every displayed factor is nonzero for beta>0. The final constant cannot
cancel it, so degree83 is exact uniformly on every authentic compiler slice.

The six comparisons N1=N2=NA=NI=NT=1, I^2=Qordinary take63 operations,
maximum degree22. Their sum of six squared residuals takes80 operations
and has exact degree44. This is a lower-degree but slightly larger system
than the unsheared ordinary six-comparison source (61 operations,
maximum degree28, sum-of-squares degree56).

For reference, applying both shears to normalized67 gives69 operations
and degree139, not133: its auxiliary factor drops from degree60 to54,
not48, because its square coefficient has degree46. That normalized
point is dominated here by ordinary69/degree99; it is retained only as
an arithmetic cross-check.

## Files and verification

The newly authored build_sheared_tradeoffs.py reads the prior circuit as
inert JSON, imports no received source program, verifies all registers,
ports, liveness and ledgers, performs100 complete signed coordinate
identity checks per sheared circuit, and independently expands two dense
modular affine univariate specializations attaining each exact degree.
The files are start_only_ordinary69.json, start_only_ordinary_sheared71.json,
start_only_sheared69.json and sheared_tradeoff_audit.json.

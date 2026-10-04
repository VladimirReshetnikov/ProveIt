# Rational reconstruction at the all91 strong-root boundary

This bounded scout confirms that the fixed-polynomial absorption theorem
does **not** extend to arbitrary rational substitutions on the same all91
boundary. One fixed quotient of integer polynomials reconstructs `f` at
every original full positive zero. This is a zero-locus identity, not a
new arithmetic program, witness reduction or operation bound.

## Source binding and rational identity

The source is `complete84_scaled_strong_output.json`, SHA256
`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
The companion read is SHA256
`01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`.
The accepted all91 companion read is
`complete84_full_independent_root_absorption.md`, SHA256
`1280fb32702c4ec99f69807ee4b6fd0bdbd5f83830e5187c41bfbc81da7935b7`.
All files were read inertly; no predecessor helper was executed or imported.

Use the actual source names

    Delta=A, c=R10a, c²=c2, R=r_lhs,
    T=auxiliary_quotient, y=y_aux, y²=aux_y2,
    S=aux_coefficient_root=Delta*i*c², Q=R16=S².

The displayed numerator below is called `A_rat` to distinguish it from
the source register `A=Delta`. Define fixed integer polynomials

    D = 1+Delta*i²*c⁴ = 1+(i*c²)*S,
    b = c+R*D,
    A_rat = Q*(c²*D*T²+b²) − (Q−1)*y² − 1,
    B_rat = 2*Q*c*T*b.

All arguments belong to the established E88 boundary together with
`T,y,y²`; neither polynomial depends on `f`. The fresh source census
finds exactly 67 computed and 24 supplied f-independent values. It binds
`c²,S,Q` to their actual dependent producers rather than treating them as
independent witnesses.

The actual two factors are

    V=c*T*f−c−R*f²,
    Na=Q*(V²−y²)+y²,
    Ns=Delta*f²−Q.

At a full positive zero in an inherited valid fixed-program slice,
the accepted parent theorem gives `Na=1`, `Ns=Delta` and `R>0`.
Hence `f²=D`, `V=c*T*f−b`, and expanding `Na=1` yields

    A_rat = B_rat*f.                                  (1)

In particular `B_rat>0` there, since all of `Q,c,T,b` are positive.
The quotient `A_rat/B_rat` therefore equals the original positive integer
`f` at every such zero, with the same remaining supplied values.

There is even no denominator pole on the full positive supplied-port
domain before imposing the polynomial: `Delta,c,i,T` are positive,
`D=1+Delta*i²*c⁴>c`, and `R` is an integer. Thus `b=c+RD` cannot
vanish, since `0<c<D`; consequently `B_rat != 0`. Its sign outside
the original zero set is not asserted positive.

For an exact algebraic check, put `E=f²−D`. The fresh helper proves
coefficientwise over the integers that

    Ns−Delta = Delta*E,
    Na−1−(A_rat−B_rat*f)
      = Q*E*(c²*T²−2*R*c*T*f+2*R*b+R²*E).             (2)

Thus (1) uses actual unit equations, while (2) is an all-ring identity.
The source boundary, all auxiliary producers and complete original
finalizer are independently expanded and bound in the fresh evidence.

The all91 theorem permits only a fixed integer polynomial `G`. If it
instead permitted any fixed rational function, this particular quotient
would retain every original accepting input, including an infinite
ordinary-input language for a suitable valid program. Its finite-input
conclusion would therefore fail. There is no conflict with the rational
E88 bound inside the all91 proof: the numerator and denominator here also
use the auxiliary quotient and ordinate. Clearing the denominator is
not a free operation or a proof of a new integer-polynomial compiler.

## What the squared elimination does and does not give

Set `K=A_rat²−D*B_rat²`. It is necessary at every original positive
zero. For integer values with `B_rat != 0`, `K=0` does imply that
`A_rat/B_rat` is an integer: write the fraction in lowest terms `p/q`.
The equality `p²=D*q²` and coprimality force `q=1`. Hence no separate
divisibility condition is needed for this local square-root step.

The positive sign remains an issue. A local exact diagnostic is

    Delta=8, c=i=R=1, T=81, y=255,
    D=9, Q=64, b=10,
    A_rat=−311040, B_rat=103680.

Here `K=0` reconstructs `f=−3`; the original local expressions give
`Na=1` and `Ns=8=Delta`. Every listed parameter other than the reconstructed
f is positive. This refutes automatic positivity from these local
equations alone. It is **not a native full tuple**: for example `c=1`
cannot equal the actual `R10a=ksn2+eta` on positive source ports. No
counterexample to the full positive compiler or its parent theorem is
claimed. The local diagnostic does not settle whether some stronger set
of remaining native constraints could restore the sign.

The full source has only two direct f consumers, `L16=f*f` and
`auxiliary_Tf=T*f`, but removing them also affects the auxiliary/strong
factors and their product finalizer. Let `P5` be the product of the five
f-independent first, main, input, index and transport factors. The actual
source is `F84=P5*Na*Ns−Delta`. Modulo `E=0`, its equation is

    F84 = Delta*(P5*(A_rat−B_rat*f+1)−1).

The helper verifies this statement by an explicit polynomial multiple of
E. Eliminating f from this entire equation instead produces the distinct
candidate condition

    [P5*(A_rat+1)−1]² − D*(P5*B_rat)² = 0.

It is not the same polynomial as K. Neither replacing the two local unit
equations by K nor using this whole-output resultant automatically
supplies a positive reconstructed f, retains every required implication
of the other source factors, or proves the signed-T compiler theorem.
Those obligations must be resolved before any universal-source claim.

## A paid local ledger, without a complete compiler claim

At the already computed boundary
`Delta,c,c²,i,S,Q,R,T,y²`, a division-free schedule computes the quotient's
numerator and denominator using

    k=i*c²; D=1+k*S; b=c+R*D; u=c*T;
    A_rat=Q*(D*u²+b²−y²)+y²−1;
    v=Q*u*b; B_rat=v+v.

These producers cost **17=10M+7A**. Computing `A_rat²−D*B_rat²`
adds **4=3M+1A**, for a local **21=13M+8A** schedule. All 21 rows
are explicitly emitted and live in the fresh receipt; the helper checks
their polynomials against the formulas above. Doubling uses one paid
addition. No variable division occurs in this local schedule.

This ledger excludes the cost of supplying that computed boundary, the
remaining source constraints and finalizer, and any necessary sign
certificate. It cannot be subtracted from 84 as though those parts were
free. There is no 17-witness universal polynomial, complete operation
saving, or fresh accepting native tuple in this scout.

Fresh standard-library evidence is retained in
`complete84_rational_root_scout.py` and `.json`. Normal and `-O` executions
produced byte-identical receipts. This checks exact source/formal
identities, the all91 census, the local 21-row schedule and the stated
negative-root component example; it does not execute or certify a new
universal compiler. Helper SHA256:
`7d7766f6536be28a3819d1764a4fbb31f70ce91f47a313fd22d57384787cde06`.
Receipt SHA256:
`ab7e0a11e9cc04b961085a2dae6b94eff43761c155cdae2ace4a4b29a29348c2`.

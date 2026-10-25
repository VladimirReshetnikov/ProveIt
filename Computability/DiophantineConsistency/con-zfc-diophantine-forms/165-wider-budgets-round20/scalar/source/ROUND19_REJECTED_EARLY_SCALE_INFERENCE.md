# Rejected scalar simplification: carrier divisibility alone does not restore scale

The proposed deletion of the free-scale strengthening
`Budget=Y^2 B0-k^2 q^8`, replacing it by `Budget=B0`, is **not accepted on
the proposed early-scale argument**. This is a counterexample to that
intermediate arithmetic lemma, not a counterexample to a complete calibrated
Diophantine equation.

The carrier does give

    2q^3 | H(Y-q^3),    H=4(X+1)Y+3,    X=qW.

It follows that `q^3|HY`. Also `gcd(H,Y)=gcd(3,Y)` and `gcd(q,3)=1`.
These facts **do not** imply `q^3|Y`, or even `q|Y`. A prime dividing `q`
may occur in `H` and not in `Y`; the gcd fact only prevents its occurrence
in both factors. Modulo an odd prime dividing `q`, the alternate branch is
`Y=-3/4`, not necessarily zero.

A fully explicit counterexample is

    q=20, W=4, X=80, Y=1728,
    H=559875, M=2q^3=16000.

Here `q` is even and equals 2 modulo 3; `X` is zero modulo 8 and equals
2 modulo 3; `|X|=4|q|`; `H=4(X+1)Y+3` is odd; `gcd(q,3)=1`; and
`gcd(H,Y)=3`. Nevertheless

    H(Y-q^3)/M=-219471

is an integer while `q` does not divide `Y`, and `|Y|=1728<8000=q^3`.

The obstruction is not confined to small illustrative bases. For any even
`q` coprime to 3 with odd part `d>1`, write `q=2^a d`. With any `W` and
`X=qW`, the number `4(X+1)` is invertible modulo `d^3`. By CRT choose `Y`
such that

    Y=q^3 modulo 2^(3a+1),
    Y=-3/[4(X+1)] modulo d^3.

The second congruence is merely a proof notation for the modular inverse.
Then `d^3|H`, while no prime dividing `d` divides `Y`. Together with the
first congruence this gives `2q^3|H(Y-q^3)`, but not `q|Y`.
The authentic affine family contains bases with odd part greater than one:
at `j=1`, `q=7(2^1064921-1)+1=2(7*2^1064920-3)`.

The inherited free-scale proof deliberately restores full scale only after
its large-base projector proves `q` is a power of two; then odd `H` is
indeed coprime to `2q^3`. Using that later conclusion to justify removal
of the pre-projection magnitude guard would be circular. Likewise the
proposed map to the old weak-scale frame uses `v_weak=Y/q` and cannot be
invoked before proving that quotient integral by a different valid route.

An independent alternative argument could still make a different candidate
work. Exact degree or gate savings alone do not supply that missing
calibration, so no lower-degree consistency endpoint follows from this
rejected inference.

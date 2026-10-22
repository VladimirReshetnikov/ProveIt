# Signed-coordinate improvements for the normalized blank certificate

The source is `06-blank67` at ProveIt
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.
This note concerns ordinary mathematical proofs, not a new formalization.

## Freeing h

Keep every source-positive coordinate positive except allow h to be any
integer. Unit extraction and the transport argument are unaffected.
The source outer bounds give `E>R+2`, `R>3q`, and `q>=16`.
The index unit gives `k=R+epsilon+hE`, with `epsilon` equal to 1 or -1.
Since k is positive, h cannot be negative. If h=0, then k=R+epsilon.
The first norm has the classification
`k=2 psi_P0(n)`, `P0=2XY^2+1`, n>=1.
For n=1 this gives k=2, contradicting R>3q. For n>=2 it gives
`k>=4P0>R+1`, since `P0>E>R+2`. This also contradicts h=0.
Thus h is automatically positive and the original proof continues.

## Freeing gamma

Allow gamma to be any integer and D accordingly signed. The main norm
still gives `|D|=chi_A(p)` and `c=psi_A(p)`, p>=1. Everything through
signed auxiliary index recovery uses c, not the sign of D, and yields
`p=R`, `n=(R+1)/2`, and `r=(R-1)/2>=2`.
The lower-ratio estimate is unchanged:

    Y > X^r/3,     a=Y(X+1)>X^(r+1)/3.

Since X>=16 and r>=2, `(X/4)^r>6`, and hence

    0 < X 2^R = 2 X 4^r < a.

Modulo `H=4a+3`, one has `Delta=a^2` and
`A+a=2a+2=2^(-1)`, whereas `A-a=2`. The Pell addition identities
therefore imply

    chi_A(R)-a psi_A(R) = 2^R (mod H),
    chi_A(R)+a psi_A(R) = 2^(-R) (mod H).

If D were negative, the defining equation `D=X+ac+gamma H` would give
`X 2^R=-1 (mod H)`. This contradicts `0<X 2^R<a<H-1`.
Therefore D is positive. The ordinary comparison of two positive
representatives below H now recovers `X=2^R`, and the remainder of the
source proof is unchanged. Gamma need not be separately proved positive.
For completeness the original positive gamma remains available.

## Signed f,T,tau,y

The source audit's odd-quotient proof does not require V positive.
With normalized strong norm, let `|f|=chi_A(m)`,
`psi_A(m)=|i|c^2`, and `rho=Delta |i| c^2`.
Then `pc|m`, `m>2p`, and `c|m`.
The auxiliary norm yields

    V = sigma Q_u(rho^2),   ell=2u+1,   sigma in {1,-1}.

The exact polynomial V gives `V=-c (mod f)` and `V=-R (mod c)`;
the latter follows from `f^2=1 (mod c)`.
Consequently

    sigma (-1)^u psi_A(ell)=-c (mod |f|),
    sigma (-1)^u ell=-R (mod c).

Squaring the first congruence, then applying chi step-down as in the
source audit, gives `ell=+p or -p (mod m)`, hence modulo c.
The second gives `R=+p or -p (mod c)` and therefore p=R using
`0<p,R<c/2`. Neither positivity of T nor positivity of f was used.
The norms exclude f=0, tau=0 and y=0 when i is nonzero.

## Odd normalized i for completeness

Root's construction uses `m=cR` instead of the source `m=2cR`.
Expand `(D+c sqrt(Delta))^c`: its odd terms show
`c^2 | psi_A(cR)`. Under the canonical conditions, A is even,
R is odd, `c=psi_A(R)` is odd, and thus m and psi_A(m) are odd.
Therefore `i=psi_A(cR)/c^2` is odd and positive.
The canonical quotient V has both required minus congruences because
R=3 mod4; this does not require m to be even.
Thus i can be written `2r+1` with r an unrestricted integer, excluding
the degenerate i=0 branch and permitting the signed-rank proof above.

## A square w and its zero boundary

If the canonical tableau dimensions are powers of five, N is odd; d is
also odd. Canonical R is odd, and `w=2^(R-dN)` is a positive square.
Set `w=u^2` with u unrestricted. Completeness is preserved.

There is a direct zero exclusion, identified by the independent audit.
If u=0 then X=E=0 and a=Y>=q^3>0. Since D=ac+gamma H and
Delta=a^2+H, the main norm is divisible by H:

    D^2-Delta c^2 = H(2ac gamma + gamma^2 H-c^2).

But H=4Y+3>1, whereas the main factor must be a unit (or explicitly 1
in the system). This is impossible. Thus u is nonzero before any rank
argument. The same exclusion works for the ordinary strong certificate.

## Metric accounting

Freeing h,gamma,f,T,tau,y converts 15 positive coordinates to 9 positive
and 6 unrestricted. Parametrizing each positive coordinate with
`1+x^2+y^2+z(z+1)` gives 33 unrestricted integer coordinates.
Replacing i by an odd signed coordinate gives 31 at two extra gates.
The square-w construction gives 29 at one further gate.
This note does not assert that 29 is minimal.



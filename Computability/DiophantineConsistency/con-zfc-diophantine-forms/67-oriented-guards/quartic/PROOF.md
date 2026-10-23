# A quartic in 42 unrestricted integers by orienting a shared sign guard

## Exact object and scope

`quartic42.json` lists 42 unrestricted integer unknowns and 27 quadratic
residuals. The single equation is their sum of squares equal to zero.
`quartic42_expanded.json` is its exact 391-term symbolic expansion, with
four fixed ports left as coefficient symbols. Their values are fixed by the
whole package34 mixed-parity-unrounded-1064921 tuple, not selected by a
consistency assumption. Its exact total degree is four: the coefficient of
tau^4 is one even on the actual fixed coefficient slice.

This improves the incoming 45-integer quartic by three unknowns and one
quadratic residual. It does not compete with the much higher-degree
nine-positive or ten-integer variable counts. No global minimum is claimed.
The conclusion is the ordinary mathematical theorem formalizable in ZFC:
this quartic has no integer zero if and only if Con(ZFC). The proof imports
the identified Q45/native-compiler calibration and Pell arithmetic; it is
not a new end-to-end Lean/Rocq or object-language proof artifact.

The incoming Q45 is copied verbatim at `upstream/q45/quartic45.json`, along
with its complete proof and original source/payload subtree. `SOURCE_PINS.json`
authenticates all49 retained files and the original archive. The coefficient
manifest paths in our emitted JSON are adjusted to this retained subtree.
The four ports are beta=2^1064921-1, K0=K, MC, and the already shifted MF_source.
No individual port is replaced from any smaller tuple.

## 1. Two exact changes

Retain all Q45 arithmetic residuals, its dyadic radix guard, and its two
simplex product guards. Change its square-scale equation

    w=u^2

to

    w=4u^2.                                             (A)

Delete the separate ternary positivity representations for eta and zeta,
including their six private variables, and replace them by

    eta*zeta=1+p1^2+p2^2+p3(p3+1).                       (B)

Every right-hand value in(B) is positive; every positive integer is
represented. For the latter statement, Legendre's three-square theorem
represents4n-3, which is1 mod4 and is not4^a(8b+7). The three squares have
one odd and two even entries, yielding this expression after dividing by4.
Thus(B) gives eta,zeta nonzero of the same sign, not their individual
positivity. Proving the missing orientation is the new point.

The counts are45-6+3=42 unknowns and28-2+1=27 residuals. Equation(A) adds
no unknown or residual and preserves quadratic degree. The unchanged
quadratic lift is interpreted exactly as in Q45; its auxiliary registers
are not deleted or silently expanded into higher-degree residuals.

## 2. Ordered preliminary bounds

At a quartic zero all residuals vanish, because they are integer squares.
Let q=beta J+1 and C=q-F-alpha. The unchanged guard q=2v^2 gives J>0:
J<=-1 would make q negative, and J=0 would give1=2v^2. Hence q>=16.
The unchanged positive products F alpha>0 and F C>0, together with
F+alpha+C=q>0, give F,alpha,C>0.

The unchanged arithmetic lift provides the abbreviations and identities

    s=2v_scale+1, i=2r+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=(X+1)Y, H=4a+3,
    Delta=(a+2)^2-1, D=X+ac+gamma H,
    k=R+1+hE,
    V+c=fo, V=jc-R,
    tau^2-(XY^2)(XY^2+1)k^2=1,
    D^2-Delta c^2=1,
    (i c^2)^2=Delta(f^2-1),
    (i c^2)^2 V^2-((i c^2)^2-1)y^2=1.

Here R is the same explicit native mask polynomial as in Q45. Its bounds
follow from q,F,alpha,C, the complete fixed tuple, and the mask identities:

    q(q^2-1)<R<q^4-2.                                   (C)

This uses neither z>0 nor any sign of h,s,k. The quotient z is not used in
the sign-orientation proof. All four fixed ports remain the Q45 ones.

Since s is odd, Y is nonzero and Z=|Y|>=q^3. If u=0, then X=0,
a=Y and D=ac+gamma H. Reducing the main norm modulo H gives0=1 modH,
because Delta=a^2+H. But |H|=|4Y+3|>1, a contradiction. Thus u!=0.
Equation(A), rather than the old w=u^2, now gives

    X>=4q, |E|=XZ>=4q^4>3R+1.                          (D)

This bound is obtained before any Pell index or power-of-two recovery.
It is what removes the previously problematic negative common-sign branch.

From(B), write sigma=sign(k), k0=|k|, eta0=|eta|. Then
0<eta0<k0, k0>=2. Put c0=|c|. For Y>0,
c0=k0 Z+eta0; for Y<0, c0=k0 Z-eta0. In either case

    k0(Z-1)<c0<k0(Z+1), hence c0>k0.                    (E)

Let B=|a+2| and P0=2XY^2+1. Then

    B>|E|>R, Delta=B^2-1, P0>B>=2.                      (F)

Indeed B>XZ because Z>2, and2XZ^2+1>(X+1)Z+2 for our ranges.

## 3. Recover positive ranks without presupposing the common sign

Standard Pell classification for the consecutive-product norm and the
main norm gives positive indices n,p with

    k0=2 psi_P0(n), |tau|=chi_P0(n),
    c0=psi_B(p), |D|=chi_B(p).

By(E), P0>B, and monotonicity of psi, one has p>n.
Since P0=1 mod|E|, the polynomial Pell recurrence gives
psi_P0(n)=n mod|E|. Therefore the retained index equation gives

    2n = sigma(R+1) mod |E|.                            (G)

If sigma=+1,0<R+1<|E| implies n>=(R+1)/2. If sigma=-1, then
2n>0 implies2n>=|E|-R-1, and(D) gives n>R. Both alternatives imply
n>=24 from(C). Consequently p>=25, and the standard Pell growth bound
psi_B(p)>=(2B-1)^(p-1) gives

    c0>B Delta^2, c0>2p, c0>2R.                         (H)

In particular, the size hypothesis of the inherited ordinary strong-rank
lemma has been proved in both sign branches. It was not borrowed from the
positive-k source theorem.

## 4. Signed auxiliary recovery gives p=R

Put f0=|f|. The ordinary strong equation, i!=0, and(H) imply, by the
retained relaxed-rank lemma,

    f0=chi_B(m), p|m, c0|m, m>2p.

Let rho=|i| c0^2>1. Then rho^2=Delta(f0^2-1), and the auxiliary equation
is rho^2 V^2-(rho^2-1)y^2=1. Its classification gives an odd index
ell=2j0+1 and a sign e with V=e Q_j0(rho^2). The unchanged exposed quotient
equations give

    V=-c mod f0, V=-R mod c0.

The standard odd-Chebyshev identities are
Q_j0(1-B^2)=(-1)^j0 psi_B(ell) and Q_j0(0)=(-1)^j0 ell.
Since rho^2=1-B^2 mod f0 and rho^2=0 mod c0, squaring the first
congruence removes both signs e and sign(c). Pell duplication and signed
step-down give ell=+p or-p modm. The second congruence then gives
R=+p or-p modc0, because c0|m. By(H),0<R,p<c0/2, hence

    p=R.                                               (I)

This is precisely the sign-insensitive part of the inherited signed-rank
proof. It needs neither Y>0 nor c>0 nor the sign of f,V,y,gamma. The retained
sources `ODD_SCALE_27_PROOF.md` and `SIGNED_DOMAIN_29.md`, in the Q45 subtree,
state the relevant quotient and step-down interfaces. We have supplied the
new growth argument needed to apply them with a possibly negative k.

If sigma=-1, section3 gives n>R, contradicting p>n and(I). Thus k>0.
Together with eta*zeta>0 and eta+zeta=k, this gives eta,zeta>0.

## 5. Literal transfer to Q45 and consistency

We can now map this solution to the old Q45 solution without doing any
further power recovery ourselves. Keep every original arithmetic variable,
replace its square-scale witness by u_old=2u, and choose the standard
ternary representations of the now-positive eta and zeta. Then all old
Q45 residuals vanish exactly. In particular w=u_old^2 and the two old
positivity equations hold. Q45's proved soundness supplies all its remaining
sign, quotient and native-window conclusions and yields a finite ZFC
refutation. Invoking Q45 before proving eta,zeta>0 would have been circular;
it is invoked only here.

Conversely, start from a finite ZFC refutation and use Q45's canonical
compiler witnesses, not an arbitrary old solution. Its coherent tuple has
q=2^t with t odd, final rank R=3 mod4, and w=2^(R-t). The standard bounds
R>3q and q>=16 imply R-t>=2, while R and t odd make R-t even. Hence

    u=2^((R-t-2)/2)

is an integer and w=4u^2. Represent eta*zeta>0 by(B), retain all other
canonical variables, and obtain a zero of the new quartic. This is an
existential cofinal restriction, not a claim that4 divides every old w.

Both directions establish the asserted equivalence in ordinary mathematics
formalizable in ZFC. Negation gives unsolvability iff Con(ZFC); neither side
is asserted to hold unconditionally.

## 6. Checkable artifact and limits

`build_verify.py` authenticates49 source/payload files, builds all27 literal
quadratic residuals, expands their sum of squares in exact sparse arithmetic,
checks every supplied variable is live, and verifies the coefficient of
tau^4 is1. Actual raw/gzip payload hashes are checked as one tuple. Finite
scale examples are diagnostics only; the inequalities above prove the
universal branch ordering. Independent mathematical and code reviews are
separate from the builder. No upstream program is executed by this builder.

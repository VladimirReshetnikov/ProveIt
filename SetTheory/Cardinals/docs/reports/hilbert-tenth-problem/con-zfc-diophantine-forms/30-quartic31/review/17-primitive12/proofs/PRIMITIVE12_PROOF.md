# Twelve positive unknowns by a separated primitive element

Notation: this standalone note calls the eliminated **norm** `P12`.
The article calls that norm `R_norm` (mathcal R) and reserves `P12`
for the finalized product in equation (4) below. The constructions agree.

This note builds on the fixed blank native-window/Pell interface at ProveIt
commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. It is an ordinary
mathematical proof, not a newly checked Lean/Rocq derivation. All four
coefficient ports must come from one compatible compiler recipe, including
its shifted `MF` port. The construction applies to the T4 recipe or to any
new whole tuple satisfying the same stated compiler and mask bounds.

The new point is to eliminate **four** supplied root coordinates
`gamma,tau,y,f` and replace them with one positive integer `t`. The
resulting system has twelve positive unknowns and three equations. Its
supplied arithmetic circuit has 163 binary operations and maximum degree
2592. A product finalizer gives one polynomial of degree 2601 with 167
operations. This improves the supplied-variable count, not the degree or
arithmetic-operation frontier.

## 1. Common prefix and outer equations

The twelve unknowns are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t > 0.

Use the inherited fixed ports `Bm1=B-1,Kconstant,MC,MF`, with `MF` shifted.
Define substituted polynomials (none is an additional unknown):

    q = Bm1 J+1, Cword=q-F-alpha,
    X=wq, Y=sq^3, E=XY, k=eta+zeta,
    c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(Kconstant+w)Cword+q-F-z(q-1),
    ell=E(kY), A=1+ell(ell+k),
    I=i c^2, D=1+Delta I^2,
    Q=(Delta I)^2, d=Q-1,
    v=cT, Z=c+RD,
    e=Q(Dv^2+Z^2)-1, Broot=2QvZ,
    b=X+ac, G=Delta c^2+1.

The three equations will be `Nk=1, Nt=1, P12=0`.

The inherited weak transport/index bootstrap also works with `Nk,Nt` each
in `{+1,-1}`. It establishes `Cword>=0`, `q>=16`, `0<R<E-2`, and hence
all the positive quantities needed below. In particular `X>=16`,
`Y>=4096`, `c>1`, `Delta>0`, `I>1`, `D>1`, `Q>1`, and `d>0`. This
bootstrap does not use a root which the present construction has deleted.

## 2. An integrality lemma for a rational auxiliary Pell coordinate

**Lemma.** If `a0>1` and `V` are integers and `y` is rational, then

    a0^2 V^2-(a0^2-1)y^2=1

implies `y` is an integer.

**Proof.** Write `a0^2-1=d0 s0^2` with `d0>1` squarefree and `s0>0`.
Put `r=s0 y`. The equation gives `d0 r^2=(a0 V)^2-1`, an integer.
The denominator squared of `r`, in lowest terms, divides the squarefree
integer `d0`, so `r` is an integer.

Let `u+v0 sqrt(d0)` be the fundamental positive integer solution of the
norm-one Pell equation. Write

    a0=chi_u(n), s0=v0 psi_u(n),
    |a0 V|=chi_u(m), |r|=v0 psi_u(m).

Here `m,n>=1`. For completeness, the first-coordinate divisibility fact

    chi_u(n) divides chi_u(m)  =>  m/n is an odd positive integer

has a short direct proof. The Pell addition identities give

    chi_u(2n+j) = 2 chi_u(n) chi_u(n+j)-chi_u(j),
    chi_u(2n-j) = 2 chi_u(n) chi_u(n-j)-chi_u(j).

Reduce `m` modulo `2n` and use the second identity to reflect the
remainder into `[0,n]`. Modulo `chi_u(n)`, the value `chi_u(m)` is then
plus or minus `chi_u(r0)` for `0<=r0<=n`. Strict increase gives
`1<=chi_u(r0)<chi_u(n)` whenever `r0<n`; divisibility therefore forces
`r0=n`, equivalently `m=(2j+1)n`.

Composition of Pell sequences gives
`psi_u(m)=psi_u(n) psi_{a0}(2j+1)`. Consequently
`|r|=s0 psi_{a0}(2j+1)`, and `|y|=psi_{a0}(2j+1)` is an integer. QED.

The lemma is essential. A general nonmonic integral quadratic can have a
nonintegral rational root; no such general assertion is being used.

## 3. The sixteen algebraic root tuples

Temporarily work in an algebraic closure of the rationals. Consider the
sixteen tuples `(gamma,tau,y,f)` satisfying

    (H gamma+b)^2=G,
    tau^2=A,
    f^2=D,
    d y^2=e-Broot f.

There are two choices for each successive coordinate. The last radicand
is never zero. Indeed, if `e-Broot f=0`, then `f=e/Broot` is rational
(here `Broot>0`), and `f^2=D` makes `f` an integer. But substitution would
give

    Q(vf-Z)^2=1,

which is impossible because `Q>1` and `vf-Z` is an integer.

The same argument shows that the integer

    N=e^2-Broot^2 D

is nonzero. The `y` coordinates are permitted to be complex during this
argument. All bounds below are bounds on complex absolute values.

## 4. Explicit separating weights

Define

    g=c+X, u=ell+k,
    C=v^2+D+Z,
    r=(a+2)I,
    C2=v+c+Rr,
    S=u+g,
    wy=Q C S+1,
    wf=2 wy C2+S+1.

All are integer substituted polynomials. For every algebraic tuple above,

    |gamma|<g, |tau|<u, sqrt(A)>g,
    1/(Q C)<|y|, |y|/sqrt(D)<2 C2.

Here are the details.

* Since `G=Delta c^2+1` and `Delta=(a+2)^2-1`, we have
  `sqrt(G)<(a+2)c`. Therefore
  `|gamma|<((2a+2)c+X)/(4a+3)<c+X`.
* `u^2-A=ell k+k^2-1>0`. Also `sqrt(A)>ell` and
  `ell=kXY^2>c+X`: use `c<k(Y+1)`, `X>=1`, `Y>=2`, `k>=2`.
* The arithmetic-geometric mean inequality gives
  `v sqrt(D)+Z<C`. Thus
  `e+Broot sqrt(D)=Q(v sqrt(D)+Z)^2-1<Q C^2`.
  Because the product of the two nonzero conjugates
  `e +/- Broot sqrt(D)` is a nonzero integer, each has absolute value
  greater than `1/(Q C^2)`. Since `d<Q`, this gives
  `|y|>1/(Q C)`.
* From `Q/d<2`,
  `|y|/sqrt(D)<sqrt(2)(v+Z/sqrt(D))`.
  Since `r^2-D=I^2-1>0`,
  `Z/sqrt(D)=c/sqrt(D)+R sqrt(D)<c+Rr`, which proves the final bound.

The sixteen numbers

    gamma+tau+wy y+wf f                                      (1)

are pairwise distinct. Compare two tuples, starting with their highest
coordinate in the order `f,y,tau,gamma`.

If `f` differs, its weighted difference is `2 wf sqrt(D)`. All lower
differences together have absolute value less than
`4 wy C2 sqrt(D)+2S`, which is smaller by the definition of `wf`.
If `f` agrees but `y` differs, its weighted difference is greater than
`2 wy/(QC)>2S`, whereas the remaining two differences are less than
`2S`. If only `tau` and perhaps `gamma` differ, the `tau` difference is
`2 sqrt(A)>2g`, larger than the possible `gamma` difference. Finally,
if only `gamma` differs, its difference is nonzero. This proves explicit
separation without a genericity or unquantified weight assumption.

## 5. A division-free polynomial with precisely these roots

In the free rank-four algebra

    Z[f,tau]/(f^2-D,tau^2-A),

set

    zeta0=Ht+b-H wf f-H tau,
    qy=H wy,
    Raux=e-Broot f,
    K=d(zeta0^2+G)-qy^2 Raux,
    E0=K^2-4 d^2 G zeta0^2.

Define the norm operations by polynomial multiplication and reduction:

    Norm_tau(U)=U(f,tau) U(f,-tau)  reduced using tau^2=A,
    Norm_f(V)=V(f) V(-f)           reduced using f^2=D.

The required polynomial is

    P12=Norm_f(Norm_tau(E0)).                                (2)

This is an explicit finite polynomial recipe over the integers; it has
no unbounded product, no existential coefficient choices, and no
division. The supplied Python generator emits every binary arithmetic
gate. A norm of `u0+u1 tau` is exactly `u0^2-A u1^2`, and the final norm
of `v0+v1 f` is exactly `v0^2-D v1^2`.

Over the algebraic closure, the polynomial has the exact factorization

    P12=d^8 H^16 product_over_16_tuples
                  (t-gamma-tau-wy y-wf f).                  (3)

To check the scale, first multiply the two gamma factors; the result is
`((zeta0-qy y)^2-G)/H^2`. Multiplication over the two `y` signs and
clearing `d^2` gives `E0`. The two successive quadratic norms give
the remaining powers. In particular `P12` has degree sixteen in `t`
and leading coefficient `d^8 H^16`, which is nonzero in the domain of
the proof.

## 6. Root recovery and the twelve-variable equivalence

If an integer `t` satisfies `P12=0`, equation (3) gives an algebraic tuple
with `t` equal to (1). Every automorphism of the algebraic closure fixing
the rationals maps this tuple to another of the sixteen tuples and
fixes its sum (1). The sums are pairwise distinct, so every such
automorphism fixes every coordinate. In characteristic zero this says
that `gamma,tau,y,f` are all rational.

Since `f^2=D` and `tau^2=A` are integers, `f` and `tau` are integers.
Set `V=vf-Z`, an integer. The recovered auxiliary equation is

    Q V^2-(Q-1)y^2=1.

As `Q=(Delta I)^2` is an integer square greater than one, Section 2 makes
`y` an integer. Finally
`gamma=t-tau-wy y-wf f` is an integer. This is the second essential
integrality step: no claim that the rational root of the nonmonic main
quadratic is automatically integral is needed.

We have restored exactly the four deleted roots, possibly with signs.
The inherited signed ordinary-core theorem accepts signed
`gamma,tau,y,f` and positive retained ports. Its ordinary strong
coordinate is `i_ordinary=Delta i`; the restored normalized strong
equation gives

    (i_ordinary c^2)^2=Delta(f^2-1)=Q.

Thus all six ordinary factors are restored, with the other two equations
being `Nk=Nt=1`, and the inherited theorem yields the blank halting
condition for K215. No sign assertion about a recovered root has been
smuggled into a positive-only theorem.

Conversely, a canonical positive normalized witness for blank halting
has all four original coordinates positive. Define `t` by (1), using the
displayed weights. It is positive, and all three new equations hold.
Therefore

    exists12 positive variables (Nk=1, Nt=1, P12=0)
       iff K215 halts blank.

The inherited K215 calibration gives, by ordinary reasoning formalizable
in ZFC,

    ZFC proves: no positive solution iff Con(ZFC).

## 7. Single-polynomial finalizers

The transparent sum-of-squares finalizer is

    (Nk-1)^2+(Nt-1)^2+P12^2=0.

It has degree 5184 and 170 binary operations.

There is a smaller-degree product finalizer:

    Nk Nt (1+P12)-1=0.                                      (4)

Indeed `E0` is a square modulo four in the quadratic algebra. Polynomial
norms are multiplicative over any commutative coefficient ring, including
integers modulo four: the identity

    (ac+delta bd)^2-delta(ad+bc)^2
       =(a^2-delta b^2)(c^2-delta d^2)

is valid over the integers and remains valid after reduction modulo four.
Thus `Norm(U^2)=Norm(U)^2` in either quadratic algebra. The two successive
norms therefore leave `P12` a
square modulo four. Hence `1+P12` is never minus one modulo four. At a
zero of (4), the three factors are integer units, so `P12=0` and
`Nk Nt=1`; the two outer factors may initially both be minus one.

The weak bootstrap used above permits both signs. Root recovery gives
the six-factor signed ordinary-core product with value one, whose
established signed theorem proves blank halting and subsequently forces
the correct outer signs. This avoids assuming those signs prematurely.
Completeness follows from the positive canonical witness. The degree of
(4) is 2601 and its emitted circuit has 167 operations.

## 8. Exact total degrees

All twelve supplied variables have degree one and the four fixed ports
degree zero. The common degrees are

    c:5, a:6, H:6, Delta:12, R:4, ell:11,
    A:22, I:11, D:34, Q:46, Z:38, e:122,
    C:38, r:17, C2:21, S:11, wy:95, wf:116.

Let a subscript `top` denote the nonzero top homogeneous form. Then

    D_top=a_top^2 I_top^2,
    Z_top=R_top D_top,
    C_top=Z_top,
    C2_top=R_top a_top I_top,
    wy_top=Q_top C_top ell_top,
    wf_top=2 wy_top C2_top.

In the initial norm, the two degree-324 terms in `K` do **not** cancel:
their leading coefficients have ratio four to one. Consequently

    K_top=3 Q_top H_top^2 wy_top^2 R_top^2 D_top^2.

The subtracted term `4d^2G zeta0^2` has degree only 392, below the degree
648 of `K^2`. The first norm therefore has degree 648, the tau norm
degree 1296, and the final f norm degree 2592. In particular

    (P12)_top = 3^8 Q_top^8 H_top^16
                       wy_top^16 R_top^16 D_top^16,

which is nonzero for every compatible tuple with `Bm1>0`. (The top
`R` form is `(Bm1 J)^3(Bm1 J-F)`, hence is not the zero polynomial.)
The product finalizer has degree `7+2+2592=2601`. The sum of squares
has degree 5184 because its highest residual square is unique.

The attached generator also verifies these degrees on a modular generic
line. That finite diagnostic supplements the uniform leading-form proof.

## 9. Artifacts and scope

Run `python3 build_primitive12.py --degree-check` (the delivered version
uses only the standard library, including for this optional diagnostic), then
`python3 verify_primitive12.py` (standard library only). The latter
independently checks fifty complete sixteen-root finite-field
factorizations, fifty encoded roots, one thousand modulo-four guards,
and a finite rational-Pell integrality sample. It does not search for
a K215 halting computation or a ZFC inconsistency.

The construction has twelve positive unknowns rather than the pinned
repository's thirteen. No claim of global minimality is made, and the
classical nine-variable existence results remain a different benchmark.

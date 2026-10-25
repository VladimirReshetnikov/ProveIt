# A primitive denominator and an absorbed positive padding coordinate

## 1. Result, domain and inherited boundary

The principal equation `quotient_absorbed.json` uses **ten strictly
positive integer unknowns**, 86 binary arithmetic operations and exact
total degree 466. Its four fixed coefficients are the whole original
compact44 tuple, with the bytes and hashes specified by
`coefficients/BINDING.json`. The finite recipe under `coefficients/recipe/`
reconstructs every byte. `MF` is the already shifted source coefficient;
it must not be shifted a second time or mixed with another tuple.

The 87-operation `quotient.json` is a control with a direct positive-zero
bijection to the pinned parent. Absorbing one positive integer term into
the padding coordinate saves the additional operation. That absorption
preserves existence of positive zeros; its soundness requires the new
sign argument below, rather than an unsupported positivity assertion
about an inverse coordinate change.

The parents are the scaled uncentered and sharp equations in
`inherited/gap_fusion/equations/`. Their complete ordinary proofs are in
`inherited/gap_fusion/PROOF.md`; coprime fusion and canonical reconstruction
are detailed in `inherited/COPRIME_PROOF.md`, and the saturated witnesses
are discussed in `inherited/SATURATION_REPORT.tex`. The retained source61
material under `inherited/source61/` supplies the stated rank, index and
auxiliary interfaces. The coefficient calibration is described in
`inherited/COEFFICIENT_PROOF.md` and the packet's pinned native sources.
The parent snapshot is ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`.

These are ordinary arithmetic proofs formalizable in ZFC, composed with
the identified inherited refutation calibration. No new complete Lean,
Rocq, or encoded object-language ZFC proof is claimed. Neither consistency
nor inconsistency of ZFC is assumed.

## 2. The complete four equations

Let the ten quantified inputs be

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

Let the four fixed ports be `beta,K0,MC,MF`, satisfying the pinned tuple's
box

    beta odd, beta >= 31, K0 > 0, 0 < MC < beta < MF < 2 beta.

Define integer polynomials

    q = beta J + 1,       g = q - 1,       X = w q,       Y = q^3 s,
    C = q - F - alpha,    B = (K0+w) C - F,
    mu = q^2+1,          A = mu Y(X+1)+1,
    Delta = A^2-1,       H = 4A-5,
    k = eta+zeta,        c = kY+eta,
    v = X mu^2 Y^2,      D = v(v+1)k^2+1,
    G = (q-1)(q-F)+alpha,
    R = G(q^2-1)+(MC+q MF)J,       e = k-R-1,
    E = i c^2,           Fs = 1+Delta D E^2,
    Q = Delta^2 D E^2,   delta = Q-1,
    b = c(T+alpha)-R,    V = Fs b-c,
    Dnum = Q V^2-1,      Kpos = X(3c-2X)+2,
    a = D Fs,            M = g mu^2 H.

Select the two polynomial abbreviations in this table:

| File | Padding term `sigma` | Center `Gamma` | Operations | Exact degree |
|---|---:|---:|---:|---:|
| `quotient_absorbed.json` | `0` | `0` | 86 | 466 |
| `quotient.json` | `s` | `0` | 87 | 466 |
| `quotient_absorbed_sharp.json` | `0` | `A D E` | 89 | 450 |
| `quotient_sharp.json` | `s` | `A D E` | 90 | 450 |

Set

    Z = g mu^2 [H(n+sigma+V+Gamma-bB)+Kpos]
        - H(mu^2 B+g e),

    N = (delta Z^2-M^2 Dnum-delta M^2 a)^2
        -4 delta M^4 a Dnum.

The corresponding equation is `N=0`. Every displayed symbol other than
the ten listed inputs denotes a polynomial abbreviation. There is no
variable exponent, rational function, or additional existential witness
in the equation. Each JSON file gives the entire binary arithmetic
schedule, including the shared intermediate registers and all four
coefficient ports.

The exact normalized carrier, used only in the proof, is

    Z/M = n+sigma+V+Gamma+Kpos/H-WB/g-e/mu^2,
    W = 1+g b.                                             (1)

Here `M>0` on the quantified domain. Divisions in (1) are explanatory
notation and do not occur in the actual polynomial.

## 3. Exact relation to the old polynomial

The old scaled parent has denominator `M_old=q^3 g mu^2 H` and normalized
carrier

    Z_old/M_old = n_old+V+Gamma+Kpos/H+Y/q^3-WB/g-e/mu^2.

For the unabsorbed chart use `Y=q^3s`, `n_old=n`. For the absorbed chart
use `Y=q^3s`, `n_old=n-s`. In either case direct expansion gives

    M_old=q^3M,       Z_old=q^3Z.

The finalizer is homogeneous of degree four in its two arguments `(Z,M)`.
Therefore the exact polynomial identities over the integers are

    N_old(Y=q^3s,n_old=n)   = q^12 N_quotient,
    N_old(Y=q^3s,n_old=n-s) = q^12 N_absorbed.              (2)

Both identities hold without positivity, a Pell assumption, or any source
interpretation. For the 87-operation chart the old theorem `q^3|Y` at
every positive zero makes (2) a positive-zero bijection, with inverse
`s=Y/q^3`. For the 86-operation chart, `n-s` can be nonpositive at an
arbitrary positive input. Consequently (2) alone is not its soundness
proof. Sections 4--6 supply that proof directly.

## 4. Root extraction and the early kernel facts

The old kernel is unchanged after defining the positive integer `Y=q^3s`.
The unconditional bounds include `q>=32`, `X>=q`, `A>4`, `c>=3`,
`E>=c^2`, `D>1`, `delta>c^2-1` and `Fs>c+2`. If `b=0`, then `V=-c`
and the auxiliary radicand lies strictly between `c^2` and `c^2+1`.
If `b` is nonzero, then `|V|>=Fs-c>1`. Hence both radicands
`a=D Fs` and `Dnum/delta` are positive before root extraction.

They are unequal: equality would give `delta D Fs=Q V^2-1`, which is
impossible modulo `D`, since `D|Q` and `D>1`. A zero of the norm gives
a nonzero rational signed sum of their roots. A nonzero rational signed
sum of two square roots with positive rational squares makes both roots
rational, by squaring and solving linearly for either root.

Thus `D Fs` is an integer square. Since `Fs=1 mod D`, coprimality gives

    D=tau^2,       Fs=f^2,       tau,f positive integers.

Put `I=tau E`; this is a proof-only integer, not a new unknown. Then

    f^2-Delta I^2=1,       Q=(Delta I)^2,       c^2 | I.

The parent's adjacent-Pell descent makes the remaining rational root a
positive integer `y`, and the signed carrier becomes

    Z/M=epsilon tau f+nu y,       epsilon,nu in {1,-1}.     (3)

The folding and first-Pell arguments in the parent now apply exactly as
stated. They use neither the sign of the padding coordinate nor its
normalized-carrier position. They recover an odd index `p>=3` with
`c=psi_A(p)` and

    c>kY>=k>=4(2v+1)>8X mu^2Y^2,
    R<c alpha/4,       b>c,       V>0,       Kpos>0.        (4)

For clarity, the strict auxiliary-index gap can be seen directly.
Because `p>=3` is odd,

    c>=psi_A(3)=4A^2-1=4Delta+3>4Delta.

Let `S=Delta I`, so `Q=S^2`. The auxiliary equation is
`(S V)^2-(S^2-1)y^2=1`; its positive Pell index is odd. Its first three
possible abscissa quotients are

    chi_S(1)/S=1,
    chi_S(3)/S=4Q-3,
    chi_S(5)/S=16Q^2-20Q+5.

But `b>c` gives `V>(Fs-1)c>4Q`. Hence the auxiliary index is at least
five, which gives `V>8Q^2`. Since `Fs<Q`, it follows that `b>8Q`.

The parent bounds consequently give, before transport or parity,

    tau f < H D E < b/2,
    0<y-V<b/4,
    e/mu^2<b/4.                                          (5)

The second inequality follows from the auxiliary norm and `Q-1>2Fs`.
For the last, `b-e=c(T+alpha)-k+1>0`; division by `mu^2>4` suffices
when `e>0`, and a nonpositive `e` is immediate. All uses of these facts
are on the same positive input domain as the parent.

## 5. The direct sign argument for absorbed padding

Solving (1)--(3) for the actual positive coordinate `n` gives

    n=(epsilon tau f-Gamma)+(nu y-V)-Kpos/H-sigma
      +WB/g+e/mu^2.

Both `Gamma` and `sigma` are nonnegative. Since `y>0`,
`nu y-V<=y-V`. Dropping the strictly negative `-Kpos/H` and using (5)
therefore yields

    n < b+WB/g.

If `B<=-1`, then `WB/g<=-W/g=-b-1/g`, contradicting `n>0`.
Thus `B>=0`. Its defining equation and `F>=1` imply `C>0`, after
which the original mask bounds give

    3q<R<q^4-2.                                          (6)

This argument uses positivity of the new `n`, with no requirement that
`n-s` be positive. It applies equally to the two unabsorbed controls.

## 6. Ordered source recovery with the smaller denominator

The unchanged normalized strong-rank and signed auxiliary-index lemmas
use the kernel facts `c^2|I`, `c>2R`, `c>2p`, `V=-c mod f`, and
`V=-R mod c`. They recover `p=R`. Oddness of `p` therefore gives the
same mask parity conclusion: `q` is even and `J` is odd.

Only now use coprimality. One has

    gcd(mu,g)=gcd(q^2+1,q-1)=gcd(2,q-1)=1,
    H=-1 mod mu,

so `gcd(mu^2,gH)=1`. Since the signed carrier is integral, its separated
fractions imply `mu^2|e`. The first norm gives `k=2n0 mod 4v`, with
`mu^2|4v`. Its comparison with the main base and (6) force
`n0=(R+1)/2`, exactly as in the parent. Write `R=2r+1`, with `r>=48`.
The unchanged zero-offset ratio lemma gives

    Y>X^r/3,       X^(r+1)<3Y(X+1)<H.                   (7)

After `mu^2|e`, the carrier implies `H|g Kpos`, a stronger conclusion
than the parent's `H|q^3g Kpos`. As `H` is odd, the same projector
identity gives

    H | g(X-2^R)(2^R X+1).

The parent whole-product upper bound with prefactor `q^3g` already lies
strictly below `H`. Removing the positive factor `q^3` cannot enlarge
the absolute value, so (7) forces `X=2^R`. No nonunit factor of `H` is
cancelled in this argument. The projector then gives `H|Kpos` itself.

Removing the now integral terms from the normalized carrier leaves
`WB/g` integral. Since `W=1 mod g`, this gives `g|B`. The other old
partial-fraction conclusion, `q^3|Y`, is built into `Y=q^3s` from the
start. The fixed-minus parity lemma gives `R=3 mod 4`, and the original
ratio/rounding argument identifies `Y` with the required half-binomial.

These are exactly the outer facts used in the parent's fresh unscaled
source reconstruction at `A_source=Y(X+1)+2`. That reconstruction does
not reuse the scaled strong ordinate or the padding coordinate. It
yields a finite syntactic refutation through the same pinned
source61/native/controller calibration. This proves soundness of all
four equations.

## 7. Completeness and the precise existence claim

Given a finite refutation, choose the parent's canonical positive tuple
for the matching center. It has `q^3|Y`. Put `s=Y/q^3>=1` and retain
all other coordinates except the padding coordinate.

For an unabsorbed chart take `n=n_old`. For an absorbed chart take
`n=n_old+s`. These are positive integers, and (2) gives a new zero.
Thus each new equation has a positive zero if and only if the parent
refutation calculus has a finite contradiction. Composing with its
inherited arithmetic calibration gives the ordinary theorem

    ZFC proves [no positive integer zero of N <-> Con(ZFC)].

For an absorbed chart no positive pointwise inverse from every arbitrary
new zero is asserted or needed. The reverse direction proceeds through
the source reconstruction of Section 6. The 87-operation and
90-operation controls retain the stronger direct positive-zero bijection.

## 8. Exact degrees and complete leading forms

All ten inputs have degree one; fixed coefficients have degree zero.
The new degree table is

| Register | Degree |
|---|---:|
| `q,X,mu,Y` | `1,2,2,4` |
| `A,Delta,H` | `8,16,8` |
| `k,c,v,D,E` | `1,5,14,30,11` |
| `Fs,Q,delta,b,V,M` | `68,84,84,6,74,13` |
| `a`, sharp `Gamma` | `98,49` |

In particular, `b` now has leading part `c0(T+alpha)`, of degree six.
It is not the old leading part `-R0`. Put `Z0=Z-M(V+Gamma)`; from the
displayed formula one has `deg Z0<=21` in every chart.

The exact centered identity is

    Theta = delta M^2(Gamma^2-a)-M^2(V^2-1)
            +2delta M(V+Gamma)Z0+delta Z0^2,

    N = 4delta^2M^4V^2(Gamma^2-a)
        +4delta M^2V Gamma Theta+Theta^2
        -4delta M^4aV^2+4delta M^4a.                     (8)

For `Gamma=0`, the first term has degree
`2*84+4*13+2*74+98=466`; `deg Theta<=208`. The remaining nonzero
terms have degrees at most 416, 382 and 234. For the sharp center,

    Gamma^2-a=D^2E^2-D,

of degree 82. The first term in (8) has degree 450, while
`deg Theta<=192` and the other terms have degrees at most
425, 384, 382 and 234. Thus the first term is uniquely highest in both
families.

Writing `q0=beta J` and `k0=eta+zeta`, the full leading homogeneous
components are

    uncentered:
      -2^10 q0^326 i^10 w^30 s^64 k0^34(T+alpha)^2,

    sharp:
       2^10 q0^314 i^10 w^28 s^62 k0^34(T+alpha)^2.       (9)

These products are nonzero for the actual fixed positive `beta`.
The exponent sums are respectively 466 and 450. This proves the exact
degrees for the actual coherent coefficient tuple. The two-ray finite
checks in the verifier corroborate these explicit leading forms; they
are not the proof of the global upper bound.

The arithmetic schedules all have the looser syntactic degree bound
516. Their metadata records both this bound and the proved exact degree.

## 9. Verification and comparison

`verify.py` is read-only unless an explicit `--output` receipt path is
supplied. It uses the Python standard library, and it performs no K215
execution or search for a contradiction. It checks:

- the four fixed coefficient hashes, bit lengths, whole-parent binding
  and port box;
- every reconstructed coefficient byte from the finite Wang/controller
  recipe and its pinned transition seed;
- topological validity, operation splits, all live rows and every input;
- deterministic builder replay;
- unchanged kernel/finalizer rows and exact free-polynomial identities
  for both carriers, denominators, finalizer and homogeneity;
- the universal centered identity and sharp-center defect;
- 192 signed/positive full-formula and parent-identity controls;
- eight degree/leading-form ray checks over two primes;
- rejection of three planted transcription errors.

The 86/466 principal equation improves the inspected 89/288 parent's
operation count by three, while increasing degree. It is a deliberate
operation/degree tradeoff. The 89/450 and 90/450 sharp companions are
dominated by existing positive equations on these two measures and are
included only as algebraic controls. Operation counts treat the fixed
coefficient numerals as leaves; they are not bit-complexity claims.

No global optimum, smallest unrestricted-integer variable count, or
literature-wide novelty of denominator removal is asserted.

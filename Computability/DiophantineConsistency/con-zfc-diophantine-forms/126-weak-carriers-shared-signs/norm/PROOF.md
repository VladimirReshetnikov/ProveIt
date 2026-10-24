# Eleven unrestricted integers with weak congruence carriers

This note treats the two cubic-scale equations. `MIXED_PROOF.md` gives the
full companion proof of the mixed-scale pair. All four are literal ordinary
integer polynomials, with the same six fully supplied fixed source34
coefficients and eleven independently quantified integer coordinates.

## Literal cubic-scale equation

Use the definitions in `MIXED_PROOF.md`, with precisely these replacements:

    Y=(2v+1)q^3,
    S=srH,
    zc=HT+K,
    Ac=(zc^2+3H^2)(zc^3-19H^3).

The carrier registers M and Dc are not additional inputs. All other front
arithmetic and guard definitions are unchanged, in particular

    D=3Budget-4, Dt=1+L(L+k), Dg=1+D Dt s^2, P=Dt Dg,
    I=rc^2, Df=1+Delta I^2, Q=Delta^2 I^2,
    V=Df(c-R+4IT)-c, Da=(Q-1)(QV^2-1).

For the centered equation set `Z=S(n+3QV)-Ac`; for the direct equation set
`Z=Sn-Ac`. Put `u=S^2 Df`, `b=9S^2 Da`, and `e=81S^2 P`. Both use

    F8=[(Z^2-u-b-e)^2-4(ub+ue+be)]^2-64ube Z^2=0.

The centered equation has exact degree464 and123 binary operations; its
direct companion has exact degree488 and120 operations. The mixed-scale
equations have degrees416 and456 at129 and126 operations respectively.
These counts include every live binary multiplication by a fixed integer,
every square, addition and subtraction. Abbreviations are not unknowns.

## Soundness and exceptional inputs

The original cubic scale gives `|Y|>=|q|^3`, so `Y!=0`. The authentic fixed
base gives `|q|>=16`, `|X|>=64`, `|a|>3`, `H!=0`, and `Delta>1`.
Also `Df,Dt>=1`. The homogenized quintic Ac is nonzero on every integer
assignment because `(x^2+3)(x^3-19)` has no rational root. At `S=0`, the
polynomial becomes `Ac^8!=0`. Thus every zero has `s,r!=0`.

If c=0, then I=Q=0 and Da=1. If c!=0, then `|I|>=c^2`,
`Df>|c|+1`, and the integer expression `V=Df*b0-c` forces `|V|>=1`.
Thus Da is positive in both cases. A negative Dg would contribute the
sole imaginary radical to a vanishing conjugate factor, so Dg is
nonnegative. Budget and D are divisible by4 because q,cone_A,cone_B are
even. Therefore Dg is1 modulo4 and is positive. Budget<=1 would imply
Budget<=0 and Dg<=-3, contradiction. Hence Budget>=4.

When c=0, the budget equals

    k^2[q^2(1-4Y^2)-Derr] <= 0.

This contradiction proves c!=0, hence I!=0 and Q>1. The same budget gives
the common nonzero sign of q,F,C,q-F-C and the centered strip
`|c/k-Y|<1/2`.

Modulo3, X=2 and therefore a=H=Delta=0. Hence Df=Da=1 modulo3.
The normalized root weights are1,3,9. In each nontrivial squareclass
not divisible by3, the participating coefficients have distinct minimum
3-adic orders0,1,at least2. A class divisible by3 can contain only the
last term. Independence of squareclasses excludes every irrational class.
Thus Df,Da,P are squares. Since gcd(Dt,Dg)=1, the positive product square
P splits into separate squares Dt and Dg. The rational auxiliary root
sqrt(Da)/(Q-1) is integral by the adjacent-coefficient Pell descent,
whose Q>1 hypothesis has already been proved. The integral vanishing
factor then gives `S|Ac`, in particular `H|K^5`.

Define `Kquad=X(X+2ac)-1`. The identity `K=HXc-2Kquad` gives
`H|Kquad^5`, since H is odd. Main-root folding and the centered source's
pre-projection rank argument use only the recovered norms, the centered
strip and common signs, `c^2|I`, and the exact residues
`V=-c (mod f)` and `V=-R (mod c)`. They give

    R=2t+1, t>=24, c=sign(c)*psi_(a+2)(R),
    |Y|>(|X|-3)^t/2-1.

For `x=|X|`, `sigma=sign(c)`, and
`Pi=(sigma X-2^R)(2^R sigma X+1)`, the exact source congruence is
`2^R Kquad=Pi (mod H)`. Thus H divides Pi^5. The rank bound gives
`|H|>x(x-3)^t`. The unchanged huge beta gives x>=2^64, so

    |Pi|^5<2^(20t+20)x^10<x^(t+1)/2^t<|H|.

The middle strict inequality follows from
`64(t-9)>(21t+20)` for all t>=24. Therefore Pi=0 and
`sigma X=2^R`. The retained centered orientation and half-binomial proof
recover X,c,k,Y>0 and0<eta/k<1/4. Fresh private odd strong and auxiliary
witnesses then restore the precise old signed native source zero.

Composing the explicitly retained ordinary native/compiler/refutation
calibration proves, in ordinary ZFC, that absence of integer zeros is
equivalent to syntactic Con(ZFC). This argument does not prove consistency,
and no new full Lean/Rocq or object-language ZFC certificate is asserted.

## Completeness and quantifier order

Start with the inherited canonical native witness. It gives the stated
outer coordinates, Dt=tau^2 and Budget>=64. Since Dt=1 modulo3,
`D Dt` is positive and2 modulo3, so it is nonsquare. Ordinary Pell
existence supplies positive s,g with `g^2-D Dt s^2=1`, exactly Dg=g^2.

Choose one positive strong pair I,f with `4s c^2|I`, and define r=I/c^2.
Every prime of `m=sr` divides I. The supported-modulus interpolation
theorem of the retained Round14 proof supplies every auxiliary residue
T modulo m while keeping this same strong pair fixed.

Canonical main projection gives H|K; write kappa=K/H. Choose a residue
a modulo m for which `pi(a+kappa)=0 (mod m)` using the classical
intersectivity of pi(x)=(x^2+3)(x^3-19). Then request T=a modulo m from
the fixed-pair interpolation theorem, obtaining an integral auxiliary y.
The quotient

    Ac/S=H^4*pi(T+kappa)/(sr)

is integral. For the direct equation set `n=Ac/S+f+3delta*y+9tau*g`;
for the centered equation subtract3QV. One conjugate factor vanishes.
The strong pair is fixed before the intersective residue is chosen.

## Exact degrees and the polynomial shear

The two versions in each chart differ by the polynomial coordinate
bijection `n_direct=n_centered+3QV`; Q,V do not involve n. This preserves
the entire integer zero set up to that explicit bijection, not just
canonical witnesses.

For the cubic chart, `deg S=8, deg Q=30, deg V=23, deg Ac=35`,
`deg u=34, deg b=122, deg e=110`. In the direct equation b is the unique
largest-degree term in the first squared bracket, giving highest form
b_top^4 and degree488.

For the centered equation let `C0=3SQV`, `z0=Sn-Ac`, and
`omega=Z^2-b`. The exact defect identity is

    b-C0^2=9S^2[-Q(V^2+1)+1].

Hence deg(omega)<=96. Rewriting the identical norm as

    [(omega-u-e)^2-4(ue+b(u+e))]^2-64ube Z^2

shows the inner bracket has unique top term -4b_top*e_top, of degree232.
The final correction has degree388. Thus the highest form is
16b_top^2 e_top^2 and the exact degree is464. Its actual nonzero coefficient

    [j^264 w^52 v^64 h^12 z^4 s^12 r^24 c^32] F8
       =2^456 * 3^330 * beta^264 > 0

is verified independently, along with the entire homogeneous leading form.
`MIXED_PROOF.md` gives the corresponding degree416 proof and coefficient.

## Executed finite verification

The independent standard-library checker authenticates the six complete
numeral payloads against fixed source hashes, verifies every named register
in a free polynomial ring, checks the complete35-term three-root norm and
the center-defect identity, recounts all live gates and variables, and checks
the entire leading forms and their actual nonzero coefficient. It includes
384 modular replays with authentic coefficient residues, 3,125 guard
divisibility controls, 540 CRT boundary controls, and six rejected circuit
corruptions for each variant. Normal and optimized Python runs both pass.
See `AUDIT_INDEPENDENT.json` and `AUDIT_INDEPENDENT_OPTIMIZED.json`.

These are finite artifact checks. They do not verify the entire unbounded
Pell, native compiler or refutation calibration. The proof uses the explicit
ordinary dependencies retained in the package; the distinction is essential.

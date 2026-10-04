# Fixed polynomial absorption of the strong Pell root has finite input projection

Fix a valid compiler-numeral slice of the actual complete84 polynomial. Let
E85 be all64 computed registers and all21 supplied values independent of the
four auxiliary witnesses i,f,T=`auxiliary_quotient`,y=`y_aux` in its literal
source graph. The supplied values are the fourteen other witnesses, positive
ordinary input x, and six fixed numeral ports. Their algebraic dependencies
are retained.

For a fixed integer polynomial G in these85 formal arguments, substitute
f=G(E85) in the complete source. Keep every other supplied witness, including
T, strictly positive. After combining like monomials, put t=deg G and
L=max(1,sum of absolute coefficients). Use t=0,L=1 for G identically zero.
Then every positive zero of the substituted polynomial satisfies

    G(E85)!=0,
    2d*x+b<R<c<4t+ceil(log2 L).

In particular the ordinary-input projection is finite on each fixed compiler
slice. This conclusion includes signed G and the zero-value sector. It is an
obstruction to this literal substitution class, not a generic implementation
of G, operation saving or global lower bound. The universal84 circuit is
unchanged.

## 1. The signed-quotient lemma supplies exactly the needed domain

Use the literal source notation

    A0=a+2, Delta=A0²−1, c=R10a, R=r_lhs,
    D=R14, S=Delta*i*c², V=c(Tf−1)−Rf².

The [signed-quotient theorem](complete84_signed_quotient_absorption.md)
considers this same complete polynomial with f,i,y and all the exterior
supplied coordinates positive, but with T any integer. Its proof recovers,
on every such zero, the main and strong indices p,m with

    p=R>=3, c=psi_R(A0), D=chi_R(A0),
    f=chi_m(A0), psi_m(A0)=i*c², R*c divides m,
    2d*x+b<R,
    |E_j|<c⁴ for all85 exterior values.

The normalized strong-rank argument giving R*c|m is essential. It is stronger
than merely knowing c|m: strong divisibility gives R|m; writing m=R*j,
psi_(R*j)/c is congruent to j*D^(j−1) modulo c. Since its actual value i*c
is divisible by c and gcd(D,c)=1, c divides j.

These are the direct signed-domain rank and size statements proved there.
This use does not assume a positive old auxiliary restoration, R=3 modulo4,
or the entire positive-parent compiler theorem on arbitrary signed-T tuples.
Those stronger statements are not needed for the finite-input conclusion.

## 2. The strong root grows faster than c^c

For integer A>=2 let chi_n(A),psi_n(A) be the usual Pell coordinates. The
positive Pell unit identity implies

    chi_(rs)(A)=chi_s(chi_r(A)).

Indeed, raising A+sqrt(A²−1) first to r gives the positive unit with first
coordinate chi_r(A), and raising it to s gives the same first coordinate as
raising the original unit to rs.

Since m>=R*c and the chi sequence is increasing,

    f=chi_m(A0)>=chi_(R*c)(A0)=chi_c(D).

The main norm gives D²−Delta*c²=1 with Delta>1, hence D>c. Also c>=2.
The positive binomial expansion of chi_c(D) contains D^c and the strictly
positive term binom(c,2)*D^(c−2)*(D²−1), so

    f>=chi_c(D)>D^c>c^c.                              (1)

All variable exponents in this argument are mathematical estimates, not
unpriced arithmetic gates in a proposed compiler. Inequality(1) holds for
every permitted strong completion, not just the least chosen one.

## 3. Restoring a signed substituted root without changing its arguments

In the actual84 source, the only direct consumers of the supplied f are

    L16=f*f,
    auxiliary_Tf=T*f.

There are no other consumers of T. Therefore simultaneous sign reversal
of f and T preserves both producers, every downstream value and the whole
polynomial:

    F84(...,f,T,...)=F84(...,−f,−T,...).              (2)

This is an exact all-ring identity on the unchanged source. Every argument
of G is independent of both f and T (and i,y) by its literal dependency
census.

At a substituted zero with g=G(E85) nonzero, set

    f'=|g|, T'=sign(g)*T.

Then f'>0, T' is an integer, and f'²=g², T'f'=Tg. Every other supplied
coordinate remains positive and unchanged, as does every member of E85.
Thus(2) gives a zero in the signed-quotient lemma's precise domain. The map
is used only for proof; it does not assert a positive inverse into the
original positive-T parent. If g is negative, the restored quotient is
negative, which is precisely why the signed-domain lemma is needed.

Applying that lemma and(1) gives

    |g|>c^c,                 |E_j|<c⁴.

No claim that the original substituted f itself is positive is made.

## 4. Effective finite cutoff

The formal polynomial G has fixed degree t and coefficient norm L. Even
though its arguments may be dependent, their individual bounds imply

    |G(E85)|<=L*c^(4t).

Write s=ceil(log2 L). If c>=4t+s, then c>=2 and

    c^(c−4t)>=c^s>=2^s>=L.

This contradicts the strict growth inequality |G(E85)|>c^c. Consequently

    c<4t+s, equivalently c<=4t+s−1.

Together with 2d*x+b<R<c this proves the stated finite ordinary-input bound.
For L=1, the logarithmic ceiling is0; the same strict endpoint argument
applies. Coefficients of G may depend on the fixed compiler slice but stay
fixed while input and witnesses vary. Variable-degree families, rational
substitutions, or arguments depending on the removed auxiliary coordinates
are outside this theorem.

## 5. The zero-value sector is impossible before index recovery

Let P5 denote the actual product of first, main, input, index and transport
factors. The full source is

    F84=P5*Na*Ns−Delta,
    Na=S²(V²−y²)+y², Ns=Delta*f²−S².

At f=0, V=−c, S²=Delta²*i²*c⁴, and Ns=−S². Hence the literal all-ring
identity is

    F84|f=0 = −Delta * (
      Delta*i²*c⁴*P5*(Delta²*i²*c⁴*(c²−y²)+y²)+1 ). (3)

On the retained supplied positive domain, a=Y(X+1)>0 gives the integer
Delta=a²+4a+3>=8 before any norm equation. The expression in parentheses
is1 modulo Delta and cannot be zero. Therefore no substituted zero can
have G(E85)=0, including a formally nonzero G that vanishes on its dependent
arguments. This argument uses no signed-T native theorem, Pell rank or
canonical completion.

The empty zero sector is distinct from the surviving zero-i sector in the
earlier exterior multiplier theorem. Here the entire input projection is
finite.

## 6. Exact source evidence and scope

The fresh helper authenticates nine predecessor files as inert bytes. It
checks that the signed-domain theorem binds the same84-row polynomial and
its normalized rank and exterior-bound statements. A new dependency pass
rederives all64 computed and21 supplied arguments of G, the only two f
consumers and the sole T consumer, and the actual positive-discriminant
boundary. Eight actual auxiliary-independent cuts expose all24 remaining
output ancestors. Exact integer polynomial expansion checks all17 terms of
the full output, simultaneous sign invariance, and the four-term zero-f
contraction(3), including disappearance of T.

Finite corroboration checks36 formal composition identities over Z[A] for
r,s=1..6, through degree36;120 strict growth cases D=2..9,n=2..16; and108
coefficient/degree cutoff cases at two integer endpoints each. These checks
corroborate the displayed quantified proofs. They are not full native zeros,
a generic implementation of G, or a substitute for those proofs.

The helper uses strict JSON, explicit checks retained under optimization,
type-sensitive exact receipt comparison, and exclusive output creation. It
neither imports nor executes any predecessor. Fresh normal and optimized
replays from working directory / passed. During staging, use:

```text
python3 /tmp/complete84_strong_root_absorption.py --root ABS_WIP --signed-root /tmp --expect /tmp/complete84_strong_root_absorption.json
python3 -O /tmp/complete84_strong_root_absorption.py --root ABS_WIP --signed-root /tmp --expect /tmp/complete84_strong_root_absorption.json
```

After installation, the signed predecessor defaults to `--root`; omit
`--signed-root` and use the installed file paths. Use `--output NEW_PATH`
instead of `--expect` only when authoring fresh evidence.

| Inert dependency | SHA-256 |
|---|---|
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| complete84_exterior_auxiliary_absorption.py | `46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9` |
| complete84_exterior_auxiliary_absorption.json | `ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b` |
| complete84_exterior_auxiliary_absorption.md | `69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de` |
| complete84_signed_quotient_absorption.py | `cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f` |
| complete84_signed_quotient_absorption.json | `c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00` |
| complete84_signed_quotient_absorption.md | `79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9` |

Helper SHA-256: `3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c`.

Receipt SHA-256: `424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a`.

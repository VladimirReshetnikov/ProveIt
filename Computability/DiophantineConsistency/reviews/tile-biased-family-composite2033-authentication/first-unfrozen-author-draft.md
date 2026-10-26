# A whole composite-modulus controller reduction at49/2033

This separate CODE-FREE hand note specializes only the finite controller
arithmetic of the frozen tile-biased family. It does not approve that
family, select a successful auxiliary prime or compute any new kernel
unit. ROOT supplied the2033 lead; `/root/alternate_encoding_research`+checked the following small identities by hand. Both are contributors,
not independent peers. The parent still needs its two full nonauthor
reviews. All parent files and the maintained decimal-page work are unchanged.

## 1. Exact conditional instance and the full fixed modulus

Use EXACTLY every fixed bit recipe, tile, coefficient, mask, padding,
native interface and positive P66 definition in
`../tile-biased-single-clause-family/README.md`, SHA256
73965f17f7cea0581b7f0be055e80c91f8c6dd7e823b06e64ee1d44b2a545db7.
In that family set the fixed parameters

    b=49, L=2033=19*107,
    rho=2^49, d=49L=99617=7²*19*107,
    B=rho^2033=2^99617, H_ctrl=1+B*K+B².

K here means the ENTIRE new tile-biased kernel of the parent: its
count-shift12 selector coefficients use the fixed p/s corrections, its
sole clause is1006, and DC has bare18 but NO bare marker. No old K,
old finite residue or earlier successful controller is substituted.

The parent allows any fixed odd L>=2031; it never requires L prime.
Here the49 padding is eighteen full fields2012..2029 and LOW32 at2030,
strictly below2033. Last product2011, safe-dummy outputs1983/986/977,
the zero tail, every mask/subset, slack and actual-rank argument remain
those of that complete conditional family. Nothing is repacked or
transported from an old numerical word.

## 2. Elementary factor and order evidence

19 is prime by division by2 and3.107 is prime by division by2,3,5,7;
its square root is below11 and7*15=105.53 is prime by division by2,3,5,7.
The primes7,19,107 are distinct. Their product with the repeated factor7
therefore gives exactly the stated factorization of d.

Modulo49,2³=8=1+7 and

    2^21=(1+7)^7=1 mod49.

The nonconstant linear binomial term is49 and every higher term is
divisible by49. The proper-order tests are2^7=30 mod49 and2³=8 mod49,
both nonunit residues distinct from1. Thus ord_49(2)=21. Equivalently,
the order modulo7 is3, so the order modulo49 is a multiple of3; it
divides21 and is not3. Here 'nonunit residues' is not needed: these
residues are units because they are powers of2; only inequality to1
is used in the proper-order tests.

Modulo19,2^9=512=-1 and2^6=64=7. Squaring the first congruence gives
2^18=1. The two proper-order tests for primes2 and3 are not1, so
ord_19(2)=18.

Modulo107, repeated squaring gives

    2^8=42, 2^16=52, 2^32=29,
    29*52=10,
    2^53=29*52*16*2=320=-1.

Consequently2^106=1. The proper-order tests for primes2 and53 are
2^53=-1 and2²=4, neither1. Hence ord_107(2)=106=2*53.
These are complete small hand identities, not executable residue evidence.

## 3. Exact B orders and every fixed B²-1 unit

The complete exponent has the elementary reductions

    99617=21*4743+14=18*5534+5=106*939+83.

For an element of order m, its d-th power has order m/gcd(m,d).
The relevant gcds are7,1,1. Therefore

    ord_49(B)=3, ord_19(B)=18, ord_107(B)=106.

For clarity, direct small residues also give

    B=2^14=18 mod49,
    B=2^5=13 mod19,
    B=2^83=-2^30=73 mod107.

The last line follows from2^53=-1 and2^30=34: multiplying the already
listed residues52*42*16*4 gives34 modulo107. Thus B²-1 is respectively

    29 mod49, 16 mod19, 85 mod107.

In particular its residue modulo7 is1. It is a unit modulo the ENTIRE
d=7²*19*107, including49; checking only the squarefree product would
not by itself establish the needed B-power congruence in section4.

CRT on the relatively prime moduli49,19,107 gives the exact whole order

    ord_d(B)=lcm(3,18,106)=2*3²*53=954.

This is the order of B, not of2 modulo d. It follows that for EVERY
nonnegative integer kappa,

    B^kappa=1 modd  iff 954 divides kappa.           (1)

## 4. Exactly what remains unresolved

The parent's whole-d condition P_bias(49,2033) is equivalent to the
following conjunction for some auxiliary prime lambda:

    H_ctrl!=0 modulo each of7,19,107;
    lambda>99617 is prime and lambda=1 mod954;
    B²!=1 modlambda and H_ctrl!=0 modlambda;
    v_lambda(B^(lambda-1)-1)=1.                    (2)

Indeed(1) is exactly the whole-d congruence, section3 removes the fixed
B²-1 obstruction, and the three nonzero H tests are equivalent to H
being a unit modulo7²*19*107. The lambda tests supply precisely the
remaining gcd condition. Since lambda>d is odd prime, Fermat gives
B^(lambda-1)=1 modlambda; its valuation-one requirement is an additional
condition and is not inferred from Fermat. No condition in(2) is dropped.

One may parameterize the remaining prime candidates by lambda=954k+1
with lambda>d, but this note selects NO k or lambda and makes no prime
or valuation-one existence claim. Every H residue, including the three
fixed ones, remains UNKNOWN. If a fixed H test fails, changing lambda
cannot repair it. No old certificate determines these new H values.

Under(2), the parent controller applies without any squarefree premise.
In particular B^(lambda-1)=1 modulo49 as well as19 and107. With
N=lambda^n and the independently cofinal dimensions from the parent,
q and the transport reduce to B modulo WHOLE d. Gamma is a unit modulo
the full dN, LTE supplies the lambda-power order, and CRT gives every
orbit1+d*lambda*z. The safe Boolean-subset proof and actual-rank tuning
therefore have their full stated modulus. A whole native/P66 conclusion
still requires both the reviewed parent theorem and actual evidence for(2).

## 5. Precise obstruction to53 with the same composite L

If instead b=53 and L=2033, then d=53*2033=107749. Since2033 is odd,
the same proven107-order identity gives

    B=2^(53*2033)=(2^53)^2033=-1 mod107.

But107 divides L and d. Thus107 divides B²-1 and the parent's necessary
gcd((B²-1)*H_ctrl,d*lambda)=1 fails for EVERY K and lambda. No auxiliary
prime or H value repairs this specific whole-d controller. This is a
scoped obstruction to P_bias(53,2033), not a counterexample or
impossibility theorem for the native encoding or Diophantine equation.
L2039 may remain a prospective53 choice; no primality, order, unit,
lift or successful-tuple assertion for it is made here.

The only new result is the complete small fixed-modulus reduction(1)
and the conditional characterization(2), together with the precise53
controller obstruction. No new constant array, numerical tuple, endpoint,
raw/text/page metric, Lean proof or global minimum is supplied. No code,
application, helper, import, AST, prime search, large-kernel evaluation,
TeX/PDF or rendering process was used. The finite conditions in(2) remain
to be checked after the family receives its separate ordinary reviews.

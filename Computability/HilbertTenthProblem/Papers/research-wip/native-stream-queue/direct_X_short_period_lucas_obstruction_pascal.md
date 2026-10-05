# Canonical half-binomial scales: an exact fixed-quotient prime obstruction

For a canonical direct-X index of the form `R=2h*p^e-2j+1`, with h and j
fixed, the odd primes dividing the half-binomial scale belong to an explicit
finite set independent of e. This excludes two natural high-central-carry
index families at every odd prime dividing the proposed short-period radix.
It does not exclude all indices or construct a full compiler zero.

The source context is Open question 1 of
`direct_X_canonical_resonance_repair_aristotle.md`, SHA256
`addf7b16329a70f002478895295e5979f1b0561f9b1962cfe3bafc9cd467f1e9`.
That note was read in full, inertly. Its source-coupled repair remains
`F=(K+W)(Z+W)`, together with its exact affine resonance and positive slack
criterion. None of those outer equations is replaced here. This note treats
the remaining necessary scale condition `q^3|Y_R`, where

```
r=(R-1)/2, X=2^R,
Y_R=(1/2)*sum(l=0..r) binom(2r,r+l)*X^l.          (1)
```

For odd R>=3 this is a positive integer: the central binomial coefficient
is even and every other summand is even. At odd primes its residue is
therefore one half of the displayed sum in the residue field.

The prior `complete83_gamma_small_prime_digit_rules.md`, SHA256
`b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e`,
already proves the general two-state Lucas recurrence in Section 2, including
persistence after a central carry. It was read inertly through line 240;
no saved certificates or helper were replayed. The contribution below is the
closed fixed-quotient collapse at canonical X, its exact finite exceptional
prime set, and the resulting restriction on the proposed short-period host.
It is not claimed to be a first digit recurrence or a general obstruction
to all higher-prefix choices.

## 1. Exact fixed-quotient theorem

Let p be any odd prime, e,h,j positive integers, P=p^e>2j, and

```
r=hP-j, R=2hP-2j+1 >=3,
xi=2^(2h-2j+1),
S_h(T)=sum(l=0..h-1) binom(2h-1,h+l)*T^l.        (2)
```

The rational number xi is a unit modulo every odd p, including when its
exponent is negative. Then the exact congruence is

```
2Y_R = xi^j*(1+xi)^(P-2j)*S_h(xi) (mod p).        (3)
```

Write `xi=a/b`, with a and b positive powers of 2 and at least one equal
to 1, and put the fixed positive integer

```
T_h(a,b)=sum(l=0..h-1) binom(2h-1,h+l)*a^l*b^(h-1-l),
N_(h,j)=(a+b)*T_h(a,b).                          (4)
```

The following criterion is exact, including the case xi=-1 modulo p:

```
p divides Y_R  if and only if  p divides N_(h,j). (5)
```

In particular, for fixed h,j the exceptional prime set is finite and
independent of e. The canonical congruence R=3 modulo 4 holds exactly when
h-j is odd; (3)--(5) themselves do not require that parity restriction.

### Proof

Freshman's dream and the ordinary binomial theorem give, in F_p[t],

```
(1+t)^(2r)=(1+t^P)^(2h-1)*(1+t)^(P-2j).         (6)
```

The low factor has degree P-2j<P, so these blocks do not overlap. Every
block with high index at most h-1 ends at most at
`(h-1)P+(P-2j)=hP-2j<r`. Every block with high index at least h begins
strictly above r. Thus the upper-half sum in (1) consists of precisely
the complete blocks with high index h through 2h-1. Substituting X gives

```
2Y_R=X^j*(1+X)^(P-2j)*S_h(X^P) (mod p).         (7)
```

Here `X^P=X` and `X=2^R=2^(2h-2j+1)=xi` modulo p, because
P=1 modulo p-1. This proves (3).

If xi=-1, the exponent P-2j is strictly positive, and both sides of (5)
vanish: p divides a+b. If xi!=-1, Frobenius gives

```
2Y_R=xi^j*(1+xi)^(1-2j)*S_h(xi) (mod p).         (8)
```

All displayed factors outside S_h are units, and
`S_h(a/b)=b^(-(h-1))*T_h(a,b)`. This proves (5) in the remaining case.
No division by 1+xi was made on its zero locus.

## 2. Two canonical denominator-resonant families

For (h,j)=(1,2), xi=1/2, S_1=1 and N_(1,2)=3. Therefore, for
P=p^e>4 and every odd p!=3,

```
R=2P-3,          Y_R=1/27 (mod p).                (9)
```

For (h,j)=(2,1), xi=8, S_2=3+T and N_(2,1)=9*11=99. Therefore,
for P=p^e>2 and every odd p!=3,

```
R=4P-1,          Y_R=44/9 (mod p).                (10)
```

Both index families satisfy R=3 modulo 4. Formula (9) is a p-unit for
every p!=3; formula (10) is a p-unit unless p is 3 or 11.
The theorem asserts only divisibility by p at the exceptional primes,
not the higher divisibility needed by q^3.

These are genuine high-central-carry examples. For p>=5, in either family

```
v_p(binom(R-1,(R-1)/2))=e.                       (11)
```

For (9), r=P-2 has low base-p digit p-2 and the remaining e-1 digits
p-1; doubling creates exactly e carries. For (10), r=2P-1 has e low
digits p-1 followed by the digit 1. The e low positions carry, and the
next digit becomes 1+1+1=3<p, so there is no additional carry. Equivalently,
Legendre's factorial valuation gives (11).

**Review remark 1 (central carries do not transfer to the canonical sum).**
The proposed shortcut “at least 3a central-binomial carries at p imply
p^(3a)|Y_R” is false when canonical X=2^R is a p-unit. Choose p>=5,
e>=3a, and R=2p^e-3. Equation (11) supplies the proposed central depth,
while (9) proves p does not even divide Y_R. For example p=5,e=3,a=1
has R=247 and central valuation 3, but Y_R=3 modulo 5. The second family
has the same failure away from 11. This is an exact scalar obstruction;
it does not assert authentic outer/slack data for these index choices.

## 3. Consequence for the proposed short-period q

Fix the authentic compiler exponent d, a power of 5 with d>=5, and set

```
B=2^d, Q=B^n, k=B-1,
m=1+Q+...+Q^(k-1), q=m+1, n>=1.                 (12)
```

Then m is divisible by B-1 and divides `2^(dn*k)-1`, as in the pinned
proposal. Also q=2 modulo Q, q>2, so q is even nondyadic with v2(q)=1.
The useful additional fact is

```
gcd(q,33)=1.                                     (13)
```

Indeed d is odd, so B=-1 modulo 3. Also `d=5 (mod 10)` and `2^5=-1
(mod 11)`, so B=-1 modulo 11. For either prime, if n is odd then Q=-1
and the odd number k of alternating terms sums to 1; hence q=2. If n
is even then Q=1 and q=1+k=B=-1. These are nonzero residues. At the
prime 3 the two residues coincide, which causes no exception.

Consequently, for any odd prime p dividing a q in (12), neither
`R=2p^e-3` nor `R=4p^e-1` can satisfy even p|Y_R, hence neither can
satisfy q^3|Y_R. This holds at every size and for every e in the stated
ranges, irrespective of whether the other outer conditions would have
been solvable. It rules out these prescribed denominator-resonant choices
as a scale completion of this actual fixed-B host.

More generally, for any fixed h,j, a prime divisor p of q outside the
explicit finite set of prime divisors of N_(h,j) excludes every index
`R=2h*p^e-2j+1` with p^e>2j. This conclusion does not require factoring
q or computing its enormous Pell witnesses inside a paid circuit.

## 4. What remains open and evidence limits

**Open question 1.** Can the repaired affine outer index and its short
period be arranged so that q^3 divides the full canonical Y_R? The
quotient h=(R+2j-1)/(2p^e) need not remain bounded as q and R vary.
Then N_(h,j) changes, and the finite-prime conclusion for fixed h,j
is not a uniform obstruction. Even divisibility by p at every p|q does
not supply the required prime-power depths. No source-coupled completion,
full positive zero, or universal83 conclusion is established here.

The fresh companion checker computes scalar residues directly from an
integer binomial recurrence and modular powers of 2, and compares them
with (3) and (5). Separate small controls check (11) by factorial valuations
and (13) by a modular geometric recurrence, without forming the huge q.
They corroborate, rather than replace, the proofs. Their parameter values
are scalar controls and are not presented as compiled programs or full
source zeros. Exact case totals and hashes are in the companion receipt.

The source context read beyond the pinned repair note is the literal
powers-of-five/mask setup in lines 1--120 of
`complete75_half_binomial_compiler.md` and the prior digit-rule note through
line 240, including its complete Section 2. Both were read inertly. No predecessor,
supplied, archived or frozen helper is executed or imported; no saved
source array is evaluated or propagated, and no compiler or build runs.
All new files are under /tmp. There is no new operation or witness ledger.

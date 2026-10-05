# Direct-X83: parity, square exclusion and isolation of a wrapped first index

This is a continuation of `complete83_direct_X_boundary_pascal.md`, not a
new source or a proof of universal83. Every full positive child zero has
R=3 modulo4. On an authentic compiler slice q is even and the direct
coordinate X cannot be a square. In the remaining wrapped sector, fixing
(q,X,s,v,epsilon) confines R to an explicit open interval of width less
than one. A fresh exact rational-interval computation excludes wraps for
even 16<=q<=64. It does not exclude wraps for all q or recover q|X.

The ordinary input remains the parent's positive x. The symbol X below
is the newly supplied positive native coordinate, not that ordinary input.
No saved source array or predecessor helper is executed or imported.

## 1. Inherited hypotheses and the parity of R

At every full positive child zero the pinned boundary proof establishes

    Y=s*q^3, E=X*Y, A=Y*(X+1)+2, Delta=A^2-1,
    H=4Y*(X+1)+3, P=2XY^2+1,
    c=psi_A(R), k=2psi_P(n), Y<c/k<Y+1,
    R<2n<2R, 2n=R+epsilon+vE, 0<=vE<R,          (1)

with epsilon in {−1,1}. For authentic fixed-program numerals it also gives

    q>=16, (2q−1)(q^2−1)<R<q^4−q^3.             (2)

The normalized strong and positive auxiliary equations supply

    f=chi_A(m), c|m, m>=Rc>2R,
    c>2R, f>2c,
    V=Q_j(S^2), ell=2j+1,
    S^2=Delta*(f^2−1), c|S,
    V=−R mod c, V=−c mod f,
    chi_A(2ell)=chi_A(2R) mod f.                 (3)

All these statements precede recovery of q|X or exclusion of v>0.

**Proposition 1.** R is odd for every positive child zero.

The psi recurrence modulo2 is psi_A(t+2)=psi_A(t), so
psi_A(t)=t modulo2 for every integer A. If R were even, c and then m
would be even. The already used signed step-down gives ell=±R modulo m,
contradicting the oddness of ell. This proof needs no parity assumption
on A or q.

**Proposition 2.** In fact R=3 modulo4 at every positive child zero.

Use the stronger, plus-sign chi step-down stated in
`HALF_PARAMETER_PELL_92_PROOF.md`, lines154–158: its modulus is4m.
The last congruence in (3) is a plus congruence, with 0<2R<m, so

    ell=eR+2mt, e in {−1,1}, t an integer.        (4)

In the quadratic integer ring modulo f, the fundamental unit to power
2m equals −1: chi_A(2m)=2f^2−1 and psi_A(2m)=2f*psi_A(m).
Thus

    psi_A(ell)=e*(-1)^t*c mod f.                 (5)

The polynomial identities Q_j(0)=(-1)^j*(2j+1) and
Q_j(1−A^2)=(-1)^j*psi_A(2j+1), applied modulo c and f respectively,
now give

    e*(-1)^j=−1, e*(-1)^(j+t)=−1.               (6)

Here (3)'s strict c>2R and f>2c turn congruences of signed R and c into
actual sign equalities. Hence t is even. Equation (4) yields
ell=eR modulo4. If e=1, (6) makes j odd and R=ell=3 modulo4.
If e=−1, j is even and −R=ell=1 modulo4. Both cases give the claim.
There is no division by two inside a residue ring in this argument:
(4) is obtained by dividing an equality of integers by two.

## 2. Authentic outer parity and a square obstruction

Root independently pointed out the following consequence of Proposition1.
The unchanged literal source has

    q=(B−1)J+1,
    R=(q*(q−F)−Z)*(q^2−1)+(MC+q*MF_source)*J.   (7)

The authentic recipe has B even, MC even and MF_source odd. If q were
odd, J and q^2−1 would be even, making R even. Consequently q is even,
J is odd, and (7) modulo2 then gives Z odd. In particular Y is divisible
by8, A=2 modulo8 and H=3 modulo32. These conclusions use the actual
recipe; arbitrary supplied numeral ports do not inherit them.

**Proposition 3.** X is not a square on any authentic positive child zero.

The retained main projection gives X=2^R modulo H. Therefore gcd(X,H)=1.
Since H=3 modulo8, the Jacobi symbol (2/H) is −1. By Proposition1,

    (X/H)=(2/H)^R=−1.                            (8)

A square coprime to the positive odd H has Jacobi symbol +1, a
contradiction. This excludes X=1 as well. More generally, if X=2^a*z^2,
then a must be odd. These are necessary conditions, not a classification
of the remaining nonsquares. Even without authentic q parity, odd-square
X is excluded because odd X already makes H=3 modulo8.

## 3. A rigorous interval for every possible wrap

Suppose v>=1 in (1). The inherited bounds give

    1<=X<q, 1<=s<q/X, 1<=v<q/(Xs).               (9)

Put

    L=log(2A^2/P), E0=q^4*(1/A^2+1/P^2),
    d=epsilon+vXY−2,
    L_R=[2log(4AY)+d*log(2P)−2E0]/L,
    U_R=[2log(4A(Y+1))+d*log(2P)+2E0]/L.        (10)

The logarithms are natural. All arguments are positive; d>0 and
A^2−2P=Y^2*(X−1)^2+4Y*(X+1)+2>0, so L>log4.

**Proposition 4.** Every wrapped full positive child zero satisfies

    L_R<R<U_R,
    U_R−L_R < (2/q^3+1/q^2+1/q^8)/log4 < 1.     (11)

Thus there is at most one integer R for each tuple in (9), with each
choice of epsilon. The theorem does not assert that such an integer
exists, satisfies the main congruence, or extends to a full zero.

Here is an elementary logarithmic estimate sufficient to prove it.
For an integer C>=2 set alpha=C+sqrt(C^2−1). The exact formula

    psi_C(t)=alpha^(t−1)*(1−alpha^(−2t))/(1−alpha^(−2))

gives

    |log psi_C(t)−(t−1)log(2C)|<t/C^2, t>=1.    (12)

Indeed 0<log(2C)−log(alpha)<1/C^2: use
alpha/(2C)>1−1/(2C^2) and −log(1−u)<=u/(1−u).
The remaining logarithm in the exact formula lies in
[0,−log(1−alpha^(−2))) and is less than1/C^2, since
alpha>2C−1 and ((2C−1)^2−1)>C^2. Combining the negative first error
and the nonnegative second error proves (12), including t=1 directly.

Apply (12) to c and k/2. With

    T=(R−1)log(2A)−(n−1)log(2P),

we have |log(c/(k/2))−T|<R/A^2+n/P^2<E0, since R,n<q^4.
The positive ratio slacks say 2Y<c/(k/2)<2(Y+1). Substitute
2n=R+epsilon+vXY and multiply by two to obtain (10)–(11)'s interval.
Its width is

    [2log(1+1/Y)+4E0]/L.

Finally A>=2Y, P>2Y^2 and Y>=q^3 give the first bound in (11).
For q>=16 its numerator is less than1, while log4>1, proving the
second inequality. The errors are uniform in the allowed wrapped X,s,v;
there is no hidden assumption X>=q, X=2^R or Y exponentially large.

## 4. Bounded fresh corroboration and the remaining question

The new scalar helper checks all20,160 tuples given by even q from16
through64, (9), and epsilon in {−1,1}. It encloses each logarithm using
integer arithmetic with scale10^60: reduce an integer N to
N=2^e*t with 1<=t<2, and use log(t)=2*atanh((t−1)/(t+1)).
Every series ratio is at most1/3. Seventy outward-rounded terms and the
strict tail bound3^(−140) give explicit rational enclosures. Directed
integer division then encloses (10). No floating-point logarithm is used.

Only three enlarged rational intervals contain an integer R:

| q | X | s | v | epsilon | R | strict outer upper bound |
|---:|---:|---:|---:|---:|---:|---:|
|26|2|1|4|−1|2021770|439400|
|40|1|1|25|−1|27144627|2496000|
|54|1|1|8|1|23008023|8345592|

All three violate (2), so none is a full-positive-zero candidate. The
interval theorem itself assumes R<q^4; listing those integers is only
a record of the necessary-condition sieve, not a claim that their actual
Pell ratios satisfy the estimated error at those out-of-range R values.
No tuple reaches the optional main-projection test. The helper also
corroborates (12) on512 independently generated scalar Pell values,
2<=C<=17 and1<=t<=32. It constructs these by the elementary recurrence,
not by any source array or predecessor implementation.

This finite check concerns an arithmetic pretyping superset. It supplies
no authentic compiler instance, native auxiliary witnesses or accepted
ordinary input, and makes no claim that a compiler's actual B lies in
the tested range. The all-size conclusions are Propositions1–4; the
finite exclusion is expressly limited to the recorded q range.

**Open question 1.** Exclude the at-most-one integer from (10), or
construct a genuine full positive child zero, for unbounded q with
authentic constants. The congruence X=2^R modulo H and the input/transport
equations remain additional tests; the interval alone does not solve
them. The distinct no-wrap obligation q|X is unchanged. No new operation
count, witness reduction, universal83 theorem or termination assertion
is claimed here.

## 5. Frozen dependencies and evidence

The boundary MD and JSON are pinned respectively at
`c0debb531d18f9a480d419f82e3503dd5be0c8ffdc4183ab0e56fba8bc74b467`
and `1d779079afa3a6ac79f281b6b09c166f8397191966074eb043ea3b2b6c232241`.
The actual complete84 JSON is
`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
Its outer rows were read as definitions only; no source array was evaluated.
The half-parameter proof, whose lines118–186 were read here, is
`c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b`.
The authentic modified-mask definitions and parity, read at lines26–59
of `complete75_half_binomial_compiler.md`, are pinned at
`68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.
The boundary proof was read in full; the older half-binomial42 proof was
read at lines1–240, ending within Section6, without running its helper.

Fresh evidence is `/tmp/direct_X_wrap_isolation_checks_pascal.py`, SHA256
`f14a95b26cd42934d5b9491be73fcb2b6cbefc5581df7636ec5f9e595e5eda96`,
and its JSON SHA256
`6f4846bd7d1bd7e74e1665ecb918b1d4a4c10f0df91824e83dd50a659dc116d0`.
Normal and optimized Python runs produced byte-identical receipts before
freeze. Root independently challenged the auxiliary two-sign argument;
no peer review of the new logarithmic interval is implied by that fact.
Only this newly written scalar helper and fresh read-only metadata were
executed. Repository files and frozen predecessors were not changed.

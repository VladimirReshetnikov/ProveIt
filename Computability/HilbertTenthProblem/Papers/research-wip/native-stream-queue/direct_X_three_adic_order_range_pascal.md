# Exact order certificates exclude the three-adic family through d=5^16

The canonical ansatz

    B=2^d, q=B*3^k, R=2*3^e-3, k,e>=1

has no authentic direct-X83 positive zero when `d=5^n` and
**2<=n<=16**. The proof combines the previously established all-offset
size bound with two small, exact modular-order certificates. It never
materializes B for the large endpoint d, or any canonical X,Y or native
witnesses.

This is a bounded range of compiler exponents, not a theorem for all
powers of5. It also does not address other canonical q/R families or
general direct-X83 soundness. Root requested the order-versus-size
route; the certificates and the finite range below were derived and
checked here using fresh scalar arithmetic.

## 1. The exact order-versus-size criterion

Assume the repunit, divisor and numerical-window premises of the
committed varying-offset theorem:

    q=(B-1)J+1, J>0, J divides R,
    (2q-1)*(q^2-1)<R<q^3*(q-1).                    (1)

The literal packed-index equation supplies J dividing R on authentic
source zeros. The theorem gives

    3^k<=3B^3(B-1)<3*2^(4d).                       (2)

Since `2^11=2048<2187=3^7`, raising (2)'s strict inequality to the
eleventh power yields

    3^(11k)<3^11*2^(44d)<3^(11+28d),
    11k<11+28d.                                    (3)

Now let M>=2 be a modulus coprime to3 with `2^h=1 modulo M`.
If h divides d, then M divides B-1. The repunit in (1), together with
B=1 modulo B-1, implies `3^k=1 modulo B-1`, hence also modulo M.
Therefore the exact unit order `ord_M(3)` divides k. With several such
moduli, their orders' least common multiple O divides k.

Consequently the exact sufficient obstruction is

    11*O >= 11+28d.                                (4)

Indeed k>=O would contradict (3). Neither M nor B-1 is assumed prime.
The modulus-divisibility and order certificates must actually be proved;
a list of unverified large factors would not establish (4).

## 2. Two complete finite order certificates

Use the following moduli and exponents:

| M | h with 2^h=1 mod M | Exact order O_M of3 |
| --- | ---: | ---: |
| 33554431=2^25-1 | 25 | 450 |
| 269089806001 | 125 | 44848301000 |

Both residues `2^h mod M` are1, as are `3^(O_M) mod M`. The complete
factorizations of the proposed orders are

    450=2*3^2*5^2,
    44848301000=2^3*5^3*41*107*10223.

The prime factors in these expressions are verified by finite trial
division; the largest requires only testing divisors2 through101.
The residues at the order divided by each distinct prime factor are:

| M | prime ell | 3^(O_M/ell) mod M |
| --- | ---: | ---: |
| 33554431 | 2 | 14069411 |
| 33554431 | 3 | 6967995 |
| 33554431 | 5 | 5738380 |
| 269089806001 | 2 | 269089806000 |
| 269089806001 | 5 | 164136984823 |
| 269089806001 | 41 | 47900848917 |
| 269089806001 | 107 | 38645547593 |
| 269089806001 | 10223 | 207448671296 |

All are different from1. Since the order divides O_M, any proper order
would divide O_M/ell for some prime ell dividing O_M, contradicting its
listed test. Thus these are exact orders. In particular the argument
does not need or claim primality of the two moduli. The second modulus
is used only through the explicitly verified power residues, not through
a supplied factorization program or external primality assertion.

## 3. The covered exponent range

For every d divisible by25, the first certificate makes450 divide k.
At d=25, criterion (4) holds since `11*450=4950>711=11+28*25`.
This already excludes the minimal inherited power-of-five exponent.
It strengthens the earlier necessary divisor150 of k to450.

For every d divisible by125, both certificates apply and give

    O=lcm(450,44848301000)=403634709000.             (5)

The missing factor when the second order is used alone is9. Thus
(4) excludes every such d with

    d<=floor((11*403634709000-11)/28)
      =158570778535.                               (6)

In particular

    5^16=152587890625,
    11*O=4439981799000,
    11+28*5^16=4272460937511,

with strictly positive difference167520861489. For each3<=n<=16,
`d=5^n` is divisible by125 and no larger than5^16. The same obstruction
therefore applies throughout that range. Together with the d=25 case,
this proves the headline2<=n<=16 statement.

The actual modified75/direct-X recipe requires d to be a power of5
and25 to divide d, so its possible exponents start at n=2. The result
does not assert that any particular compiler has d within (6); it
gives an exact conditional exclusion whenever its fixed d does.

## 4. Explicit limit of the fixed-certificate argument

**Review remark 1 (the finite certificates do not prove all n).**
At `d=5^17=762939453125`, the two fixed certificates merely require
k to be a positive multiple of O from (5). Their smallest allowed
value k=O is not excluded by even the sharper size bound (2):

    2*O=807269418000 < 3*5^17=2288818359375,
    3^O<2^(2O)<2^(3d)<3B^3(B-1).

It passes these two order requirements and that numerical size test.
This is an exact counterexample to treating these partial tests as an
all-n exclusion argument. It is not asserted to satisfy the full
repunit modulo B-1, to admit any suitable e or packed index, or to be
a compiler zero. No huge value in the display is materialized: the
exponential comparison follows from3<4 and the displayed small
integer exponent comparison.

**Review remark 2 (corrected diagnostic count).** A pre-freeze summary
called the distinct order primes "seven". Their exact set is
`{2,3,5,41,107,10223}`, which has six members. There are eight
proper-divisor power tests because2 and5 occur in both order
factorizations. The helper's set-based count was already six; only
the prose summary needed correction. No certificate or range changed.

**Open question 1 (root's all-d route).** Can further exact moduli or
an all-size order lower bound force ord_(2^(5^n)-1)(3) above the
necessary exponent bound for every n>=17? No such general theorem
is proved here. A sequence of successful finite tests alone would not
justify it. The varying-offset finite candidate theorem remains
available separately for each fixed compiler.

The present exclusion does not use the half-binomial valuations beyond
the family context: it already follows from (1). It cannot be exported
to unrelated q or R formulas, arbitrary inputs, or the wrapped/direct-X
problem without its displayed hypotheses. In particular the separate
universal84 result is unchanged.

## 5. Fresh evidence and dependencies

The new scalar helper verifies exactly the two modulus power tests,
their order powers and all eight proper-prime-divisor residues; it
checks the small order factorizations, their prime factors, the lcm,
and the finite endpoint inequalities. It also binds this note and the
read dependencies. No supplied, archived, predecessor or frozen helper
is run or imported; no source array is evaluated or propagated. No
repository or Git mutation occurs.

The main bound is inherited from the full committed
`direct_X_varying_three_adic_offset_bound_pascal.md`, SHA256
`926f648494c4bac101901f4dd1552402f94a44c39efb80ee4df3c30466254394`.
The recipe and the earlier order context are read from the full
`direct_X_canonical_three_adic_family_pascal.md`, SHA256
`c18f09aa7fd0b4eb89bbdbbca2a5b5ad3aed3f5d559e6afb02034cb9bb62f7cc`,
and `complete75_half_binomial_compiler.md`, lines1--70, SHA256
`68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.
The literal outer equations are bound by
`direct_X_authentic_outer_root.md`, lines1--49, SHA256
`35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617`.
These are inert proof reads, not new executions or complete re-audits
of ancestral native or universal compiler theorems.

The fresh controls contain two modulus certificates, eight proper-order
tests and complete bounded trial-division records for six distinct
order primes. Normal and optimized (`-O`) executions before freezing
produce byte-identical receipts. The helper SHA256 is
`6b221fbdbd42275034e74fa68cbbfa2ea11f5169aac735628a93b54e8ed9781e`.
The receipt binds this note and its exact dependency spans; its own
hash is supplied separately to avoid a circular note/receipt hash.

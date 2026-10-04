# Independent review of the native prime-index reductions

**PASS, with no requested author change.** I read the complete frozen
[proof](complete83_gamma_native_prime_scaling.md),
[helper](complete83_gamma_native_prime_scaling.py) and
[receipt](complete83_gamma_native_prime_scaling.json), and checked the
canonical compiler congruence against its actual pinned proof. The
identities hold for every odd prime p and positive odd K, including
p dividing K and the exceptional residue 2^K=−1 modulo p.

| Frozen author file | SHA256 |
|---|---|
| complete83_gamma_native_prime_scaling.py | `31f232e01ce4c4cbaca1c2ffcea91938676339691924c592338e6dd439b95c91` |
| complete83_gamma_native_prime_scaling.json | `f2b018c05e6a837270d03491acbb232c1307e2cb5c2e08fb69ccd2fed8739a6d` |
| complete83_gamma_native_prime_scaling.md | `25a5ea05edca5a94527eeda9c7744e50a045f22deff9616774074c136eefa69a` |

## The arbitrary-prime split

For k=(K−1)/2, h=(p−1)/2 and x=2^K modulo p, the upper tail at pK
has threshold pk+h and top binomial argument p(K−1)+(p−1). Comparing
coefficients in the characteristic-p polynomial identity

    (1+z)^[p(K−1)+(p−1)]
       =(1+z^p)^(K−1) (1+z)^(p−1)

gives the claimed low-digit coefficients, with no condition on whether
p divides K. The central coefficient is lambda*C_K. If x is not −1,
the complete low-digit sum is one, and the partial sum from h through
p−1 is (lambda*sigma+x)/(1+x). Thus only the central high-digit block
differs from the smaller-index upper tail. Its correction is exactly

    C_K*x^k*(lambda*sigma−1)/(1+x).

The changed threshold contributes x^(pk+h)=x^k*sigma. Substitution into
the defining half-binomial expression proves

    C_(pK)=lambda*C_K,
    2a_(pK)−C_(pK)=sigma*(2a_K−C_K)             modulo p.

When x=−1, neither proof nor helper divides by 1+x. The defining factors
X+1 make both a values zero, while Euler's criterion gives
sigma=x^h=(−1)^h=lambda. This verifies the same identity directly,
including p=3. All other divisions are by nonzero x or by 2.

For the zero-low-digit identity, the top argument is p(K−1), the threshold
is pk, and only positions divisible by p survive. Both the central
coefficient and the whole upper tail reduce to the index-K quantities.
This argument also works when x=−1. Iteration is legitimate because
every intermediate index remains a positive odd integer. Squared sign
characters equal one, giving the unrestricted paired-prime-factor
removal. The R=1 endpoint is consistently interpreted in Z[1/2] and
modulo odd primes; it is not asserted to be an integer native kernel zero.

## The canonical compiler specialization

Section 6 of the pinned half-binomial compiler actually provides
R=dh modulo dN, with d,h,Htime,N pure powers of five and
N=h*Htime, Htime>=25. Together with 0<dh<dN and R>0 this gives

    R=5^(a+b)*(1+5^f*z),  z>=0,

and fixes v5(R)=a+b. The native theorem separately supplies R=3 modulo4.
Since every five-power is1 modulo4, z=2 modulo4 and z+1 is a positive
odd index. Applying the two general identities in this order gives
exactly the stated parity-dependent residue at z+1.

There is no illicit deletion of an arbitrary cofactor: pure five-power
height is a stated hypothesis. The old compiler's dummy adjustment is
used only to obtain its actual prescribed congruence, and the note does
not claim that the residual z can be freely chosen. I also checked the
quoted dummy-change formula: its factor q²−1 indeed locks the residue
under these particular fixed-q changes modulo every divisor of q²−1.
This does not exclude different compiler or padding strategies.

## Counterexamples and their precise limitation

The residues

    R=395:  a_R=274 mod625, Delta_R=550 mod625;
    R=4575: a_R=372 mod625, Delta_R=500 mod625

give exact valuations (v5(R),v5(Delta_R))=(1,2) and (2,3).
Both Delta residues are nonzero modulo 5^4, so the larger valuations
are determined exactly rather than being lower estimates. The two
cofactors are 79 and183, neither congruent to1 modulo25. Consequently
these refute the proposed unrestricted formula inequality, but do not
refute an inequality restricted to the canonical compiler congruence.

No full native witness, accepted history or false ordinary input is
asserted for either sample. The symbolic examples with indices
3*5^1000 and3*5^1001 are explicitly consequences of the proved recurrence;
neither the author nor this review evaluates their enormous tails.

Residue exclusion of a prime from Delta is correctly distinguished from
determining the order of2 modulo H. A prime divisor of H need not itself
divide the order gcd. The packet leaves full order compatibility,
positive input width and realization on a genuine canonical history
unresolved. It gives no gamma83 language conclusion or new complete
arithmetic bound.

## Independent executable evidence

I used a fresh modular evaluator based on factorial prime-adic valuations
and unit-factorial tables, followed by Horner evaluation of the upper
tail. This differs from both author methods: exact integer upper-half
coefficients and a streaming whole Pascal row. Without importing any
author or predecessor code, 481 cached index/modulus evaluations verified
all160 one-prime cases, all21 exceptional cases, all160 zero-suffix cases,
all80 iteration cases, all12 canonical congruence examples and both
counterexamples modulo625. No full enormous a_R or compiler witness
was materialized.

All seven immediate dependency byte pins authenticated:

| Dependency | SHA256 |
|---|---|
| complete83_independent_gamma_scout.json | `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20` |
| complete83_independent_gamma_scout.md | `bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41` |
| complete83_gamma_power_tests.md | `4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b` |
| complete75_gamma87_compiler_order_filters.md | `43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3` |
| complete75_half_binomial_compiler.md | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| pell_kernel_half_binomial42.md | `0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992` |
| ../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md | `44ed02164f61e410bb377b52aa292abf476e025eeea1052784f30d654a0522fa` |

Fresh exact frozen-author replays from `/` passed with normal Python and
`python3 -O`. Required checks use explicit exceptions; dependency hashes,
duplicate/nonfinite JSON rejection and recursive type-exact receipt
comparison are present. This is a bounded formula/proof review, not a
fresh audit of all ancestor compiler sources or a fixed-arity certificate
construction. No repository file was edited.

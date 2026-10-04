# Independent source and proof review of the prime-index free83 collapse

**PASS; no requested change.** I read the complete frozen helper and companion,
checked the actual complete source and its formal specialization, and challenged
the prime-progression, first/main ratio and auxiliary integrality arguments. The
result refutes the named free-coefficient 83 candidate on its inherited valid
compiler slices. It does not improve the sound84 bound or address arbitrary
83-operation circuits.

## Frozen author bytes

| File | SHA256 |
|---|---|
| [free_coefficient83_prime_outer_collapse.py](free_coefficient83_prime_outer_collapse.py) | `b87c6b8f03bd36f39a385717f118d265a2df7b8fe0a3b4ddfe8ff7b8ee60f515` |
| [free_coefficient83_prime_outer_collapse.json](free_coefficient83_prime_outer_collapse.json) | `bc1477dbf8afb849224722925ccd6fe5d48f59fec661fcb02ccec53204605287` |
| [free_coefficient83_prime_outer_collapse.md](free_coefficient83_prime_outer_collapse.md) | `d49cfcb09c8e6f422a5922c00eaeb3f8a0759d9e1772899659db968d43205abb` |

All nine dependency hashes recorded in the frozen receipt were independently
matched to the on-disk files. The receipt's self-source hash matches the helper;
its complete packet equals the pinned `complete83_free_coefficient_scout.json`
packet. In particular, no formerly open ancestor metadata was silently changed.
The exact degree 111 is inherited from that identical source certificate rather
than newly established by the tests in this review.

## Complete source and evidence audit

I checked all 83 literal operations, source closure, freshness and backward
liveness: 46 multiplications, 37 additions/subtractions, 18 witnesses and all
25 free ports are live. The formal specialization supplies every port, including
`s=Y/q^3`, `h=(k-R-1)/(qY)` and
`T=(V+c+Rf^2)/(cf)`. Its other rational denominators are H and Delta. They
are nonzero for the positive construction; formal equality alone does not
prove integral or positive coordinates.

The helper's 37 exact coefficient cuts are justified before each cut is reused.
They recover the actual original C/W, sheared transport, packed R, first/main/
input roots and current auxiliary V. Thus the full source becomes the product
of the seven displayed factors minus Delta. The independently interpreted
seven-operation finalizer includes all six products and the subtraction; its
value is zero at `(1,1,1,1,1,1,Delta)`. No factor sign or finalizer cost is omitted.

As supplementary checks, a separate short Fraction interpreter authenticated
the packet and followed every row on 24 deterministic signed/rational formal
bindings. It matched all 168 independently calculated factor values and all
24 full outputs, comprising 1,992 row evaluations. These checks are not a
replacement for the exact coefficient argument. Fresh normal and optimized
`--expect` replays of the frozen author helper from `/` both passed. No
predecessor or archived Python was executed.

The receipt accurately reports 84 gamma states, 43 Frobenius cases, twelve
auxiliary CRT cases and two trial-certified host primes. Its small outer host
is explicitly outside the compiler recipe. The sampled large prime is not
asserted to hit the strict first/main ratio. Auxiliary congruences are checked
modulo cf via an exactly divisible representative modulo Scf; this does not
materialize V, y, T or a full positive zero.

## Mathematical challenge

The original slack is positive after the stated width choice. With w=1 and
transport quotient one, the transport factor is exactly one, while the shifted
mask identity gives `0<R+1<q^4`. R is fixed before choosing s and the main index.
The choice `H=3*lprime` with `lprime=Cprime*(1+5t)+1` uses a reduced prime
progression: `Cprime=2 mod 5`, so `gcd(Cprime+1,5*Cprime)=1`. Its period
`L=2*(lprime-1)` is prime to five. Consequently the later progression
`p=Dwidth mod 4L` is reduced, since Dwidth is a power of five.

The input construction uses its actual odd index u and the elementary positive
gamma recurrence; delta and rho are positive integers. Main gamma is integral
on the selected progression and sigma is positive on its tail. The distinct
quadratic fields prove theta irrational. The finite Fourier filter, together
with prime equidistribution and the prime number theorem for a fixed reduced
progression, correctly supplies infinitely many prime-index interval hits.
The inherited strict conjugate-error estimate then gives the ratio, positive
eta/zeta and positive integral h. Ordinary irrational rotation alone would not
justify this prime restriction.

I checked the qualitative prime theorem against [Caragea and Lee,
Proposition 7](https://link.springer.com/article/10.1007/s43670-022-00031-9).
I also checked the cited Fourier filter and progression count in [Bhakta et al.,
Section 3.5](https://arxiv.org/pdf/2109.03746), rather than importing their
additional elliptic-curve hypotheses or quantitative conclusion. Dirichlet,
Vinogradov and the fixed-progression prime number theorem remain external
existence theorems, not results established by these bounded tests.

Finally, p prime and greater than Delta gives `c=+1 or -1 mod p` by Frobenius.
Together with odd c this proves `gcd(c,8p)=1`, so the two auxiliary index
congruences are compatible. For `f=chi_A(2p)` and
`S=Delta*psi_A(2p)`, the scaled strong factor is Delta. The odd quotient has
residues `V=-R mod c` and `V=-c mod f`; the return at 8p and triplication
justify the latter. Since `gcd(c,f)=1` and `f^2=1 mod c`, the current T is an
integer. All its numerator terms are positive. The auxiliary factor is one.
This closes positivity and integrality of all 18 coordinates in the same tuple.

The growing prime main indices exceed fixed R, so the construction supplies
infinitely many full positive zeros for each ordinary input, including every
input of the inherited empty-language compiler. Failure of the literal inverse
`i=2*chi_A(p)/c` is additional evidence, not the basis for the false-input claim.
The proof constructs full zeros by existence; neither this review nor the
finite receipt prints one of those giant valid-compiler zeros.

## Replay

After the author trio is installed in the research directory, from any working
directory:

```sh
review_wip=/absolute/path/native-stream-queue
python3 "$review_wip/free_coefficient83_prime_outer_collapse.py" \
  --root "$review_wip" \
  --expect "$review_wip/free_coefficient83_prime_outer_collapse.json"
python3 -O "$review_wip/free_coefficient83_prime_outer_collapse.py" \
  --root "$review_wip" \
  --expect "$review_wip/free_coefficient83_prime_outer_collapse.json"
```

This is a bounded source/proof cross-read note, not a new compiler API, a new
exact-degree computation, or a finite proof of prime equidistribution.

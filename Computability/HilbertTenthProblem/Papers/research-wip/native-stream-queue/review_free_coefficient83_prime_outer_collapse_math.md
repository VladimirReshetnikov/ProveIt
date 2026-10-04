# Independent mathematical review of the prime-index free83 collapse

**PASS; no unresolved mathematical finding.** The frozen
[prime-index construction](free_coefficient83_prime_outer_collapse.md)
gives infinitely many full positive zeros of the unchanged free-coefficient
83 source at every positive ordinary input on every inherited valid
fixed-program slice. In particular it refutes that candidate's intended
representation of the rejecting compiler. This is a full ordinary-input
result, not an inference from failure of the literal witness inverse. It
does not exclude unrelated 83-operation polynomials or other coefficient
recipes, and it does not change the sound 84-operation universal bound.

I read the complete final proof and its evidence boundary, inspected the
literal source as data, and independently challenged the following steps.

## 1. The original outer bound and the prime progression

The choices `Z=1`, `W=2^(2dx+b)`, `C=W+1`, `F=(K0+1)C`, `w=1` and
`transport_quotient=1` give the actual original-bound expression C and
transport factor one when `alpha=q-F-W-2dx-2>0`. No weakened slack or
negative input-root tuple is substituted. The shifted source mask convention
is preserved. Its exact packed remainder bounds give the sharper estimate
`R<=q^4-q^3+q-2`; hence `0<R+1<q^4<=E`, including s=1. R is odd and
does not depend on s or either Pell index. This explicit sharper bound was
the only wording precision requested during my draft review and is present
in the final note.

Since `Dwidth=dN` is a power of five, it is odd and is one modulo four.
Thus q is minus one modulo three and two modulo five. The integer
`Cprime=4q^3(q+1)/3` is two modulo five. For `s=1+5t`, the progression
`lprime=Cprime+1+5Cprime*t` is reduced: its first term is coprime to
Cprime and is three modulo five. Dirichlet therefore supplies a prime
lprime>3, fixed before the main-index search. With `Y=q^3s`, the actual
`H=4Y(q+1)+3` is `3*lprime`. The even number
`L=2(lprime-1)` is a return exponent for 2 modulo H and is not divisible
by five. Consequently `gcd(Dwidth,4L)=1`. The main prime progression
`p=Dwidth mod 4L` is reduced, has p=1 modulo four, and forces the required
`2^p=q mod H`. These facts do not depend on treating a diagnostic small
mask choice as a genuine compiler.

The positive input construction uses the literal exponent u. The exact
gamma recurrence supplies positive integral rho and delta and the positive
input root `chi_A(u)`. On a sufficiently late main-index tail the same
recurrence makes `sigma=(chi_A(p)-a*psi_A(p)-q)/H-rho` positive integral.
Both input and main norms then equal one.

## 2. The analytic existence dependency is sufficient

For the chosen arbitrary positive s, A is even and Delta is odd, whereas
`v2(P^2-1)=Dwidth+2*v2(Y)+2` is odd. The two nonsquare discriminants have
different square classes. Their positive quadratic units cannot have a
rational logarithmic ratio: an equal nontrivial power would lie in the
intersection of the distinct quadratic fields, namely the rationals,
contradicting its nonzero irrational Pell component. Thus theta is
irrational; the elementary inequalities `A<P<2A^2-1` give
`1/2<theta<1`.

I independently opened the primary
[Caragea--Lee paper](https://link.springer.com/article/10.1007/s43670-022-00031-9).
Its paragraph preceding Proposition 7 and the d=1 case of that proposition
state the required qualitative equidistribution of irrational multiples
of primes. The final note correctly derives the reduced-progression
version, rather than silently replacing all primes by progression primes:
the finite Fourier residue filter leaves only irrational frequencies,
and the prime number theorem in arithmetic progressions supplies the
normalization by the progression's own prime count.

I also read the cited portions of
[Bhakta et al.](https://arxiv.org/pdf/2109.03746): the proof of Lemma 3.16
contains the Fourier filter, and printed page 15 records the progression
prime count. The note uses these only as context for those steps; it does
not import their additional elliptic-curve hypotheses or quantitative
bounds. Qualitative density is sufficient, because the modulus, interval
and all positivity thresholds are fixed before p varies.

Applying that result to `theta/(E/2)` yields arbitrarily late hits in the
stated interior interval. The floor therefore has
`n=(R+1)/2 mod E/2`. The previously pinned exact conjugate-error estimate
preserves `kY<c<k(Y+1)`. It produces positive eta,zeta and, on a tail,
positive integral `h=(k-R-1)/E`. The actual first norm and index factor
equal one. It is legitimate to discard all primes `p<=max(Delta,R)`;
neither a finite prime search nor ordinary unrestricted rotation is used
as a substitute for the prime theorem.

## 3. The auxiliary divisibility and all-positive completion

For a prime p>Delta, the binomial identity in
`F_p[t]/(t^2-Delta)` gives
`psi_A(p)=Delta^((p-1)/2)=+1 or -1 mod p`.
Thus `c=psi_A(p)` is coprime to p. It is odd because p is odd, so
`gcd(c,8p)=1`. This closes the auxiliary CRT compatibility that is missing
from a general wrong-index family.

Set `f=chi_A(2p)`, `S=Delta*psi_A(2p)` and choose the positive CRT
representative `ell_aux=R mod c`, `ell_aux=3p mod 8p`. The latter index
is three modulo four. The scaled strong factor is Delta. For
`V=chi_S(ell_aux)/S`, the odd quotient polynomial gives `V=-R mod c`.
Modulo f, the Pell state at index 4p is minus one and at 8p is one;
`psi_A(3p)=(2f+1)c`. Together with `S^2=-Delta mod f` and the negative
odd-quotient sign, this gives `V=-c mod f`.

The norm implies `f^2=1 mod c` and `gcd(c,f)=1`. Hence
`T=(V+c+R*f^2)/(c*f)` is integral. Every summand is positive, so T is
positive and its literal source expression recovers V. The auxiliary
Pell norm is one. All 18 supplied witnesses are therefore positive and
the actual factor list is `(1,1,1,1,1,1,Delta)`. Its paid finalizer is
zero. Distinct unbounded prime indices give distinct c and infinitely
many full tuples with the same ordinary x and compiler constants.

This proof never restores a positive parent i before using a parent
soundness theorem. The nonintegral value `i=2chi_A(p)/c` is merely a
separate consequence after the full false-input construction is complete.

## 4. Source and finite-evidence scope

My independent data-only comparison confirms that the complete saved
packet is identical to the frozen free83 parent packet. A fresh static
walk confirms 83 live rows, all 25 free ports live, and 46M+37A. Exact
degree 111 is inherited from that identical source; this review does not
repeat its degree expansion or the author's 37 coefficient cuts.

The final evidence section correctly limits its two prime/outer host
checks and its bounded gamma, Frobenius and auxiliary CRT cases. In
particular the sampled prime is not claimed to be a ratio hit; the small
numerals are not compiler exports; and reduction of the huge auxiliary
quotient modulo cf is not a materialized full zero. I did not execute the
author, predecessor or archived Python, and did not simulate prime density.
No repository or frozen predecessor file was changed.

## Frozen dependencies

All twelve hashes below were checked against the final author trio and
its nine current source/proof dependencies. The external primary papers
are cited above; their mathematical results are explicit proof premises,
not outcomes of the finite checker.

| File | SHA-256 |
| --- | --- |
| `free_coefficient83_prime_outer_collapse.py` | `b87c6b8f03bd36f39a385717f118d265a2df7b8fe0a3b4ddfe8ff7b8ee60f515` |
| `free_coefficient83_prime_outer_collapse.json` | `bc1477dbf8afb849224722925ccd6fe5d48f59fec661fcb02ccec53204605287` |
| `free_coefficient83_prime_outer_collapse.md` | `d49cfcb09c8e6f422a5922c00eaeb3f8a0759d9e1772899659db968d43205abb` |
| `../../1980/HALF_PARAMETER_PELL_92_PROOF.md` | `c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b` |
| `complete75_half_binomial_compiler.md` | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| `complete75_weakened86_all_input_collapse.md` | `46f3e0f25fc4efeb3f8129b77c3df988283c7a818ee2af330e8e8f460dc8d017` |
| `complete75_weakened86_auxiliary_sign_lift.md` | `491ac3c3755efed1c6c89f7e07a752c25fb040859cac8c07d7db25e803c62c53` |
| `complete75_weakened86_infinite_outer_family.md` | `74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2` |
| `complete75_weakened86_rejecting_compiler.md` | `186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78` |
| `complete83_free_coefficient_scout.json` | `682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016` |
| `complete83_free_coefficient_scout.md` | `867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31` |
| `complete83_free_coefficient_scout.py` | `a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485` |

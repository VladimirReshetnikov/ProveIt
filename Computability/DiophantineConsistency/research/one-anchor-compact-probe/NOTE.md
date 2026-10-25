# One-anchor compact-cell finite exploration

The complete finite model at anchor 2079 supports cell length 7309 and
uses 172,011 raw big-endian bytes across its four integer ports. That saves
8,976 bytes against the preserved two-anchor7691 tuple. This exploratory
receipt does not itself prove the unbounded native interface: the full
ordinary proof and final certificate are in
[`../one-anchor-independent/`](../one-anchor-independent/README.md).
The final verifier was derived from this probe, so the two scripts are
not claimed to be independent implementations.

`probe.py` authenticates the complete preserved radix55 page and its exact
decoder before decoding all 430 actions and 943 tiles. It retains the
entire 3297-slot coefficient array, clears old anchors 1095, 2195, 3296,
and sets `c[2079]=3M`, where `rho=2^47` and `M=2^44`. All slots after
2079 are zero. The physical support contains 980 positions, including
the two zero-coefficient dummies 1063 and 1064; 978 coefficients are
nonzero. The coefficient sum is unchanged, exactly 3,882,691,076,540,335.

Write `G_n(x)=1+x+...+x^(n-1)`. The entire control polynomial is

```
Psi(x,t)=x^1003*(x^20+t^17)*G_8(tx)
       +t^8*x^983*(x^30+t^17)*G_9(tx)
       +t^34*x^2079*(2t-1).
```

The probe independently expands `Psi(x,1)` into all 35 control positions
and `1024*Psi(x,2)` into their complete weighted coefficient array.
The other 943 coefficients retain the complete decoded selector recipe.

For `L=7309`, put `B=rho^L`, `beta=B-1` and

```
DC=rho^30+rho^62+rho^1137*G_943(rho)
   +sum_e c[e]*(rho^(4161-e)+rho^(5228-e)),
K=DC+B*rho^42,
MC=beta-sum_(e in E,e!=1)rho^e-2*rho^1063,
Ccore=sum_(e=1013)^1021 rho^e
     +sum_(e=1065)^1072 rho^e+rho^2079,
padding=2^25*rho^6343-rho^6325,
MF_native=4+(2^46-2)*(rho^4161+rho^5228)+Ccore+padding,
MF_source=MF_native+beta.
```

All reciprocal terms above have nonnegative exponents, and all DC
coefficient residues are disjoint. Padding is exactly 18 complete fields
6325..6342 and 25 low bits at 6343, totaling 871 bits. The core has 109
bits. Whole-integer bit counts give `pc(MF_native)=980` and
`pc(MC)=47L-980`. Scalar boxes and the two origin residues are verified
on these actual integers.

The support checks are complete enumerations, not sampled witnesses.
They include all 17 label-copy targets, the selector-count target 2079,
both clause fields, their predecessors, every field of the zero padding
band 6325..6364, the final nonzero field 7307 and zero field 7308.
The only phase-support difference 1065 is `(2079,1014)`, while clause
difference 1067 and neighbor difference 1068 are absent.

Neighbor difference 1066 is **present**: its sole pair is `(2079,1013)`.
Consequently the upper clause predecessor is `Aadj+2^18*x2079`; the
probe explicitly records and checks that extra term. Under at most one
selected tile, `Aadj<=2M-1024`; the added term and incoming carry 29
remain below rho. The ordinary proof establishes the one-tile premise
before using this reset. The unconditional adjacent-coefficient sum in
the JSON receipt is a different quantity and is not used as this bound.

The exact Boolean local convolution maximum is
3,882,691,076,540,335, reached at fields 4161 and 5228. Allowing two
extra dummy units leaves that maximum unchanged. The recorded numerical
carry inequality also allows the entire spatial digit up to three and
the temporal bound `3rho/4`. Establishing that temporal bound, cyclic
carry stabilization and all arbitrary-witness semantics belongs to the
ordinary proof. The safe-dummy local/spatial/temporal maximum exponents
are 6291, 1105, 1063; the check uses `L-(e+1)>=3` for each, giving the
strict combined bound below `q/rho^2` when the later cells lie inside
the word.

The bounded length search checks every integer beginning at 7308.
7308 is composite and 7309 is prime and passes the complete controller.
Here `d=343523`, the exact base-two and B orders are 23 modulo 47 and
1044 modulo 7309, and `lcm(23,1044)=24012` is coprime to d. The first
eligible progression candidate above d is the prime
`lambda=360181=15*24012+1`. Its lift is
`B^(lambda-1)=1+41301*lambda mod lambda^2`, proving valuation exactly one.

| Modulus | B | K | B squared | 1+BK+B squared |
| ---: | ---: | ---: | ---: | ---: |
| 47 | 25 | 1 | 14 | 40 |
| 7309 | 3446 | 4088 | 5100 | 597 |
| 360181 | 149905 | 316516 | 176616 | 144105 |

Every K residue is checked by three complete routes: dense Horner
evaluation of all 3297 coefficient slots; direct decoded tile/control
expansion with the entire 943-term unit kernel; reduction of the actual
whole integer K. Exact prime trial division and all proper-order tests
are performed, including factors 2, 3 and 29 of 1044.

| Complete integer port | Bits | Raw bytes |
| --- | ---: | ---: |
| beta | 343523 | 42941 |
| K | 345498 | 43188 |
| MC | 343523 | 42941 |
| MF_source | 343524 | 42941 |
| Total | | 172011 |

`RESULTS.json` binds the full script, authenticated source page, decoder,
seed, actions, indexed tiles and all 3297 coefficients. Reproduce it with
`python3 -B probe.py` and `python3 -B -O probe.py`; both pass. The
exploratory program reports any geometry counterexample in its receipt.
The final certificate additionally rejects all failed checks by explicit
exceptions, pins the complete ordinary proof, and requires the exact
advertised length, prime, orders and controller values. Neither receipt
claims a new formal-kernel replay or globally minimal equation.

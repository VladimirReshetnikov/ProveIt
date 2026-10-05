# Multiway Hadamard packing and a fully paid finite synchronous certificate

There is a useful exact extension of the existing two-word packing: **one product of k specially loaded finite words isolates their k-fold coefficientwise product in one central band**. For three factors this gives a concrete finite-integer certificate for a synchronous Boolean rule, using two ordinary products after loading. However, the fully charged certificate is larger than direct cell-by-cell verification. The unresolved interface is still the synchronized variable-length loader and history representation, not the local Boolean algebra. No universal-polynomial improvement follows.

## 1. Existing coverage and new scope

I read these existing notes in full as inert text in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`:

| Note | SHA256 |
| --- | --- |
| `review_definable_operations_de37a66d1.md` | `517cc3caf39e16e559802c3b8e50c5fee5efa2c754243be2cd8f18e9c8e67600` |
| `finite_word_hadamard_skew.md` | `5072d56a1681e302780eac97ceea1920afbc4ed36338fa2b3eaa88d244000ef8` |
| `native_binary_reversal_inline129.md` | `b2fa2c6a46d7a7500c52bcfb3259026c7321bf158b57cbabbeb0f7d330c92abb` |

The first separates surreal/Hahn coefficientwise definability from paid ordinary-integer computation. The second already proves a carry-free two-factor central band and complete fixed-width graphs; its short extraction component expressly does not supply a variable-spacing loader. The third supplies a complete padded binary reversal relation, but uses an existing native AND component and does not supply that missing variable-spacing loader. None of their code was executed or imported. This is a bounded extension of that local coverage, not a literature priority claim.

Everything below uses finite ordinary integers. Width n and horizon T select a finite source; they are not uncharged runtime length parameters. The local truth table is derived below, and no universality theorem about that rule is invoked.

## 2. Exact k-factor central-band theorem

Fix n>=2 and k>=2. For k length-n digit words `a^(0),...,a^(k-1)`, let

```
K = n^(k-1),          L = (n-1)(K-1),
A_0 = sum_(i<n) a^(0)_i B^(K*i),
A_r = sum_(i<n) a^(r)_i B^((n-1)n^(k-1-r)(n-1-i)),  1<=r<k.
```

Assume the digits are nonnegative, bounded by d_r in word r, and `B>product_r d_r`. Expand `N=product_r A_r`. The exponent belonging to a tuple of indices is

```
e = L + K*i_0 - (n-1)J,
J = sum_(r=1)^(k-1) n^(k-1-r)*i_r,    0<=J<K.
```

**All n^k tuple exponents are distinct.** A collision implies `K*(i_0-i'_0)=(n-1)(J-J')`. Since `K=1 mod(n-1)`, the first index difference is0 or±(n-1). The latter two possibilities are impossible: their left side has magnitude `K(n-1)`, whereas the right side has magnitude at most `(n-1)(K-1)`. Hence the first indices agree, then J agrees, then base-n uniqueness gives every index equal. This argument also covers n=2, when the congruence itself is vacuous but the same bound excludes both nonzero differences.

Each product coefficient is consequently a single digit product, at most `product d_r<B`. There are no carries anywhere, including from below the selected band. For the all-equal tuple `i_0=...=i_(k-1)=i`, the exponent is `L+i`. These n diagonal tuples occupy all n positions of `[L,L+n)`; injectivity excludes every other tuple from that band. Therefore

```
floor(N/B^L) mod B^n
    = sum_(i<n) product_(r<k) a^(r)_i * B^i.       (1)
```

At k=2 this is exactly the existing skew layout. At k=3 the weights are `n^2`, `n(n-1)` and `n-1`, with the last two words reversed, and `L=(n-1)(n^2-1)`. Root independently challenged the injectivity argument and its k-factor extension; the finite evidence below checks the three-factor specialization separately.

The product itself costs k-1 multiplications **after all k inputs are loaded**. Ordinary Horner loading costs `2k(n-1)` operations with fixed radices, before digit validation, original-input binding, extraction and numeral construction. Equation(1) does not declare those costs free.

## 3. A specific synchronous Boolean relation

Use a cyclic row of n bits `b_i`, with indices modulo n, and define

```
l_i=b_(i-1),    c_i=b_i,    r_i=b_(i+1),
f(l,c,r)=c+r-cr-lcr.
```

Its outputs on `000,001,010,011,100,101,110,111` are respectively

```
0, 1, 1, 1, 0, 1, 1, 0.
```

Thus f is Boolean, proved by eight substitutions. We do not use a universality result for this truth table, nor transfer an infinite-line or background convention to a finite cyclic row.

Choose B=4. In (1) take the three words `c_i`, `r_i` and `1+l_i`. Their digit bounds are1,1,2, so B=4 prevents every carry. With

```
A = sum_i c_i 4^(n^2*i),
C = sum_i r_i 4^(n(n-1)(n-1-i)),
D = sum_i (1+l_i)4^((n-1)(n-1-i)),
P = 4^((n-1)(n^2-1)),       Q = 4^n,
```

two ordinary products form `N=(A*C)*D`, and its central word is

`H=sum_i c_i*r_i*(1+l_i)4^i`.

If `Cword=sum c_i4^i`, `Rword=sum r_i4^i` and `Nextword=sum b'_i4^i`, the local update is equivalent to the single equality

`Cword+Rword-Nextword=H`.                            (2)

Indeed, its difference is `sum_i (f(l_i,c_i,r_i)-b'_i)4^i`. Each coefficient lies in{-1,0,1}; reduction modulo4 and induction force every coefficient to vanish. Conversely the componentwise update gives(2). No unsupported bitwise operation appears in this equality.

## 4. Complete finite positive-witness graph

For fixed n>=2 and T>=1, the external parameters are ordinary nonnegative integers x,y. The represented relation is:

> `0<=x,y<2^n`, and y is the ordinary binary encoding of the result of exactly T synchronous updates on the cyclic n-bit row encoded by x.

Use `n(T+1)` strictly positive bit hats `hat b_(t,i)` and put `b=hat b-1`. For each hat compute `b=hat b-1`, `other=hat b-2`, `boolean=b*other`, requiring the last register to be0. These three paid operations enforce exactly `hat b in{1,2}`. All intermediate history bits are bound by these guards.

Two ordinary binary Horner chains bind the first and last rows to x,y. There is no free conversion from radix4 to the external ordinary binary words. Also build a radix4 Horner word for each of the T+1 rows. The penultimate accumulator of such a chain is `S=sum_(i=1)^(n-1) b_i4^(i-1)`, so the cyclic right-neighbor word is produced in two more operations per transition:

`wrap=b_0*4^(n-1); Rword=S+wrap`.

For each transition, three more Horner chains load A,C,D with the radices `4^(n^2)`, `4^(n(n-1))`, `4^(n-1)`. Their digit order is respectively reversed c order, forward r order, forward `(1+l)` order. The third digits are the already supplied positive bit hats, so the added1 is genuinely shared, not omitted.

Introduce five positive extraction coordinates per transition:

`Hhat, low_hat, high_hat, low_slack, middle_slack`.

The complete nine-row extraction is

```
pair=A*C; product=pair*D;
q_high=Q*high_hat;
middle_plus_high=Hhat+q_high;
upper=P*middle_plus_high;
rhs=low_hat+upper;
lhs=product+(P*Q+P+1);
low_bound=low_hat+low_slack;
middle_bound=Hhat+middle_slack.
```

Impose three comparisons: `lhs=rhs`, `low_bound=P+1`, `middle_bound=Q+1`. With `low=low_hat-1`, `high=high_hat-1`, `h=Hhat-1`, they say precisely

`N=low+P(h+Q*high), 0<=low<P, 0<=h<Q, high>=0`.

Euclidean uniqueness gives h=H. The offset `PQ+P+1` compensates all three positive hats. Conversely the actual quotient and remainders give positive hats and slacks even for the all-zero input. Since H has radix4 digits at most2, it is below Q. The graph never permits a negative middle remainder masquerading as the preceding quotient.

Three further additions/subtractions form `target_hat=Cword+Rword-Nextword+1`, and the fourth transition comparison is `target_hat=Hhat`. This supplies(2). Every history step is checked. Completeness follows by loading the actual finite trajectory and its Euclidean remainders; soundness follows from Boolean guards, boundary loaders, (1), Euclidean uniqueness and (2), with no native Pell/AND theorem invoked.

The external words can be0. If strictly positive external ports are desired, represent `xhat=x+1,yhat=y+1`, add1 to the two boundary loader outputs, and compare to those positive ports. This explicit variant adds2A and no witnesses or comparisons; it is not silently included in the counts below. All existential witnesses in the emitted graphs are already strictly positive.

## 5. Every arithmetic cost, including the fixed numerals

For fixed integer literals, the producer count before converting comparisons to a polynomial is:

| Component | M | A |
| --- | ---: | ---: |
| Guards for n(T+1) bit hats |n(T+1)|2n(T+1)|
| Two external binary loaders |2(n-1)|2(n-1)|
| T+1 radix4 row loaders |(T+1)(n-1)|(T+1)(n-1)|
| Three skew loaders per transition |3T(n-1)|3T(n-1)|
| Cyclic right-word production |T|T|
| Complete product and extraction |4T|5T|
| Transition target hats |0|3T|
| **Total producers** |**(5n+1)T+4n-3**|**(6n+5)T+5n-3**|

Thus the producer total is `(11n+6)T+9n-6`. There are

- `n(T+1)+5T` positive existential witnesses;
- `m=n(T+1)+4T+2` equations, of which `n(T+1)` already have computed zero residuals.

Forming the remaining `4T+2` residuals, squaring all m residuals and summing them gives a complete SOS polynomial with

```
M = (6n+5)T+5n-1,
A = (7n+13)T+6n,
total = (13n+18)T+11n-1.                           (3)
```

For one transition these counts are `20n` producers and `24n+17` full polynomial operations. All source rows and supplied coordinates are live in the saved arrays.

The exact degree is6 on every fixed n,T slice. The three skew loaders are nonzero linear polynomials in bit hats, so their product gives a nonzero cubic term in an extraction residual; that residual's square has degree6. Every other residual has degree at most3. Highest parts cannot cancel in a real sum of squares. Fixed numeral construction does not alter this degree.

To construct every derived numeral from literals1 and2, use the standard explicit binary chain for `2^e`, costing

`mu(e)=floor(log2 e)+popcount(e)-1`, for e>=1.

Construct separately the powers with exponents

`2, 2n^2, 2n(n-1), 2(n-1), 2L, 2n`.

They provide4, all three skew radices, P and Q; the third skew radix is also the cyclic-wrap coefficient. Then construct `PQ`, `PQ+P+1`, `P+1`, `Q+1`, costing1M+4A. The exact additional prefix is therefore

`[mu(2)+mu(2n^2)+mu(2n(n-1))+mu(2(n-1))+mu(2L)+mu(2n)+1]M+4A`. (4)

No chain is claimed optimal. In particular, repeated numerals at small n are deliberately separate live computations. All exponents are positive for n>=2; `mu(1)=0`, and no hidden exponent-zero construction is needed. The twelve saved arrays cover n=2,3,4 and T=1,2 in both literal and constructed-numeral conventions. At n=2,T=1 they cost40/65 producers/SOS, or57/82 with all derived numerals built. Literal bit lengths are O(n^3); the model charges each multiplication by such a fixed numeral, not its bit-complexity cost.

## 6. A direct comparator shows this is not a gate saving

A conventional fully guarded local certificate uses the same `n(T+1)` bit hats and two boundary binary loaders. For every cell compute `cr`, `lcr` and `c+r-cr-lcr` in2M+3A and compare to the next bit. It requires no extraction witnesses or large skew constants. With the same explicit SOS convention its total is

`(13T+9)n+1` operations, of which `(5T+4)n` are multiplications.

This is a sufficient schedule, not an optimality claim. It already beats (3) by

`18T+2n-2 > 0`.

Packing has compressed the variable-by-variable local products into two ordinary products per time step, but its loaded integer encodings, guards, shifts, remainders and finalizer more than consume that gain. Treating the loaded encodings or a Hadamard call as free would reverse this comparison by hiding precisely the missing work.

## 7. What remains at variable width or unbounded history

The emitted family does not accept n or T as ordinary runtime inputs. Increasing either changes the source length and witness count. For fixed n the cyclic system has only2^n configurations, so an unrestricted temporal horizon alone is not an unbounded-memory computational substrate. A general accepting-history compiler must let the spatial representation grow and bind its input/background/boundary convention.

A fixed-arity use of (1) would need a fully paid common-width graph for

```
KA=4^(n^2), KB=4^(n(n-1)), KC=4^(n-1),
P=4^((n-1)(n^2-1)), Q=4^n,
A=the n^2-spaced center word,
C=the reversed n(n-1)-spaced right-neighbor word,
D=the reversed (n-1)-spaced (1+left-neighbor) word,
```

with the same n everywhere, ordinary binary input binding, digit guards, cyclic boundary shifts and a quantified duration/history encoding. Naming these relations POWER, reversal, shift or Hadamard does not supply their Diophantine graph or count. The frozen reversal component has a precise projection but does not provide all these synchronized loaders or eliminate its own use of AND. The earlier two-word loader gap therefore persists; the multiway identity clarifies its new required exponents rather than resolving it.

There is also a simple unconditional obstruction to a stronger free-evaluator interpretation. No fixed straight-line polynomial evaluator using only ordinary `+,-,*` and fixed integer constants can equal `x AND y` for every nonnegative pair. At y=1 its polynomial specialization would equal `x mod2`, a bounded but nonconstant function on all nonnegative integers. A nonconstant real polynomial is unbounded there, while a constant cannot alternate. Consequently unbounded Hadamard requires an additional representation/range/quotient/quantified interface. This argument does not prohibit existential Diophantine graphs, a fixed-width family, or a charged division/shift primitive.

## 8. Fresh evidence and frozen scope

The fresh standard-library checker and receipt are optional companions to this bounded note:

- `/tmp/hadamard_next_arithmetic_checks.py`, SHA256 `5246d7aa225630bc272660834ac077b91629f611989d979716cf78e12d0e20fd`;
- `/tmp/hadamard_next_arithmetic_checks.json`, SHA256 `9415b89a1eae04efb5869b85d6f7cef02ff2eed85e94f1d80d55fa6b076c5b5d`.

They save twelve complete small arrays, positive witness lists, comparisons, residuals and full finalizers; all counts, topology and liveness are checked. Constructed-numeral arrays contain only literal operands0,1,2. Fresh exact checks covered18495 three-way exponent positions at n=2 through16,5456 complete one-step input/output word pairs at n=2 through6, and744 complete positive trajectory zeros across n=2 through6, T=1,2,3 and both numeral conventions. These are corroboration of the proofs above, not extrapolated universality. The all-k identity and all-n,T source theorem are proved symbolically in the note; the finite positional probe tests k=3.

The new writer and its normal and `-O` exact checks from `/` passed before freezing. Only these newly authored checks executed. No supplied, archived, copied predecessor or frozen program was executed/imported, no repository file changed, and no external definability/ordinal/real operation was treated as a paid integer primitive. The local claims were derived directly; no new literature-dependent universality fact is asserted.

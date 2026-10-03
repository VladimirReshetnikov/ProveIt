# Independent review: five-coordinate congruence atom

PASS on source SHA256 `f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc`. This is a review of the literal atom schedules, their natural witness semantics, and their complete polynomial relation. It does not certify a global arithmetic minimum or a new universal equation bound.

Let the modulus `d>=1` be fixed and let `L` be an already evaluated integer. Use five natural auxiliary coordinates `(q+,q-,b,s,h)` and put `r=b(s+1)`. The rows are

```
q+ q-
L - d(q+ - q-) - r
r + h - (d-1)
b(b-1)
(b-1)s
```

The last row is the negative of the statement's `(1-b)s`; their zero sets and squares agree. Booleanity gives `b=0 or 1`, and the range row gives `0<=r<d`. Hence the second row is the unique Euclidean division `L=dq+r`, including negative `L`. The first row uniquely splits `q` into its nonnegative positive and negative parts. If `r=0`, then `b=0`, and the last row forces `s=0`. Otherwise `b=1,s=r-1`. Finally `h=d-1-r`. Thus there is exactly one complete natural tuple for every `L,d`, and `1-b` is the divisibility truth bit. For `d=1` the same argument gives `r=b=s=h=0`; there is no exception.

The displayed six-coordinate parent uses a separate remainder `a` and last row

```
a - (2b-1)s - b.
```

Restoring `a=b(s+1)` preserves the first four rows and negates the fifth, identically as polynomials. Consequently the entire parent sum of squares restricted to that graph equals the child sum of squares on **all integer or rational tuples**, without Booleanity or zero-set assumptions. On natural parent zeros, `b=0` gives `a=-s`, so naturality forces `a=s=0`; `b=1` gives `a=s+1`. Every parent natural zero is therefore on the graph. This proves the natural zero-set bijection, not just equality on constructed Euclidean witnesses. The witness domain matters: the unrestricted parent integer zero set need not be on this graph.

The actual child DAG computes `bs=b*s`, `r=bs+b`, and reuses `b-1`. Its five rows use `4M+8A=12` operations. Five squares and four additions cost `5M+4A=9`, giving `9M+12A=21`. The displayed parent uses `4M+9A` for its rows and the same finalizer, totaling `9M+13A=22`. Constants `d` and `d-1` are fixed coefficients. Evaluating `L`, evaluating or sharing an external `1-b` output, the surrounding Boolean circuit, and accumulation into any larger final polynomial are separate charges. In particular, multiplying by `d=1` remains charged in this uniform displayed schedule; no modulus-specific optimality is claimed.

Replacing every congruence atom in the cited natural compiler removes one witness per atom, giving `2I+5C+G` witnesses and retaining `2I+5C+G+1` rows under that compiler's established accounting. The five atom rows are quadratic. Their SOS is exactly quartic because the positive coefficient of `(q+ q-)^2` cannot cancel.

[Independent checker](review_presburger_congruence_five.py) and [receipt](review_presburger_congruence_five.json) pin the actual source before import and restore any preexisting module entry afterward. An independent gate interpreter verifies all emitted rows and complete polynomial identities symbolically for moduli `1,2,3,7,10^100+267`; this is five complete graph identities, 25 row maps and ten charged ledgers. The checker also verifies 175 exhaustive small natural fibres (the proof bounds every possible root inside the searched ranges), 175 truth bits, 120 signed graph evaluations, and six invalid exact-integer/modulus rejections. The general proof above covers arbitrary fixed positive moduli. No author full replay was duplicated for this bounded second review.

Reproduce with the pinned author module wherever stored:

```
python review_presburger_congruence_five.py --source presburger_congruence_five.py --expect review_presburger_congruence_five.json
```

The source's `canonical` and `residuals` are domain-checked; its low-level `build/evaluate` remain construction/evaluation utilities rather than a general hostile-packet authentication interface. The review does not claim otherwise. Source comments and the saved-receipt comparison were strengthened during review to state the exact graph identity and use recursive type-sensitive equality; no formula change was needed.

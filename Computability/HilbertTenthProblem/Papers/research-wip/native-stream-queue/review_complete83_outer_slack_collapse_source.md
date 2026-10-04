# Independent source review of the refuted 83-operation outer chart

**PASS on the authenticated final author freeze, with no outstanding finding.** The complete 83-operation source is an exact signed pullback of the 84-operation parent. It has 18 supplied positive witnesses, exact degree 187, and cost 47M+36A. This is a refuted candidate: its all-input positive-zero construction does not give a universal 83-operation bound.

The independent [helper](review_complete83_outer_slack_collapse_source.py) reads the frozen author receipt and ten pinned predecessor source/proof artifacts as data. It executes no author, predecessor, or archived Python. The [review receipt](review_complete83_outer_slack_collapse_source.json) contains the final author and dependency pins. The final author hashes are:

| File | SHA-256 |
| --- | --- |
| `complete83_outer_slack_collapse.py` | `8e3c335f157e9a237791eeaceffec94415ba9ce8c2638d89d023213cfcbd0fd5` |
| `complete83_outer_slack_collapse.json` | `9b0b05ad969eec99ca761898149ec3798a803fbb591a7bf462bf82a15090c207` |
| `complete83_outer_slack_collapse.md` | `6623a525ab1b0376b1d6a452f8e5618f8e1f64f0a255fdcbcc97611dd3598259` |

The complete author helper and companion were read; the two inherited all-input and auxiliary-sign notes were also read in full. Authentication of the other dependencies is not presented as a new complete review of their original compiler proofs.

## Literal source and complete polynomial

The reviewer constructs the expected child directly from the actual saved 84-row parent, then compares all 83 rows in order. The only deleted row is `q_minus_FZ`; its two consumers are exactly `C_after_alpha` and `gap`. The supplied `alpha` has just one consumer. Replacing it by `alpha_sum`, changing those two consumers and their private `gap_product` producer accounts for every use. Every other row, all seven factors, the final target `A` (the discriminant), fixed numeral ports, and ordinary input are retained. The full graph is closed, single-assignment, and live, including every supplied port.

Write `U=q-F`, `Q=q-1`, and `b=alpha_sum`. Independent exponent-vector coefficient expansion proves the two necessary cuts:

```
(U-Z)-(b-Z) = U-b,
Q*U+(U-Z) = q*U-Z.
```

The source definitions of q and U remain unchanged. All descendants outside these cuts have identical literal definitions. This proves the entire output identity over every commutative ring,

```
P83(b,...) = P84(alpha=b-Z,...),
```

without treating the changed private product as equal. The unchanged finalizer is separately read from the actual source, including the early `norm_pair` and `norm_triple` products. It has six multiplications and the subtraction of Delta. At factor values `(1,1,1,1,-1,-1,Delta)` it returns zero.

The full ledger is 83=47M+36A; exactly one addition was removed. The independent syntactic degree propagation gives 197. The exact formal degree is 187 because the displayed substitution is a linear automorphism of the varying-coordinate polynomial ring, with inverse `b=alpha+Z`, while all fixed numeral values remain unchanged. Thus the parent's uniform exact degree survives every admissible fixed-program specialization. This is a degree theorem about the full polynomial, not a zero-set inference.

The positive forward map is unconditional: every old positive tuple gives `b=alpha+Z>0`. Its inverse is positive exactly when `b>Z`. Nothing in this source audit turns an inverse failure into a false-language theorem.

## Corrected counterexample interface

I cross-read the new existence argument against the literal factors and inherited all-input/sign-lift notes. It does not merely insert old weakened86 tuples into the new source. The exact two changes in the congruence construction are essential: the new first-index factor is fixed at −1, matching the transport factor, and the auxiliary target is R itself.

With the declared outer choice C=0, the current transport factor is `(q-2)-(q-1)=-1`; its `(K0+w)C` term vanishes. Therefore changing the old symmetric witness `X/q³` to the current asymmetric witness `w=X/q` does not disturb this factor. The note distinguishes the paid `MF_source=MF_native+B-1` from the native mask in the packed K formula.

The independent sign choices supply an even `0<j_wrap<2M` with
`j_wrap=omega+t_sign*(M*sigma_sign-K)` modulo `3M`. In the exceptional boundary class, changing omega shifts the four covering residues by two; it does not change the required index sign. The new numerator `K-omega*p+j_wrap*c-M*Fv` removes the old `2epsilon` term. The resulting `R=omega*p-j_wrap*c` and `2n=R-1` modulo E give `h=(k-R+1)/E>0` and the literal index factor −1. The inherited prime progression and rotation arguments are used to choose arbitrarily large strict-ratio hits on this corrected progression, rather than assumed from the earlier target formula.

For the new auxiliary coordinate, the old quotient-polynomial identities supply `V=-R` modulo c and `V=-c` modulo f. Normalized strong gives `f²=1` modulo c and `gcd(c,f)=1`. Consequently

```
T=(V+c+R*f²)/(c*f)
```

is integral. Increasing the odd auxiliary index by multiples of `4pc` preserves both congruences and makes `V>|R|f²+c`, hence T positive. Its literal source value is `c*(T*f-1)-R*f²=V`. The auxiliary factor is +1 and the scaled strong factor is Delta, giving precisely the seven-factor list above. No obsolete `R+2epsilon` target or direct positive inverse is used.

The all-input consequence remains conditional on the already stated actual compiler recipe, Dirichlet theorem, and irrational-rotation existence theorem. This review finds no new missing interface or sign premise. It does not implement these existence constructions, materialize a full compiler zero, or supply a universal 83-operation representation. The author's finite modular and auxiliary checks are explicitly component evidence.

## Independent evidence and replay

Beyond the exact coefficient cuts and complete row comparison, the reviewer checks 40 whole assignments, including 20 rational ones, under the signed pullback. All 82 comparable retained register values agree in every assignment, giving 3,280 checks; the unequal private product is excluded for the stated reason. These checks supplement the symbolic proof.

From any working directory, after installation:

```sh
python3 /absolute/path/native-stream-queue/review_complete83_outer_slack_collapse_source.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/native-stream-queue/review_complete83_outer_slack_collapse_source.json
```

An optional `--author-root DIRECTORY` selects a pinned author staging directory. `--output FILE` writes a receipt instead of the mutually exclusive exact-type `--expect` comparison. This is a bounded standard-library review CLI, not a maintained general compiler API. Fresh normal and optimized exact-receipt replays from `/` passed against the final author pins above. No repository or frozen predecessor is edited.

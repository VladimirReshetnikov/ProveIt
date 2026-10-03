# Independent review of the marked-word83 obstruction

**PASS: no correction requested.** The frozen [author note](complete86_marked_word_obstruction.md) proves a false ordinary input for the two specific complete84/83 sources. Their cheaper arithmetic is real, but replacing the positive raw slack by a positive marked word loses a necessary upper bound. This review does not exclude other83-operation representations or claim that the changed sources accept every input.

The reviewed author pins are:

| Artifact | SHA-256 |
|---|---|
| Python | `68ce3fe9dd0eff4b70d66047f75048f15dfd49089a3a7221923fc178f3094686` |
| JSON | `fdaa4713693f17560eefc56ce8c19738f682e9e82bde4c4a1ad5af7e98a90e73` |
| Markdown | `86f3a8beb0cf83d2ff239475a9a2981dec6cbd7fb12577584d9ffb2ca5dd8c76` |

The [independent checker](review_complete86_marked_word_obstruction.py) and [receipt](review_complete86_marked_word_obstruction.json) authenticate all three, the author's six predecessor files, and the asymmetric-scale proof used in the canonical forward passage. They read source and JSON bytes without importing any author or historical compiler module.

## Complete source audit

Starting from the actual normalized86 JSON source, I independently reconstructed both saved candidates. The private-consumer checks establish that supplying `C_word` removes exactly the two gates `C_after_alpha` and `marked_rhs`; it does not remove the paid `twice_cell_bits*x`, which still supplies the input Pell index. The remaining shared gap admits the exact rewrite

```
(q-1)*(q-F)+(q-F-Z) = q*(q-F)-Z.
```

Its one additional deletion is valid after checking the actual consumers of `q_minus_FZ`. The full ledgers, including every fixed-numeral product, seven factor multiplications and final subtraction, are:

| Source | M | A | Total | Positive witness ports |
|---|---:|---:|---:|---:|
| Frozen normalized parent |48|38|86|19|
| Supplied marked word |48|36|84|19|
| Supplied word and factored gap |48|35|83|19|

Every gate, ordinary-input port, witness and fixed-numeral port is an ancestor of the output. The witness change is exactly `alpha` to `C_word`; the six program numerals and eighteen other witness names are conserved.

An independent coefficient expansion proves the inverse-coordinate cut

```
alpha=q-F-Z-2d*x-C_word.
```

Together with the gap identity and the literal retained rows, this gives the complete polynomial pullback for both candidates over arbitrary integer or rational assignments. The independent DAG comparison checks83 and82 retained gate values respectively, all eight factors in each circuit, and both entire product-minus-one outputs. The changed intermediate `gap_product` is deliberately excluded from the common-register claim. No equality at unchanged supplied coordinates or unrestricted positive-coordinate inverse is asserted.

## Canonical existence and the input shift

I read the complete author argument, the raw compiler's canonical completeness and width clauses, the half-binomial canonical witness construction, the normalized strong reconstruction, and the positive forward coordinate maps in the asymmetric-scale and first-root notes. The needed provenance is a complete canonical accepted parent certificate, not an arbitrary local Pell solution. Its relevant properties are

```
q=B^N=2^t,  t=dN,  d>=4,  N>0,
e=2d*x+b odd and >=3,  W=2^e<q,
R>=q^2,  R=3 mod4,
X=2^R,  c=psi_A(R),  D=chi_A(R).
```

Normalization can choose its auxiliary witnesses at `m=2cR`, with the additional divisibility `c^2 | psi_A(m)` proved by the binomial expansion in the normalized note. The asymmetric forward map only replaces `w` by `q^2*w`, preserving X and all computed data; the first-root forward map supplies `T=L+g`. Both preserve strict positivity. Thus the obstruction legitimately starts from the actual normalized, asymmetric, first-root source. It does not assume a new soundness theorem for the unsafe child.

The arithmetic source calls the main parameter `a` by `R12`, the modulus H by `a4m5`, and the discriminant Delta by `A`. In the mathematics here, `A=a+2`, `Delta=A^2-1`, and `H=4A-5`; these conventions agree with the literal source.

The proposed shift is

```
x'=x+N, e'=e+2t, W'=q^2 W,
C_word'=Z+W',
zplus'=zplus+(K+X)(q+1)W.
```

The essential strict margin is valid: `e<t` implies `e'<3t<q^2<=R`. The middle inequality follows for every integer `t>=4`, not from the finite fixtures. The exponent e' is still odd. No program numeral, q, packed computation index R, or main parameter changes.

For the shared main/input quotient, set

```
gamma_n=(chi_A(n)-(A-2)psi_A(n)-2^n)/(4A-5).
```

Subtracting the recurrence of `2^n` from the Pell recurrence gives

```
gamma_0=gamma_1=0,
gamma_(n+1)=2A gamma_n-gamma_(n-1)+2^(n-1).
```

This proves integrality for all n. The difference equals
`(2A-2)gamma_n+(gamma_n-gamma_(n-1))+2^(n-1)`, so gamma_2=1 and strict growth from index2 follow by induction. Consequently

```
rho'=gamma_e' > 0,
sigma'=gamma_R-gamma_e' > 0,
rho'+sigma'=gamma_R.
```

The odd-index congruence `psi_A(n)=n mod Delta` follows by induction from `A^2=1 mod Delta`: the even-index residue is `nA` and the odd-index residue is n. Strict Pell growth at odd n>=3 then makes
`delta'=(psi_A(e')-e')/Delta` a strictly positive integer. The new C_word and zplus are positive because their displayed summands are positive on the valid compiler slice.

The independent source dependency audit confirms that the first, auxiliary, index, strong and linear factors use none of the replaced inputs. The main factor depends on the changed rho and sigma only through their unchanged sum. The input factor becomes the exact Pell norm at e'. Finally an independent coefficient expansion verifies

```
(K+X)(Z+q^2 W)+(q-F)
 -[zplus+(K+X)(q+1)W](q-1)
 = (K+X)(Z+W)+(q-F)-zplus(q-1).
```

Thus the complete transport factor is preserved. All eight factors remain one, with all nineteen child witnesses positive. The auxiliary tower is retained unchanged, rather than reconstructed from an unproved new input decoding statement.

## Why this is a false-input theorem

The signed inverse has

```
alpha'=q-F-2Z-2d*x'-q^2 W<0.
```

In particular the construction escapes precisely the old positive raw bound. Fix the valid compiled singleton language `{1}` and take its canonical certificate at1. Its positive width N yields a child zero at `1+N`, outside that singleton, with all fixed program constants unchanged. This is a complete-zero existence argument, not an inference from a negative inverse on an arbitrary off-zero tuple.

The claim is source specific. It neither proves all-input acceptance nor rules out every universal83/84 circuit. The maintained universal86 theorem and source are unchanged.

## Executable evidence and limits

The independent receipt records:

- Both full reconstructed candidate sources and all three complete live ledgers;165 retained-gate,16 factor and2 whole-output DAG identities after independently proved cuts.
- Seven local coefficient identities, including the full transport correction, quotient recurrence algebra, and actual discriminant formula.
- 64 independently generated signed full-source pullbacks, including16 rational cases.
- 1,015 ordinary-input width checks respecting `e=2d*x+b<t`.
- Nine separate Pell/width component cases, using an independent first-order multiplication in `Z[sqrt(Delta)]`;16,146 recurrence/growth steps and8,082 odd-index congruences. These cases satisfy the numerical `R>=q^2` margin and verify the shifted input norm and unchanged main root, but instantiate neither compiler masks nor the full auxiliary tower.

The arbitrary signed and rational checks establish coordinate algebra only. Positivity and the singleton counterexample are proved above using the pinned canonical theorem. Neither the author's four Pell components nor this review's nine components are advertised as materialized full compiler zeros. No historical author suite executes, and the author's research CLI is not treated as a maintained general compiler API.

Replay from any directory with the subject trio beside this reviewer, or give `--subject-root` explicitly:

```sh
python review_complete86_marked_word_obstruction.py --root ROOT \
  --expect review_complete86_marked_word_obstruction.json
```

ROOT is the `native-stream-queue` directory with the authenticated predecessors and its actual `../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`. The additional asymmetric note is authenticated at its current frozen hash. Missing or changed bytes are rejected; no Git fallback or ordinary module import is used. Receipt comparison serializes exact JSON types, and optimized Python is rejected. This is a conventional mathematical and executable review, not a machine-checked formalization.

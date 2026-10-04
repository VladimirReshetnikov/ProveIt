# Independent review of the auxiliary square/product 82 chart

**PASS within the stated candidate scope.** The source is a complete **82=45M+37A** polynomial with 18 strictly positive witnesses and uniform exact degree **185**. Its forward map from the proved 84-operation parent is exact over every commutative ring. The stated conditional projection theorem and the nonsquare extension from actual parent zeros are sound. Ordinary-input soundness remains **UNPROVED**; this review establishes neither an 82-operation universal bound nor a false accepted ordinary input.

The frozen [author source](complete82_auxiliary_square_product_chart.py), [receipt](complete82_auxiliary_square_product_chart.json), and [proof](complete82_auxiliary_square_product_chart.md) have SHA256 pins:

| File | SHA256 |
| --- | --- |
| `.py` | `5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc` |
| `.json` | `7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a` |
| `.md` | `10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9` |

The [independent helper](review_complete82_auxiliary_square_product_chart.py) authenticates all three files, the author receipt's self-source/dependency fields, and every one of its nine immediate predecessor source/proof/data pins. It reads these files as bytes or JSON only. No author verifier, predecessor Python, archived code, or historical suite is executed. Both helpers are scoped standalone CLIs; no broad public compiler API certification is asserted.

## 1. Complete source and full polynomial identities

The new coordinates are `F_aux=L16` and `U_aux=auxiliary_Tf`. The original packing coordinate `F` remains unchanged. Independent reconstruction from the pinned 84 receipt deletes exactly

```
L16 = f*f
auxiliary_Tf = auxiliary_quotient*f
```

and replaces those two free-coordinate names. It matches **every other row in order**, both free/witness interfaces, all fixed numerals, the ordinary input, factor list and final output. The old `f` has exactly these two consumers; old `auxiliary_quotient` has exactly the second. No omitted consumer survives. Every one of the 82 paid rows and all 25 free ports is live. The seven finalizer operations remain paid, giving the 75-operation factor core plus `6M+1A` finalizer.

Exact expression interning proves all 82 retained-register identities after `F_aux=f²,U_aux=T*f`, hence the complete all-ring identity

```
P82(f²,T*f)=P84.
```

Thirty-two additional whole-source evaluations, including sixteen rational assignments, check 2,624 retained values. Positivity makes this a forward map on full positive parent zeros. Its literal positive inverse exists precisely when `F_aux` is a positive square and its positive square root divides `U_aux`; the complete candidate does not enforce those conditions.

Write `Delta=A`, `c=R10a`, `R=r_lhs`, and let `P5` be the product of the five untouched first/main/input/index/transport factors. The actual retained source gives

```
S=i*Delta*c², K=S²,
V=c*(U_aux−1)−R*F_aux,
Na=K*(V²−y_aux²)+y_aux²,
Ns_scaled=Delta*F_aux−K.
```

Independent sparse expansion of the **actual output graph** at these scalar and five factor cuts proves

```
P82 = Delta*(P5*Na*Qs−1),
Qs = F_aux−Delta*i²*c⁴.
```

The expansion has 17 nonzero terms. This is an all-value polynomial identity. It neither assumes that the retained factors are units nor replaces the paid finalizer by an informal conjunction.

## 2. Conditional full-output projection and both signs

Fix the actual outer coordinates, including `i`, in the stated sector

```
Delta>0, c>0 odd, R>0, i>0, Delta*i²*c⁴>1.
```

Only `F_aux,U_aux,y_aux` are then existentially refreshed. The source's positive sizes imply `Delta>=8`; however, the mathematical theorem also works under the explicitly weaker displayed hypotheses. Odd `c` and positive computed `R` are sector restrictions, not assertions about every candidate zero.

At a full zero, cancellation of the nonzero integer `Delta` gives `P5*Na*Qs=1`. All three factors are therefore integer units. As `K=S²` is zero or one modulo four,

```
Na=K*V²−(K−1)*y_aux²
```

is respectively `y_aux²` or `V²` modulo four. It cannot be −1. Consequently `Na=1` and `Qs=P5=epsilon∈{−1,+1}`. The author correctly avoids asserting that every individual retained factor equals +1.

Conversely, given `P5=epsilon`, set `F_aux=Delta*i²*c⁴+epsilon>0`. The sector implies `S=i*Delta*c²>1`. Since `c` is odd, the CRT conditions

```
v ≡ epsilon*R (mod c),   v ≡ 3 (mod 4)
```

have a positive solution. This uses only `gcd(c,4)=1`; no coprimality with a main Pell index is needed. Define the usual positive Pell coordinates at parameter `S` and index `v` by `(chi_S(v),psi_S(v))`, and put `V=chi_S(v)/S`, `y_aux=psi_S(v)`.

For `v=2j+1`, the identity `chi_S(v)=S*Q_j(S²)` has integer coefficients, with

```
Q_0=1, Q_1=4T−3,
Q_(j+2)=(4T−2)Q_(j+1)−Q_j,
Q_j(0)=(-1)^j*(2j+1).
```

Thus division by `S` is an integer-polynomial division. Because `j` is odd and `c` divides `S`, it gives `V≡−v≡−epsilon*R (mod c)`. Also `F_aux≡epsilon (mod c)`. Therefore

```
U_aux=(V+R*F_aux)/c+1
```

is a strictly positive integer. The literal expression for `V` is restored exactly, the Pell norm gives `Na=1`, and `Ns_scaled=epsilon*Delta`. The full output is zero. This proves the stated projection **if and only if `P5∈{−1,+1}`**, for each fixed outer tuple and fixed `i` in the sector.

The independent checker uses a different direct CRT formula and logarithmic Pell-pair powering. It verifies 248 positive extensions covering both signs, odd `c` including one, and several discriminants/indices, plus all 64 residue cases and twenty odd-quotient constant terms. Those tests corroborate the general proof; they do not enumerate the unbounded sector.

## 3. Failure of the literal witness inverse and native-example boundary

At an actual positive parent zero, the **inherited parent theorem** gives the five unchanged factors equal to one, odd `c>1`, positive `R`, and a positive main root `D` with `D²−Delta*c²=1`. These facts must be obtained from the parent theorem, not inferred from the new scaled product alone.

The coordinate `i` has no consumers outside the changed auxiliary/strong block. Set it to one, retain all five-factor data and the ordinary input, then apply Section 2 with `epsilon=+1`. This yields a full positive candidate zero with

```
F_aux=Delta*c⁴+1.
```

It is strictly between `(cD−1)²` and `(cD)²`, since the two positive differences are respectively `c(2D−c)` and `c²−1`; `D>c` follows from the positive main norm and `Delta>1`. Thus it is not a square and cannot be in the literal forward chart image. This is a full-zero failure of the proposed witness inverse at an **already accepted input**. It does not show an unaccepted input becomes accepted or rule out a different existential soundness argument.

I also read the scaled first/main proof and the free-coefficient native-alias proof, including their necessary-mask obstruction. The author's `t=13` example correctly has main index `p=195`, first index `n=182`, abstract target `R=363`, and `gcd(c,p)=195`, which does not divide `R−p=168`. The new sector construction needs no old divisibility condition and can choose auxiliary index 363. This supplies a native subsystem extension, not its missing actual packing/input/transport equations.

Independent binary powering checks its exact first/main norms, positive ratio gaps, positive integral `h`, positive main projection, odd `c`, failed old CRT condition, and nonsquare interval. Its `c` has 40,741 bits and `F_aux` 163,379 bits. The large remaining auxiliary Pell coordinates are not materialized.

For additional scope protection, the checker inserts the exact first/main data into an otherwise fully specified positive assignment for the **actual 82-row source**. At the declared diagnostic numerals the source computes packed `R=61263` and index factor `−60899`, while its first and main factors are both one. The complete polynomial is explicitly nonzero. These numerals are not asserted to be a valid compiler recipe, and this numerical example is not evidence of a false ordinary input.

## 4. Uniform degree from the actual rows

The review derives the degree directly from the emitted source, rather than relying only on the author's modular line diagnostics. All supplied witnesses and the ordinary input have degree one; all six fixed numeral ports have degree zero but remain symbolic in the coefficient ring.

It authenticates the exact main and input producer cones and independently proves the local all-ring cancellation

```
(ac+z)²−(a²+H)c² = z²+2acz−Hc².
```

Use `z=X+gamma*H` for the main factor, and replace `c` by the paid input index and use `z=W+rho*H` for the input factor. These two exact rewrites remove the only problematic naive top-degree cancellations. Every other source row is processed directly using its degree and full leading homogeneous polynomial; any unproved cancellation would cause the checker to fail.

With `Q=Bm1*Jrep`, `k0=eta+zeta`, `gamma0=rho+sigma`, the actual auxiliary argument has degree six and leader `c_top*U_aux`; its other term `R*F_aux` has degree five. The seven exact degrees are

```
22,18,32,58,7,2,46.
```

The independently expanded complete leading homogeneous polynomial has 168 nonzero terms and equals

```
32*Q^111*h*gamma0*delta²*i⁴*k0^13*w^18*s^31
    *(w*(Q−F−Z−alpha−twice_cell_bits*x)−transport_quotient*Q)
    *U_aux².
```

The coefficient of `Jrep^112*h*rho*delta²*i⁴*eta^13*w^18*s^31*transport_quotient*U_aux²` is exactly `−32*Bm1^112`, nonzero on every inherited admissible fixed-program slice. This proves the uniform exact degree 185 without zero-only substitutions. The source's separate naive upper bound 195 is also reproduced. The final subtraction of degree-twelve `Delta` cannot cancel the top form.

## 5. Replay and conclusion

The full author helper and note were read. No edit or mathematical correction was requested. The receipt records the source reconstruction, all-ring identities, uniform symbolic degree proof, bounded positive-sector constructions, and the explicitly nonzero full-source native embedding. It makes the same distinction as the author between a proved arithmetic/conditional projection theorem and unresolved ordinary-input soundness.

From any working directory, after installation:

```sh
python3 review_complete82_auxiliary_square_product_chart.py --root ABS_WIP --expect ABS_REVIEW_JSON
python3 -O review_complete82_auxiliary_square_product_chart.py --root ABS_WIP --expect ABS_REVIEW_JSON
```

Before installation add `--author-root /tmp`. Fresh normal and optimized exact receipt replays from `/` both passed on the unchanged final source and receipt. All checks use explicit exceptions and recursive type-sensitive receipt comparison. No predecessor or repository file is changed.

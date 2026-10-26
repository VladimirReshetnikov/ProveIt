# Native main Pell classification and bootstrap

`NativePellBootstrap.lean` binds its arithmetic directly to the authoritative
old-z literal source `SplitCertificate59.sourceRows`. It uses positive natural
source coordinates, interpreted in the integer source equations. The pinned
source is `1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.

The inner native rank in this module is

```
R = c*j - V = nativeRank x.
```

It is distinct from the outer split116 equation's reduced rank. No outer
reduced-rank lower bound is imported to justify an inner native-rank bound.

## Exact checked interface

The generic `PortBox` retains all coefficient assumptions:

```
beta > 0, K >= 0,
0 <= MC < beta,
0 <= MF_source < 2*beta.
```

Here the ports remain parameters in the order `beta,K,MC,MF_source`.
`MF_source` is already the source port; this theorem applies no additional
shift or doubling to it.

For every positive source zero under this box,
`source_main_index_exact` proves

```
D = chi_(a+2)(R.toNat),
c = psi_(a+2)(R.toNat).
```

The separate theorem `source_native_rank_ge_twentyfour` proves `R >= 24`,
so `R.toNat` agrees exactly with the integer native rank. The bootstrap
`source_bootstrap_of_portBox` also provides a main index `p >= 6`,

```
c > (a+2)*((a+2)^2-1)^2,
2*p < c,  2*R < c.
```

No oddness premise or auxiliary-coordinate positivity restoration is used.

## Proof dependencies

1. Rows 9, 10 and 11 give the main norm at `A=a+2`. Positive `c` excludes
   index zero. Defining rows give `c=eta+k*Y >= 3`; with `A>=3`, the existing
   lemma that `psi_A(p)<=2p` forces `p<=2` proves the strict bound `2p<c`.
   The native index row and `Y>=2` independently give `2R<c`.
2. The first norm is exactly
   `tau^2 - Q*(Q+1)*k^2 = 1`, with `Q=X*Y^2`. The new theorem proves that
   `(2Q+1,2)` is its fundamental positive unit. A second coordinate of
   absolute value one would put a square strictly between `Q^2` and
   `(Q+1)^2`; all other nonzero second coordinates have square at least
   four. Mathlib's fundamental-unit classification then yields
   `tau=chi_(2Q+1)(n)` and `k=2*psi_(2Q+1)(n)`.
3. The OLD-z transport gives
   `(K+w)*(q-F-alpha)=F+(z-1)*(q-1)>0`, hence `q-F-alpha>0` and `q>=3`.
   The target row proves the exact inner rank identity

   ```
   R = ((q-1)*(q-F)+alpha)*(q^2-1) + (MC+MF_source*q)*J.
   ```

   It gives `R>=q*(q^2-1)>=24`. The two strict mask bounds give
   `R<q^4-q^3+q^2-1`, while defining rows give `E=q^4*w*s>=q^4`.
   Consequently `R+1<E`. This step uses the old positive transport
   coordinate; it is not silently transferred to a shifted-z source.
4. The first sequence congruence modulo `E` gives
   `2n = R+1 (mod E)`. The window bound therefore implies `2n>=R+1`.
   Even the weaker `R>=8` suffices for `n>=5`. Upper and lower Pell power
   bounds, together with `2A<2(2Q+1)-1` and `k<c`, force `p>n`, hence
   `p>=6`. Finally `(2A-1)^5>A^5>A*(A^2-1)^2` proves the bootstrap.
5. Rows 15, 18, 19 and 20 give the supplied strong norm exactly; rows 17
   and 21 give the auxiliary norm exactly. `Jones1980.relaxed_aux` and
   the signed `NativePellStepDown.source_index_of_strong` identify `p=R`.
   The proof never cancels the discriminant from the strong norm.

All index, size, and source statements are unbounded theorems. The small
examples in the checks file test the interface; they are not their proof.

## Remaining native calibration work

This closes the positive main classification and its bootstrap for the
parameterized old-z source under the displayed port box. It does not prove
these box inequalities for a named fixed payload, identify a payload's
instruction-tableau semantics, or prove a native source-to-K215 theorem.
Further ordinary compiler steps still include exact first-index recovery,
ratio/binomial extraction, power recovery, and mask/tableau decoding. The
closed baseline `ExplicitZFC` route remains independent of this work.
There is no new claim of an internal object-language ZFC derivation.

# A unit top mask saves one multiplication in the projective compiler

The top mask of the complete product-scale projective compiler can use the existing power `T2` directly. Removing the private multiplication `2*T2` saves **one multiplication**, with all witnesses, six comparisons and the seventeen-operation finalizer retained. The three saved complete sources become:

| Saved fixed-table source | Parent | New full polynomial | Certificate | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| Ten-letter tail-quotient source |244=103M+141A|**243=102M+141A**|226=96M+130A|36|2829|
| Private three-code paths |236=99M+137A|**235=98M+137A**|218=92M+126A|34|1789|
| Shared three-code graph |230=98M+132A|**229=97M+132A**|212=91M+121A|33|1789|

The theorem applies to the canonical nonempty fixed-table product-scale family, including its general weighted-flow version. Here “nonempty” describes the table, not its accepted input relation. These numerical tables are compiler benchmarks, not instantiated universal alphabets. In particular the ten-letter word consists of cancelling inverse pairs, and the three-code fixture leaves its fourth coordinate unchanged; their positive-input endpoint relations are empty. No new numerical universal bound is claimed. The established74/86 bounds are unchanged.

The [source](group_projective_unit_top_mask.py) and [receipt](group_projective_unit_top_mask.json) emit the three complete graphs from pinned JSON without importing or executing any historical builder. The change preserves the projection of the full positive zero set onto the ordinary input and the outer history/controller coordinates. Native witnesses can change; this is neither a same-tuple polynomial identity nor a positive-tuple bijection.

## 1. The one paid source change

In the [tail-quotient source](group_projective_tail_quotient_shift.md), and both [shared-macro sources](group_projective_shared_macro_automaton.md), the actual rows are

```
range_Bminus_shift = range_body_scale * 2
range_M = range_Mbody + range_Bminus_shift.
```

`range_body_scale` is the already computed `T2`. The first row has precisely the second row as its sole consumer. Delete the first row and replace the second by

```
range_M = range_Mbody + range_body_scale.
```

Every other row is unchanged. All powers and fixed-numeral multiplications remain paid, every surviving gate is live, and the supplied free coordinates and all six comparisons are unchanged. There is no arithmetic renaming discount or assumed new primitive.

Use the inherited names `B=16D`, `P`, and `T2=P^a`. Write the lower joined blocks as `H0,M0,Z`, so the scalar interface changes from

```
H = H0+B*T2,   M_old = M0+2*T2,   Q = 2B*T2,   q = 16Q
```

to

```
H = H0+B*T2,   M_new = M0+T2,     Q = 2B*T2,   q = 16Q.
```

The full joined output Z, q, F3, native scale X and all scalar history/controller fields remain unchanged as polynomial expressions. Only the packed native index and its native index factor change among the seven factors. The polynomial itself changes.

## 2. Strict positivity before any power or bit interpretation

At a positive zero the unchanged finalizer first forces all five outer residuals to vanish and all seven integer unit factors to have sign ±1. The literal joint-bound sum, for either sign, gives `P>=12`, `H_i<P` and `Zhat_j-1<P`. The nonnegative edge fields, repunit and retained input/height construction then give `J>=1`, `B<=P` and the original controller/state margin. This stage uses no native exponent or AND interpretation.

Exactly the [product-scale scalar bounds](group_projective_product_radix_scale.md#2-positive-computed-native-fields-before-any-radix-typing) still apply to the unchanged lower blocks:

```
0 <= H0,M0,Z < T2,    B>=16,    T2>=1.
```

The new top coefficient1 is enough. In ordinary integer arithmetic,

```
H-Z >= (B-1)*T2+1 > 0,
M_new-Z >= 1 > 0,
Q-H-M_new+Z >= (B-3)*T2+2 > 0.
```

Thus the actual reconstructed fields

```
F0 = 16(Q-H-M_new+Z)-15,
F1 = 16(H-Z)+4,
F2 = 16(M_new-Z)+2,
F3 = 16Z+8
```

are strictly positive, sum to `q-1`, and retain residues `1,4,2,8` modulo16. In particular each is less than q and `F3>=8`. These inequalities hold before q, B, P or T2 are typed as powers of two. The weaker but still strict margin for F2 is sufficient; the predecessor proof never needs its former extra T2 of margin.

The packed index `r=F0+qF1+q^2F2+q^3F3` therefore satisfies all the same scalar conditions in the [tail bootstrap](group_projective_tail_quotient_shift.md#2-pretyping-bounds-replacing-the-old-x-bound): `r=1 mod16`, `q^3+q^2+q+1<=r<q^4`, and `r<q^3(F3+1)`. With the unchanged `X=q*(w+(q-1)F3)` and `Y=(2*odd_half+1)q`, its proof gives `XY>2r+3` and `Y(X+1)>2r+3` without assuming `X>r`.

Consequently the same native argument handles both index signs, restores all native factors to+1, and excludes the negative index sign by its population contradiction. It also restores the joint bound to+1. No sign or field-typing conclusion has been imported before its hypotheses were recovered.

## 3. Identical outer semantics with fresh native extensions

After native recovery, q is dyadic. The unchanged paid identity `q=32B*P^a` gives dyadic B and P; the repunit gives `P=B^t` for a positive duration t. Now T2 is a power of two and the lower blocks are strictly below it. Binary block separation yields

```
(H0+B*T2) AND (M0+T2)
  = (H0 AND M0) + (B AND 1)*T2.
```

`B=16D` makes `B AND 1=0`. The old top mask similarly has `B AND 2=0`. Therefore the old and new complete AND constraints each reduce to precisely `H0 AND M0=Z`. The physical, controller and range regions are unchanged, so all chronological-flow, source-selection, bounded-history and endpoint conclusions transfer unchanged. In particular no input or height constraint is projected out.

Conversely, keep the ordinary input and outer coordinates of any genuine old positive zero. Their recovered radix and joined AND also satisfy the new top mask, with the positive new fields from Section2. The prescribed native component converse supplies positive auxiliaries for the actual new q and r. The first-root, coupled-unit and tail-quotient coordinate maps give the retained positive native coordinates exactly as in the parent converse; the tail inverse is positive after its exponent recovery. Hence the new complete source has a positive zero with the same outer coordinates. The reverse construction starts from any new zero, uses the old coefficient2, and invokes the same component converse.

This proves equality of the full positive-zero projections to the outer coordinates, not just agreement on finitely many accepted examples. It does not fix the native coordinates: changing the packed index changes the Pell witnesses. A valid unbounded universal alphabet, when instantiated in this compiler, inherits the one-multiplication saving; this packet supplies no numerical instance of that alphabet.

## 4. Full arithmetic effects and exact degrees

Let `T=T2`. Since `M_new=M_old-T`, the exact field and index differences at every supplied tuple are

```
F0_new-F0_old = 16T,
F2_new-F2_old = -16T,
r_new-r_old = 16T*(1-q^2).
```

The literal folded index is checked as a full polynomial in independent H,M,Z,q ports. Accordingly

```
index_unit_new-index_unit_old = 16T*(q^2-1).
```

The other six unit factors, every outer residual and all finalizer rows retain their literal definitions and polynomial values at the same supplied tuple. A shared abstract M port proves every retained downstream expression against its complete parent; it is explicitly a changed-interface proof, not a whole-polynomial equality at the original tuple.

The exact-degree proof from the tail note survives this change. Its uniquely leading F3 expression and q are unchanged; the changed portion of the packed index is lower degree than its leading F3*q^3 term. More strongly, the native index factor's highest term remains `-h*a`, which has higher degree than the packed index. All other factor leaders and the outer square-sum leader are unchanged. Thus every admissible fixed-table slice keeps the parent's exact degree, including2829/1789/1789 for the saved sources.

The helper independently verifies the main norm's full cancellation identity before tightening any degree bound. For all three complete saved graphs, dense univariate substitution with recorded integer weights, expanded modulo1000000007, has a nonzero coefficient at exactly the guarded upper degree. This certifies the actual fixed-numeral degrees without substituting equations that hold only at zeros. The original and modified polynomials are not equated in this argument.

## 5. Evidence and reproduction

The standalone standard-library helper authenticates35 predecessor files. It saves all707 paid live gates across the three new complete sources, proves707 retained-register interfaces, checks the folded index for each old/new pair, and checks72 complete assignments including24 rational assignments. It performs three full dense modular degree expansions,100 scalar pretyping interfaces including nondyadic B/T values, and975 exact dyadic top-block AND checks.

The finite scalar fixtures verify the displayed inequalities and block identities. They are not claimed to be full compiler zeros, accepted computations, or enormous materialized native Pell tuples. The general positive-zero transfer is the proof in Sections2–3, with the pinned native component theorem. The CLI is a bounded research replay tool, not a maintained hostile-input service.

```
python3 group_projective_unit_top_mask.py \
  --root /absolute/path/to/native-stream-queue \
  --expect /absolute/path/to/group_projective_unit_top_mask.json
```

Use `--output` to write its deterministic receipt. Historical sources, receipts and notes remain unchanged.

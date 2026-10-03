# Independent review of the finite coded Tree lookup scout

**PASS.** The frozen [author source](eager_tree_coded_lookup_scout.py), [receipt](eager_tree_coded_lookup_scout.json), and corrected [proof note](eager_tree_coded_lookup_scout.md) support the claimed same-coordinate natural-zero equivalence and complete costs. At external `N=8`, the degree-10 source costs **1172=445M+727A** and the hybrid degree-12 source costs **1156=445M+711A**, both with188 natural witnesses and91 residuals. Neither is a fixed-arity universal bound or an ordinary-input recoder.

The independent [checker](review_eager_tree_coded_lookup_scout.py) and [receipt](review_eager_tree_coded_lookup_scout.json) authenticate all six author/constructor-parent artifacts. The audited author source is `b2769ca2c8b8754f5b5c9d65c0ad97a5f590c5b6ebc5712a2964ac1d1a1d0e73`; receipt `acfcbd04609e49150a0e9089c7937ca0fcd20b852a337a3e39248a4e582d01c6`; final companion note `81d9be0663b212039802c1c841dd200e82baedc02ecf1005957e8f90beef457b`. No arithmetic changes were requested. One wording correction was made before this freeze: the reused `e` product survives through the retained `t1*(z−F(a,y))` output residual, not through the constructor-defining equation already deleted by the parent projection.

## Natural-zero proof

The code `P(u,v)=(u+v)^2+u` is injective on natural pairs. For `s=u+v`, its value lies in `[s²,s²+s]`, strictly below `(s+1)²`; therefore `s=floor(sqrt(P))`, `u=P−s²`, and `v=s−u`. The zero code has exactly the zero pair as its preimage. Nesting in any of the six coordinate orders gives an injective, zero-preserving triple code.

The actual retained source equations are the natural tag sum `sum(t0,...,t4)=1` and the pointer sums `t3+t4,t3+t4,t3`. The independent checker expands and verifies those literal equations. Thus tags are one-hot; each natural pointer slot is either entirely zero or selects exactly one row. In an inactive slot all original weighted targets and all new target codes vanish. In an active slot, the pointer selects a natural row triple and the tags select precisely one target triple. Equality of their codes is equivalent to the three original coordinate equalities.

The gated, weighted, and hybrid target formulas agree on the three permissible `(t3,t4)` charts `(0,0),(1,0),(0,1)`. Their full polynomials need not agree off those charts. Common retained equations are forced first by either complete SOS zero, so the implication does not assume the desired lookup equations or an already-typed history. The last row, which has no forward pointer coordinates, is covered by the same argument. No reachability, minimality or nonzero external-input premise is added.

It follows that the entire natural zero tuple sets agree at each supplied external N, with every scalar coordinate unchanged. The proof is not a signed or real-zero theorem: `P(-1,0)=P(0,0)` and `P(7/16,5/16)=P(0,1)` already show that natural injectivity does not extend to those domains. These local examples are not asserted to be complete Tree-certificate counterexamples.

## Full source, arithmetic and degree audit

The review calls the authenticated public builder solely to obtain actual complete emitted schedules. It does not call the author's `verify`, polynomial-expansion or arithmetic-evaluation helpers. Independent coefficient dictionaries reconstruct the original nine lookup rows, all new row and target codes, and every new coded residual directly from the displayed field formulas. Each retained parent gate is checked literally before its independently computed polynomial is reused.

The exact source checks cover all416 declared recipes, including all19 saved full packets. Their recipe keys are required to be distinct and to equal an independently generated set of384 gated,16 weighted and16 hybrid choices. They establish:

- 261,736 paid live gates,117,120 retained literal rows and16,224 retained residual identities;
- 648 independently reconstructed old lookup rows across the16 saved parent forms;
- 5,616 full new lookup polynomials and5,616 target-code identities, including actual metadata ports and removed-row maps;
- 416 complete SOS identities at abstract residual cuts,416 exact degree checks, and the complete paid M/A ledgers.

The list above counts recipes, not distinct polynomials. The review does not claim to enumerate every additional option combination accepted by the prototype or every possible arithmetic schedule.

Both complete finalizers are checked to square each residual once and sum those squares with exactly one fewer addition. With the unchanged residuals identified literally, this proves the all-value correction

```
F_new−F_parent = sum(new coded residuals²)−sum(removed field residuals²).
```

This is a complete polynomial relation over any commutative ring; it is not polynomial equality. The receipt includes a full natural off-zero assignment where the outputs differ. An additional76 complete numerical corrections across all19 saved packets include19 nonnegative integer,38 signed integer and19 rational assignments. These support the coefficient proof rather than replace it.

The paid pairing reuse is checked through the actual constructor product `p=(a+y)(a+y+1)`: `P(a,y)=p−y` and `P(y,a)=p−a`. All parent prerequisites remain charged. Row0's unused code is omitted because no strictly forward pointer can target it. There is no free decoder, hidden lookup oracle or omitted repeated computation. The source's optional syntactic sharing applies only to new code gates; this is preserved in the complete count.

For the two headline schedules, with `c` the Boolean parent-cleanup choice, the actual counts match

```
M = (3N²+87N+2)/2,
A_gated = 3N²+(67−c)N+7,
A_hybrid = A_gated−2N.
```

The corresponding witness and residual counts are `(3N²+23N)/2` and `11N+3`. The equations include N=1 and2, so empty forward sums and the root-code omission introduce no exceptional missing gate. At N=8, the finalizer alone costs91M+90A; the gated certificate source costs354M+637A and the hybrid source354M+621A. Their comparison baseline is the complete, matching-cleanup constructor parent at1456 operations.

Exact degree is verified from the actual residual coefficients, not just a syntactic upper estimate. For gated sources, the retained constructor residual already has a nonzero degree-five part `−t4(a+b)^4`, and all new residuals have degree at most five. Hybrid slot0 has degree-six leading part `−[t3(b+y)^2+t4(a+y)^2]^2`. Weighted targets have a nonzero degree-eight part. Squaring and summing nonzero real homogeneous leading forms cannot cancel, giving exact degrees10,12 and16 respectively. This formal degree calculation does not substitute tag or pointer equations valid only on zeros.

## Interfaces, limits and replay

The public prototype implements exact N=1,...,8, exact Boolean options and canonical packets. The independent checks include68 malformed-call or packet rejections, four defensive-copy tests, three changed-parent-byte rejections after a successful build, and optimized-Python rejection. No shared imported parent module or bytecode cache is used: the author reads pinned complete JSON packets. The independent reviewer executes the author source directly from its authenticated bytes.

The general injectivity/one-hot proof applies to the stated uniform external-N template; the concrete API and census remain bounded as documented. Composing the zero-tuple result with constructor restoration preserves the triangular parent's full natural zero fibers. Earlier unrestricted-flow normalization still preserves represented triples rather than all original witness fibers. The previous parent theorem is inherited from its frozen reviewed artifacts; no historical author suite is rerun here.

The checker uses only the standard library. With the three constructor-parent files in ROOT and the coded author trio in ARTIFACTS:

```sh
python3 review_eager_tree_coded_lookup_scout.py \
  --root ROOT --artifacts ARTIFACTS \
  --expect review_eager_tree_coded_lookup_scout.json
```

Both arguments may name the same installed WIP directory. `--output FILE` writes a new deterministic receipt. The final writer and an independent fresh `--expect` run from `/` passed. No repository or Git mutation was made during this review.

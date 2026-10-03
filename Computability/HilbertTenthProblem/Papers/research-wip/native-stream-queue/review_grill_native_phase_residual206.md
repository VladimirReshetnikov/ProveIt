# Independent review of native Grill phase-residual compression

**PASS; no correction requested.** The complete strong-cone `011` unit source drops from 209 to **206 = 93M + 113A**, and its raw source from 233 to **230 = 99M + 131A**. The new and parent polynomials are identical on every supplied tuple within each finalizer mode. All input coordinates, native equations, positive-domain hypotheses, and witness sets are retained. This is distinct from the separately reviewed weak-cone208 compiler, whose input-coordinate interpretation changes.

Reviewed author pins:

- [Source](grill_tag_native_phase_residual206.py): `b9eaa5edf08f355607adf496d9477b806960c3438a81099f64cf08d0b7471af1`.
- [Receipt](grill_tag_native_phase_residual206.json): `bc58e688fd9f47e2a6ad2414084d68cc4f4118c0234a7f72f949b2524e995908`.
- [Complete note](grill_tag_native_phase_residual206.md), version proofread: `cb5581c2e741ed78e43cc053e96021780c2d2f71b37e95c561b4723ff7ff44b1`. A later provenance-only appendix can change the note hash.
- [Strong phase-sharing parent](grill_tag_native_phase_sharing.py): `760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069`.

The [independent checker](review_grill_native_phase_residual206.py) and [saved receipt](review_grill_native_phase_residual206.json) authenticate and separately load both sources from their bytes. This review covers the complete child source and proof note, the eight published schedules, six additional symbolic schedules, current/historical metadata separation, exact public types and cache boundaries. It does not rerun unchanged historical author suites or materialize large native Pell witnesses.

## Independent algebra and complete-source proof

Write `S_p=Shat[2p]+Shat[2p+1]−2`. The independent checker expands the actual source definitions

\[
 J=\sum_{p=0}^{m-1}S_p,\qquad P=(B-1)J+1,
 \qquad T=\sum_{p=1}^{m-1}(m-p)S_p.
\]

It derives its own coefficient dictionary for

\[
 r=mS_0-(B-1)T+q_0-J-m
  =m(\widehat S_0+\widehat S_1)-(B-1)T+q_0-J-3m.
\]

The old source residual `B*Next+q0−Q−m*P` and the new source residual each expand to exactly that dictionary in **all original selector hats, `B`, and `q0`**. Neither `J` nor `P` is an independent proof atom. In particular, for `m=1` the resulting dictionary is exactly `q0−1`, with all selector and radix terms canceled. No zero, integrality, range or Boolean condition is used in this algebraic identity.

This local calculation alone would not justify arbitrary changes elsewhere. The independent checker therefore separately proves that the derived `B` expression is unchanged, and then compares the entire old and new expression DAGs with a cut only at the proved phase residual. It verifies every other comparison's actual two operands, every native unit factor, every retained semantic interface, and the complete final output. The literal finalizer instruction sequence changes only the operands of that one residual subtraction; its remaining instructions are identical.

Thus, separately for each mode,

\[
 F_{\mathrm{child}}(v)=F_{\mathrm{parent}}(v)
\]

as a polynomial in every supplied coordinate over any commutative ring. The phase comparison operands themselves need not agree; their difference does. The identity on coordinates is consequently a bijection of the full zero sets within each mode, including the intended positive-integer domain. This is not an assertion that the raw and native-unit polynomials equal one another.

The source still literally computes `P0=3*x+Z0`. All selector, phase, ordinary-input, range, scale, native factor and projection structures are unchanged. Their previous positive-domain and unbounded-duration interpretation therefore transfers directly by exact polynomial equality. This review introduces no new universality or decoder claim.

## Actual paid ledgers and public source contract

The independent audit checks topological exact-integer operands, unique gate names, complete free-coordinate closure, absence of dead paid gates, certificate/finalizer separation, both certificate and complete gate counts, exact arity and residual counts, and formal degree propagation.

| Program | Raw full cost | Unit full cost | Raw witnesses / rows | Unit witnesses / rows |
|---|---:|---:|---:|---:|
| `(0,)` | 83M + 106A = 189 | 77M + 88A = 165 | 32 / 20 | 26 / 11 |
| `(1,)` | 85M + 107A = 192 | 79M + 89A = 168 | 32 / 20 | 26 / 11 |
| `(0,1,1)` | 99M + 131A = 230 | 93M + 113A = 206 | 37 / 20 | 31 / 11 |
| `(2,0,1)` | 105M + 133A = 238 | 99M + 115A = 214 | 38 / 20 | 32 / 11 |

Each published form saves exactly **1M+2A**, including the `m=1` cases. For `011`, the measured source replacement removes eleven old certificate gates and adds eight new ones. The complete finalizer remains paid. Multiplications by nonunit constants are charged.

The checker also instantiates `(0,1)`, `(2,0,1,0)`, and `(0,1,0,1,0)` in both modes, adding six exact local/full-DAG proofs and paid ledgers at periods 2, 4 and 5. These also save three operations in the measured sources; no unrestricted optimality or universal-program statement follows. The symbolic derivation itself is valid for every `m>=1`, while the builder verifies its guarded source transformation for each actual instance and can retain a non-improving parent.

The formal degree upper bounds remain 304,304,484,520 for the table's raw forms and 737,737,1187,1277 for the unit forms. Exact degree remains unclaimed. Actual polynomial degree is preserved by the identity, but this packet does not establish its value.

The old `Q`, `Next`, `phase_lhs` and `phase_rhs` ports are not live public interfaces after the rewrite. Their formulas and parent register names are explicitly historical under `proof_only_phase_formulas`. Current ports name only the new residual's left and right operands. The previous phase-sharing proof is under `historical_phase_sharing`. The independent recursive metadata scan finds no removed register advertised in current metadata. The strong cone remains explicit, and the global same-coordinate identity flag is accurate.

## Reproducible independent evidence

The frozen checker and fresh saved-receipt replay pass:

- 14 independent sparse expansions of the complete phase residual, 14 whole-polynomial DAG proofs, 203 nonphase residual-DAG comparisons, and 28 native unit-factor comparisons.
- 14 complete ledgers, formal upper-degree and metadata audits: eight published forms plus six additional period-2/4/5 forms.
- 128 complete integer polynomial identities, including 64 signed cases, with 1,984 residual identities; 16 independent exact rational output identities.
- 758 malformed-call rejections, including complete packet mutations, exact type substitutions, wrong coordinate domains and noncanonical parent packets; 32 independent defensive-copy checks.
- A cold fake-parent-module regression preserving the caller's exact module object, and a private warm parent-source mutation rejection followed by unchanged restoration.

The code's authenticated-byte loader and warm dependency guards were read. The finite guard checks are deliberately bounded; the unchanged inherited dependency chain is not comprehensively reaudited here. The public transformations accept canonical complete parent packets, reject typed lookalikes, and retain full-input guards on cached calls.

Replay:

```
/path/to/research-python review_grill_native_phase_residual206.py \
  --source /path/to/grill_tag_native_phase_residual206.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/review_grill_native_phase_residual206.json
```

The helper is standalone except for the pinned source/compiler dependencies it reviews; it does not import another review helper. Its receipt contains no absolute workspace paths or timing fields. All review outputs and source-mutation fixtures were confined to temporary files; no repository or Git mutation was performed.

## Root integration check

The root agent read the implementation, algebraic derivation and independent
review. Both frozen author and independent checkers were replayed against the
repository dependencies; both receipts reproduced byte for byte. The phase
residual identity was also checked directly by substituting the actual J and P
formulas. The strong input cone and the same-coordinate whole-polynomial claim
remain distinct from the weak-cone language equivalence.

# Only direct coefficient cancellation remains at the nine-gate auxiliary frontier

For the paid auxiliary interface

    V=cTf−c−Rf²,  Q=Delta²*i²*c⁴,  S=Delta*f²−Q,

**sixteen of the seventeen necessary cancellation pivots are impossible in a five-multiplication circuit.** The only unexcluded pivot is a cancellation that produces **Q itself**, up to a nonzero rational scalar.

Together with the frozen nine-gate frontier, any circuit using at most nine arithmetic gates must therefore have exactly **5M+4A**, and its unique useful monomial-valued addition must output Q. This is a necessary condition, not an existence result or an exclusion of every nine-gate circuit. The complete 84-gate upper bound is unchanged.

## 1. Exact model and inherited premises

The independent variables are Delta,c,i,f,T,R. The additional paid ports are exactly c² and Delta*c². Constants and scalar multiples may be free in the lower-bound relaxation. A product of two nonconstant expressions counts as one multiplication; arbitrary scalar linear combinations are free only when proving a multiplication-count contradiction.

The frozen [nine-gate frontier](complete84_auxiliary_nine_gate_frontier.md) proves that every at-most-nine-gate circuit has 5M+4A, has a unique useful monomial-valued addition U, and has U on a path to Q. All operations on this path after U are monomial products, apart from free scalar aliases. The possible U, up to nonzero scalar, are

    Delta^a*c^b*i²  (0<=a<=2, 0<=b<=4),
    Delta*c²*i,  Delta²*c⁴*i.

The [mixed-cut proof](complete84_auxiliary_mixed_cut.md) proves that the joint outputs

    V=cTf−c−Rf²,  W=Delta*f²

need at least four multiplications from the original paid ports, even with arbitrary linear combinations free. Its proof specializes Delta=i=0, deletes one product using W's nontrivial linear relation, and invokes V's three-product lower bound with paid c². The present argument uses this established four-product statement; it does **not** strengthen it to five.

No new paid powers of c, no free pivot U, no valid-compiler coefficient relations, and no zero-set identities are introduced. The proof permits arbitrary chronological interleaving, multiplicative depth and nonhomogeneous cancellation.

## 2. A chronological specialization lemma

List a circuit's nonconstant multiplication outputs in chronological order as g1,...,gm. Before any given point, every available expression belongs to the scalar linear span of the original paid ports and the earlier multiplication outputs. This follows by induction: additions preserve this span, while each multiplication introduces precisely its own new output.

Suppose a produced expression U lies outside the original paid linear span, and suppose a specialization sends U to zero. Its linear representation before it is produced has the form

    U = A + beta1*g1 + ... + beta_r*g_r,

where A belongs to the original paid span and at least one beta_j is a nonzero rational scalar. The coefficients are scalars, not variable-dependent expressions. Let j be the largest index with beta_j nonzero. After specialization,

    g_j = −(A + sum_{k<j} beta_k*g_k)/beta_j.          (1)

Thus its multiplication can be deleted and every later use replaced by the displayed linear combination of specialized paid ports and earlier product outputs. This is allowed in the multiplication-only relaxation. Only division by a nonzero fixed rational occurs; no variable division is used. All computations needed to obtain U remain charged except the explicitly eliminated multiplication.

Now suppose a **later multiplication output** g_t, with t>r, also specializes to zero. Delete that gate first and replace its uses by zero. Since it was not present before U, it cannot occur in U's relation. Equation (1) then deletes a second, distinct multiplication. The remaining specialized outputs are computed with at most m−2 products.

This argument requires neither multiplication output to have been identically zero before specialization. The earlier product need not itself be monomial. It is also harmless if further products become scalar or zero: that only reduces the remaining count.

## 3. Apply the lemma to every proper pivot

Each of the seventeen U monomials has positive i exponent and is different from every original paid monomial. Distinct monomials are linearly independent over the rationals, so U is outside the original paid linear span. At i=0 it vanishes. The first deletion in Section2 therefore applies to the computation before the pivot addition.

Assume U is a **proper** monomial divisor of Q. Its path to Q must contain a later nonconstant multiplication. The frontier's one-i-product constraint makes the last restoration explicitly one of

    Q = U*H,  Q = U²,  or Q = U*i,

up to nonzero scalar, with H a nonconstant i-free monomial. More generally, following free scalar aliases back from the final Q wire reaches a genuine later multiplication output proportional to Q. Because U is proper, Q cannot be just a scalar alias of U. No second monomial-valued addition is available in this budget.

That later multiplication specializes to zero at i=0 and is outside the earlier U relation by chronology. Delete it, and then delete the earlier product pivot using (1). The original output V is unchanged by the specialization, while S specializes to W=Delta*f². Consequently the remaining circuit computes V,W from exactly the specialized original paid ports with at most

    5−2 = 3 multiplications.

This contradicts the inherited four-product lower bound. **Every proper U is therefore excluded.**

The deletion does not assume the old coefficient construction or the old final subtraction for S. It preserves all other downstream consumers by exact identities on the specialization. In particular, the earlier pivot's computation is not made free, and a c³ or c⁴ value obtained there is not added to the paid interface.

## 4. The seventeen-to-one census and its limit

| Pivot family | Count | Outcome |
|---|---:|---|
| Delta^a*c^b*i², except (a,b)=(2,4) | 14 | Proper pivot: two deletions, contradiction |
| Delta*c²*i | 1 | Q=U²: two deletions, contradiction |
| Delta²*c⁴*i | 1 | Q=U*i: two deletions, contradiction |
| Delta²*c⁴*i²=Q | 1 | No mandatory later multiplication; not excluded |

For U=Q, the specialization still supplies one nontrivial product relation. It need not supply a separate later zero multiplication. The surviving count is then four, consistent with the known joint V,W lower bound. The proof must stop there.

The new result changes the useful search target: a possible 5M+4A improvement must form Q **directly as the unique cancellation addition**, while also producing V and S. It cannot first recover a smaller monomial and then multiply or square it into Q. No unrestricted four-product impossibility for V,W, no depth-two reduction of arbitrary circuits, and no full nine-gate impossibility are asserted.

## 5. Finite evidence and unchanged complete source

The [fresh helper](complete84_auxiliary_proper_pivot_exclusion.py) reads nine pinned predecessor files only as inert text/JSON. It independently enumerates all thirty positive-i divisors of Q, recovers the seventeen frontier shapes, checks that every pivot is outside the original paid monomial span and vanishes at i=0, and verifies that precisely sixteen require a genuine later nonconstant restoration product. The unbounded chronological deletion lemma is proved in Sections2–3; these finite checks are not a formal verification of arbitrary circuits or a bounded numerical rejection search.

The [receipt](complete84_auxiliary_proper_pivot_exclusion.json) also retains both complete original and attaining mixed 84-row arrays from the frozen frontier. It reconstructs the five-row V splice, independently expands V,W,Q,S in the six-variable integer polynomial ring, checks every unchanged row and the external V,Q,S consumer boundary, and checks full topology/liveness. Both arrays remain **84=47M+37A**, with all 25 supplied ports and the same 18 positive witnesses. The attaining mixed local cut remains 7M+3A. Its full polynomial identity, positive zeros and degree187 are unchanged because the proved local outputs and all surrounding consumers are unchanged. There is no new lower-count source or accepting fixture.

| Inert dependency | SHA-256 |
|---|---|
| `complete84_auxiliary_nine_gate_frontier.py` | `e4197911e04fe9379fb0801ce01559ec371e3955d025486a3f84644aa17d48e2` |
| `complete84_auxiliary_nine_gate_frontier.json` | `049de5ef5f2d46802801b6f88450a852b672b218040e224c262a2ac1e79341e1` |
| `complete84_auxiliary_nine_gate_frontier.md` | `ae4925e8bf330fcd1a5d1c0f529e982f0c5df018690a7ef81e4ca27cc5ad4cd2` |
| `complete84_auxiliary_mixed_cut.py` | `a77f326d98550ed21643d5f1ea2aa25d9dca7d9a7fdca26c40e8bf1cdf80c13a` |
| `complete84_auxiliary_mixed_cut.json` | `1aa60da5b6b7278efdfd8535d10ec8f9af604b729b1f95c124eca714721dfc47` |
| `complete84_auxiliary_mixed_cut.md` | `b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2` |
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |

```sh
pivot_wip=/absolute/path/to/native-stream-queue
python3 "$pivot_wip/complete84_auxiliary_proper_pivot_exclusion.py" \
  --root "$pivot_wip" --expect "$pivot_wip/complete84_auxiliary_proper_pivot_exclusion.json"
python3 -O "$pivot_wip/complete84_auxiliary_proper_pivot_exclusion.py" \
  --root "$pivot_wip" --expect "$pivot_wip/complete84_auxiliary_proper_pivot_exclusion.json"
```

Generation uses `--output`; replay uses mutually exclusive `--expect`. Duplicate/nonfinite JSON is rejected, receipt equality is recursive and type-exact, and explicit guards remain active under optimized Python. No frozen predecessor is executed or imported, and no repository file is modified.

Fresh generation and fresh normal and `-O` exact receipt replays from `/` pass.

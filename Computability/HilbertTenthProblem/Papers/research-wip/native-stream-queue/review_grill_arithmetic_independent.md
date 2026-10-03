# Independent bounded review of the Grill encoding and arithmetic scout

**PASS; no requested correction.** This review covers the frozen encoding discrepancy packet and the complete externally bounded Grill arithmetic circuits. It does not audit the full Genera-to-Grill universal compiler, the special halt-symbol protocol, a universal ordinary-input decoder, or a fixed-arity unbounded history encoding.

Reviewed source pins:

- `review_grill_encoding_e.py`: `66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3`.
- `grill_tag_affine_scout.py`: `2f3a1b2525e82ea935d27480dd77750254cfd31236092a7a063e78708379fa81`.
- Arithmetic author receipt: `9fb0f2007a676a9ba3a89983a7106e7d9ba555404fba89afd15823411e96cf67`.
- Arithmetic companion note: `0e3e862aee6df22b2d529d0cee02d439ad9146fb4f27a18c0de14d406398741b`.

## Proof and scope

A Boolean head gives `P_next=P/2` or `P_next=4^n P`. For positive integer widths, the odd part is invariant; terminal `P_t=1` therefore forces every width to be dyadic. The second residual implies `2(P_next-Z_next) ≡ P-Z (mod 3)`, so terminal `(1,1)` also forces every content congruence. Neither assertion relies on an uncharged power predicate. An isolated local zero does not imply dyadic width.

For ordinary positive input, `P_0=3x+Z_0` with positive `Z_0` supplies the missing initial code bound: `0<x<P_0/3`. On a nonempty dyadic code, the content equation modulo two forces the correct head bit. Both branches preserve the positive code cone; an empty code `(1,1)` has no integer successor because its content numerator is odd for either head. Thus the complete ordinary-input zero is a genuine first-halting padded-binary execution. This represents existential choice of the initial padding width, not a proved universal decoder or a claim that padding is semantically irrelevant.

The aggregate equation has the correct weights. For each prefix `A_k=Z_0+Σ_(i<k) 2^i d_i(P_i+3)`, the terminal equality implies `2^k | A_k` by subtraction of its divisible suffix. Its summands are nonnegative and its initial term is positive. Consequently the omitted `Z_k=A_k/2^k` are uniquely positive integers. Consecutive prefix differences give every original content equation. Projection and this restoration are mutual inverses on complete positive zeros, including the one-step boundary where no intermediate content field exists. No off-zero identity between the two different history finalizers is claimed.

For every integer head, `B=d(d-1)>=0`. Replacing `B^2` by `B` therefore preserves the complete integer zero set; the full off-zero correction is exactly `Σ(B^2-B)`. This is separate from the coordinate-change correction `E_Z=E_P-3E_X`. The source and note keep the two arguments distinct.

With `z(t)` zero-exponent phases, independently counted complete ordinary sources give:

| Mode | M | A | Total | Positive witnesses | Residuals |
|---|---:|---:|---:|---:|---:|
| Full history | `6t+1-z(t)` | `12t-2` | `18t-1-z(t)` | `3t-1` | `3t` |
| Aggregate | `6t+1-z(t)` | `9t+1` | `15t+2-z(t)` | `2t` | `2t+1` |

All input arithmetic and the complete finalizer are counted. The squared-Boolean reference adds exactly `t` multiplications. Constant-only operations and neutral multiplications are folded; every emitted gate is live. A nonzero quadratic width residual supplies a positive quartic leading square; other quadratic residual squares cannot cancel it, and the direct Boolean terms have degree two. The exact quartic claim is sound. The horizon and program numerals are external constants throughout.

## Independent evidence

The accompanying helper pins both reviewed source byte strings before compiling those exact bytes. It uses its own sparse polynomial arithmetic, manual residual formulas and complete finalizer reconstruction; it does not call the author's evaluator to establish symbolic identities. Across six programs, horizons 1–8, four source shapes and both Boolean finalizers, it checks **384 literal complete polynomial identities, 4,848 residual identities, 384 exact quartic degrees and all corresponding ledgers, source closure and liveness**.

An independent backward enumeration of **12,276 Boolean histories** at horizons 1–10 produces 842 positive raw terminal histories, all dyadic and congruent as proved. Of these, **193** have positive ordinary input. Each of those passes both full circuits, exact projection/restoration and an independently implemented string execution with no early empty queue. Eight invalid compiler-parameter forms reject. The arithmetic author's complete saved-receipt replay also passes.

Two explicit negative-scope fixtures clarify the hypotheses, without finding a defect in the stated claims:

1. With `program=(0)`, `t=1`, `x=Z_0=1/3` and `D_0=3/2`, the projected unsquared polynomial is zero, but the all-squared polynomial is `5/16`. All supplied coordinates are positive reals. Integer nonnegativity of the Boolean factor is essential.
2. The raw positive history for `program=(1,0,0,0,0)` and heads `(1,1,0,0,0)` has states `(2,5),(8,5),(8,8),(4,4),(2,2),(1,1)`. It satisfies the full raw source but has initial content `X=-1`. Terminal dyadic width and congruence alone do not force `Z<=P`. The ordinary relation `P_0=3x+Z_0`, `x>0`, excludes it exactly as required.

## Encoding packet and primary text

The [current creator Grill page](https://esolangs.org/wiki/Grill_Tag) identifies revision 181950 and independently confirms the literal discrepancy: the verbal second grill count is `a-2`, while its displayed component width and inverse run formulas require `a-4`. The additional four bits change phase, so this is a substantive encoding-description error. The [creator discussion](https://esolangs.org/wiki/Talk:Grill_Tag), identifying revision 181840, separately confirms the repaired `01` orientation of microcommand `11`. The [Genera page](https://esolangs.org/wiki/Genera_Tag) specifies position-dependent productions and widths, consistent with the finite fragment transcribed in root's checker.

I read all of root's checker and note, compared the literal run formulas with the primary page, and reran its 10,240 two-generation fixtures. All 20,480 corrected word identities and phase identities pass; all stated uncorrected discrepancies reproduce. The assertions are restricted to two nonhalting symbols and the stated finite inputs. Root's receipt and narrative accurately distinguish this evidence from a proof of the complete universal source.

## Reproduction

From a directory containing the two reviewed helpers and this independent helper:

```sh
python review_grill_arithmetic_independent.py \
  --scout grill_tag_affine_scout.py \
  --encoding review_grill_encoding_e.py \
  --expect review_grill_arithmetic_independent.json
```

Paths may be supplied explicitly; there is no permanent `/tmp` dependency. The helper performs no downloads or repository writes. `--output` is required to write a new receipt. It is a bounded reviewer of generated canonical source forms, not a general supplied-packet validation layer.

Root read the frozen arithmetic implementation and proof, then replayed both
the author suite and this independent checker from the maintained directory.
Both fresh receipts match the committed receipts byte for byte.

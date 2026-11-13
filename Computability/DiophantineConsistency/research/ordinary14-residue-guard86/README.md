# A proposed 86-operation residue-guard form

This packet proposes a **14-positive-input, 86-operation, degree-26** equation whose positive-zero existence is equivalent to the reviewed shifted-guard 87/26 graph at the authenticated compact44 ports, conditional on its reviewed standard-integer decoder. It is submitted for independent review. It does not claim a new Lean/iPRA theorem, a PDF/file-semantics binding, a fresh provider replay, or a global minimum.

The [literal candidate](candidate.json) differs from the 87 graph only in the transport guard. With `b=J*beta`, `q=b+1`, `C=q−F−alpha`, and K the fixed K0 port, replace

```
old guard = C*(X+K*q)−F−b*omega
new guard = C*(X+K)  −F−b*h.
```

The 14th input is now the positive integer h. The source deletes the sole `K*q` gate and feeds K directly to the existing addition; all four original residuals and the first-root coordinate sigma-prime are unchanged. The exact integer-polynomial identity

```
old_guard(omega=h+C*K) = new_guard
```

holds for every integer valuation. In particular, all five squared residuals and the complete outputs agree under that coordinate substitution. This equality alone does **not** assert that the inverse maps all positive tuples to positive tuples.

## Positive-zero existence maps

For a positive new zero with `beta>0` and `K>=0`, the new guard says `C*(X+K)=F+b*h>0`. Since `X+K>0`, C is a positive integer. Set `omega=h+C*K>0` and retain the other thirteen inputs. The old guard and all other residuals vanish by the displayed identity, giving a positive 87 zero. This direction is valid for any such integer ports, not only compact44.

Conversely, at the authenticated compact44 ports, a positive 87 zero has C>0 from its guard and hence `F≤q−2`. The independently reviewed external decoder in `../ordinary14-shifted-guard87-calibration/` derives `X=2^R≥q²` from that zero using the cited rank, Pell-index and projection source statements; it does not assume the old Bt sign. Its hypotheses and provider/file-binding limitations are inherited here. Put

```
h = omega−C*K = (C*(X+K)−F)/b.
```

The old guard proves this is an integer. Its numerator is positive because `C≥1`, `K≥0`, `X≥q²`, and `F≤q−2`; therefore `h>0`. Retaining the other inputs and applying the same exact identity gives a positive 86 zero. These two maps establish standard-natural positive-zero **existence** equivalence under the cited compact44 decoder assumptions; the reverse map is not claimed for arbitrary positive valuations or arbitrary ports. A full modified-graph model bridge and the parent endpoint remain separate work.

## Count and degree

The checker pins the 87 source graph and decoder review, verifies that `K*q` has exactly one consumer, reconstructs the full row delta, checks topology and liveness, and verifies the guard identity in an exact sparse polynomial ring. It checks signed-integer graph controls, a positive scalar guard control and the four P72/P115 port payloads. All 86 gates, 14 inputs and four fixed leaves are live; the breakdown is 46 multiplications, 23 additions and 17 subtractions.

The four retained residuals have degree at most 13 by the reviewed 87/26 cancellation argument; the new guard has degree at most 2 and its square at most 4. Thus the full output has degree at most 26. The whole graph evaluated at all witnesses t and the authenticated actual port bytes modulo 1,000,000,007 has degree 26 with leading coefficient **85432412**, so its specialized integer degree is exactly 26. This is external graph and polynomial evidence, not a Lean `totalDegree` theorem.

The checker does not prove the cited unbounded decoder or the positive-coordinate argument by finite testing. Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-residue-guard86/check.py > /tmp/ordinary14-residue-guard86.json
cmp /tmp/ordinary14-residue-guard86.json research/ordinary14-residue-guard86/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-residue-guard86-independent/`.

# Source-only explicit Pell-period specialization

The requested `h=2*m*c` matrix-divisibility step is already covered by the represented-Pell source theorem `ArithmeticPellSquaredSeed.doubled_quotients`. The new inert `ExplicitPellPeriod.lean.src` proposes a short specialization in an arbitrary `IΣ₁` model. It has **not** been elaborated or compiled, and is not an internal iPRA proof or a parent-zero transfer.

The recurrence uses parameter `a` with multiplier `A=a+2` and discriminant `delta a=(a+1)*(a+3)=A²−1`, matching the conditional parent's notation after the parent's `a=Y*(X+1)` binding. Put `c=ycoord m a` and `h=2*m*c`. The proposed conclusion supplies natural-model witnesses r and t such that

```text
xcoord h a = 1 + c*c*r,
ycoord h a = t*c*c.
```

These equalities express the needed divisibility of `xcoord h a−1` and `ycoord h a` by c² without performing truncated subtraction. They include m=0. For m>0 the existing recurrence bound `time_le_y` supplies c>0; positivity of the quotient and the final graph witness still need their own client.

The proof specializes the existing theorem at `n=c, R=m`. Its returned ordinate equality is

```text
ycoord (2*c*m) a = 2*c*xcoord m a*c + c*c*s.
```

Commutativity identifies this index with h, and `t=2*xcoord m a+s` gives the proposed equality. The returned abscissa equation gives the first equality. This avoids a new matrix-power induction. The same existing source also states the **stronger ordinate-only** `squared_ordinate` at index `m*c`, and `strong_seed` packages a positive strong norm there when m>0. The requested twice-indexed form remains useful when the explicit parent construction fixes exactly `h=2*m*c`.

The existing squared-seed module was included in an earlier [paired exploratory suffix](../thirteen-model-auxiliary-seed/README.md) with its documented independent audit and inherited package/provider limitations. That record does not check this new source client, establish a compatible current endpoint provider, or eliminate the need for a guarded coherent build and axiom report. The source syntax, rewrite orientation and imported declarations in this new file remain untested by Lean.

The step alone does not prove that a literal graph's c is this represented ordinate, construct the parent's positive auxiliary coordinates, establish the conditional `m≡3`/divisibility hypotheses, or yield a derivation in iPRA. A model theorem under `IΣ₁` does not automatically give a proof-existence theorem in the chosen iPRA formalization. These remain explicit follow-on obligations.

`check.py` pins the source declarations, the parent conditional construction and this inert draft. It verifies the relevant source signatures, the polynomial coefficient identity used in the specialization, and 56 bounded modular matrix controls. Those controls are consistency checks, not proof of the quantified Lean theorem or validation of its tactics. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-explicit-pell-period-model-draft/check.py | cmp - research/ordinary13-explicit-pell-period-model-draft/receipt.json
```

No Lean, build, staging, provider audit or new axiom report was run.

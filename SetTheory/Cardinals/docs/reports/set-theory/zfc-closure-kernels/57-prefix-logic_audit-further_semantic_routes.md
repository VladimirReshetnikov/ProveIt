# Two further source routes and an explicit boundary

This note accompanies `destructive_axiom_theorem.md`. Its conclusions are
source-level mathematics. It does not certify a smaller binary table, a new
startup, or a Lean theorem. The reference source is ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38`.

A later complete repair of the restricted-GEN issue appears in
`projected_gen_theorem.md`: project the current theorem's Cantor code before
using it as a binder. The identity `Imp(i,0)=P(i,i)` then provides every
natural label. That companion note proves the more efficient version that
absorbs one scratch component into the later numerical AX parameter. The
straight omission discussed in section3 below remains uncalibrated.

## 1. Generalizing the current theorem is fully calibrated

Write a working state as `(T,S,d,h)`, and let `a=d+x`, `b=h+y` in an AX
command with fields `(c,x,y,u)`. There is a particularly simple alternative
to the original GEN prefix:

* emit `All(a,T)`;
* do not save the old `T` below the emitted rows;
* retain the original eight logical rows, original bundle, original gate,
  and reset of `d,h`.

Thus the resulting AX stack consists of the original eight rows, followed
by `All(a,T)`, followed by the old stack. The current formula is the original
gated bundle or zero. This is sound under the same invariant: `T` is a
theorem, so its generalization at the arbitrary natural label `a` is a
theorem. No restriction on variable labels is introduced.

The normalization, axiom selection, bundle selection, and MP cleanup blocks
from the destructive-AX theorem continue to work. In their contracts, the
only role of the GEN row is that it is a theorem and cannot be falsity code
1. For the actual GEN block the interface is even simpler. If `p` returns
`(H,S,0,0)`, then

```
p ; AX(c=i,x=i,y=0,u=0) ; NIP^9 ; DROP ; NIP
```

returns `(All(i,H),S,0,0)`, or halts already. The gate is zero because `c=a`.
The nine NIPs expose and cache the GEN row; DROP makes it current; the final
NIP removes the saved zero. This is valid with either preserving or
consuming DROP, and with either successful-MP stack convention.

Consequently this alternative has the full original C254 refutation
equivalence. It requires no renaming, Henkin, equality, native-theory, or
ZFC calibration theorem beyond those already used for the original
calculus. Its physical benefit is unmeasured. A direct implementation could
copy `d` into scratch1 while restoring `d`, then use original
`pair162; times4_117; add2_159` on `(scratch1,T)`. The old GEN body instead
pushes/copies the parameter and cached theorem and pops the parameter again.
Whether the new copy can share enough existing control is a compiler
question, not a consequence of this source proof.

## 2. Decoding the cached implication is fully calibrated

The original MP branch constructs `Imp(T,d+x)` and compares it with `h`.
An alternative branch can decode `h` instead. Here the ordinary command
reader still changes `d` to `d+x`; the branch itself preserves that value.

For `h` divisible by four, let

```
(A,B) = unP(h/4).
```

The new branch outputs `(B,S,d+x,0)` when `A=T`, and `(0,S,d+x,0)` otherwise.
If `h` is not divisible by four it also outputs `(0,S,d+x,0)`. Scratch
registers finish zero. The zero alias is intentional:
`h=0=Imp(0,0)` decodes to `(A,B)=(0,0)` and can only return truth zero.

Soundness is immediate from the exact base-four and Cantor equations.
Every successful nonzero or zero-tag cache is literally `Imp(A,B)`, so
current theorem `A` and cached theorem `Imp(A,B)` justify theorem `B` by
the original MP rule. On all other inputs the branch returns truth.

Completeness requires no new global proof translation. Every MP use in the
blocks of `destructive_axiom_theorem.md` deliberately prepares current `A`,
cache `Imp(A,B)`, parameter zero, and command argument `B`. The new branch
therefore returns exactly the same state as the original successful MP
with its dummy zero push removed. The normalization command `MP 1`, used
with cache zero, also has exactly the required result `(0,S,1,0)`:
the decoded antecedent/consequent are both zero, so both its matching and
nonmatching cases return current zero. Those are the only MP contracts
used by the proof-block construction. All original C254 proofs consequently
have blocks, and the unchanged exhaustive enumerator gives the same
refutation criterion.

### A fused register implementation to measure

Use original logical register names `T,S,d,h,X,Y` and assume `X=Y=0`.
The remaining registers `N,AC,PL` are preserved.

1. Consume `h` in groups of four. For every complete group execute the
   original Cantor inverse-walk body154 on `(X,Y)`. The first attempted
   decrement being zero terminates successfully. Exhaustion at the second,
   third, or fourth decrement is an invalid tag and takes the cleanup path.
2. On valid exhaustion, `h=0` and `(X,Y)=unP(old_h/4)`. Transfer current `T`
   into `h`, clearing `T`.
3. Execute the original destructive equality test123 on `(X,h)`. In its
   equality body, execute original loop211 (`Y -> X`) followed by original
   loop208 (`X -> T`). Clear any remaining `Y` after the conditional.
4. The invalid-tag path clears `T,X,Y,h` and returns normally.

The inverse-walk loop is fused with quartering; no register stores the
quotient. The transfer `T -> h` can use the existing increment-and-continue
body191 with a new decrement-T loop root. The original comparison clears
both compared values whether they match or not. A clean valid success
therefore returns `T=B`; a valid mismatch returns `T=0`; every path has
clean scratch. Correct control-level wiring and the number of newly
reachable decoder nodes remain to be measured.

## 3. Omitting the entire original first GEN parameter macro remains open

A more aggressive edit deletes the initial AX macro166 entirely. The
remaining prefix `par2; All` emits `All(T,h)`: the old current theorem is
used as the binder label. It also consumes that current value rather than
saving it. This remains sound, but it supports direct generalization only
at labels that can occur as current theorems.

There is an infinite, strictly increasing, cofinal reservoir of such labels:

```
g(i) = Imp(i,0) = 4 P(i,0) = 2 i(i+1).
```

Every `g(i)` has a purely propositional proof from truth zero and the K
schema. This uses no GEN rule. In particular `g(0)=0`, which also preserves
the special falsity alias `Rel(0,0)` under a variable injection using `g`.
If `p` returns `H` and `q_i` is a propositional block returning `g(i)`, the
preparation

```
p ; DROP ; q_i ; NIP
```

leaves current `g(i)`, cached `H`, and the original underlying stack. The
aggressive AX followed by `NIP^9; DROP; NIP` then produces
`All(g(i),H)`, with zero fields, as required. Thus the machine covers a
precisely described calculus whose allowed GEN labels include the range
of `g`.

This fact alone does **not** establish the required ZFC consistency
comparison. There is a concrete obstruction to the tempting instruction
to "rename every variable by g". In the original native bundle the same
number `c` is both the encoded matrix and the label bound for the collected
set. If matrix `f` has code `c`, global variable renaming transforms the
matrix to a formula with code `encode(rename_g(f))`, but transforms the
collection binder to `g(c)`. These are different operations. The result is
not the literal bundle produced by the original arithmetic emitter.

The original implementation resolves this coding mismatch semantically by
hygienic encoding and syntactically by ordinary first-order logic. One
cannot simply reuse the existing alpha-renaming proof in the restricted
calculus: `TarskiLeibniz.spec` uses `all_mono` at the original binder, and
`all_mono` is proved using GEN at that binder. `alpha_bwd` and the clean-form
transport inherit this dependency. The binder may be `c`, outside the
reservoir. Likewise, restricting `c` itself to theorem codes would make
the matrix a theorem and would not represent arbitrary Separation or
Collection matrices.

A sufficient remaining result would be a proved restricted-GEN completeness
theorem that handles the literal native bundles despite their bound labels
outside the reservoir, or an explicit alternative bundle transport whose
proof uses only permitted GEN labels. Neither is supplied here. It would be
incorrect to attach the original ZFC calibration to this aggressive table
solely on the basis of the reservoir construction or finite source tests.

## Primary source pointers

All references below are relative to the pinned ProveIt tree.

* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Lib254.lean`:
  `pair162`, `body154`, the transfer loops, and clean scratch contracts.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Macros254.lean`:
  exact parameter pushes, formula constructors, and theorem-stack pops.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Control254.lean`:
  destructive equality, original MP, and NIP contracts.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiDerived.lean`:
  `all_mono` explicitly invokes GEN at its index.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiLeibniz.lean`:
  `spec`, `alpha_fwd`, and `alpha_bwd`.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254GIC.lean`:
  hygienic matrix encoding and the self-code freshness gate.

The older successful-MP dummy-push deletion is prior work in
`Research/ZFC/mp_dummy_push_partial_cost.md`; it should not be attributed to
this note. The decoded-MP presentation above is a different source route,
but no claim of global novelty or binary savings is made.

# A cache-consuming AX schedule with a bounded sixth-row sampler

This note fixes the complete command-level contract for the source architecture proposed during the search. It does not assert that a particular source file or binary table realizes it.

## AX contract

Let incoming state be `(t,w,d,h)` and read the same private parameter c and two increments x,y as before. Set

```
U=d, A=d+x, B=y, C=c.
```

The key scheduling opportunity is to construct and push `Q_U(h)` before consuming the old cache, then compute A while U is still available. Construct `rho6(U,A)` at that point. Afterward the remaining row emitters may reuse the former cache and counter storage for A and B.

The desired final AX interface is

```
(G(A,B,C), [a1,...,a8,Q_U(h),t;w], 0, 0),
```

where the first eight heads are any fixed permutation of

```
R1(A,B,C), R2(A,B,C), R3(A,B,C), R4(A,B,C),
R5(A,B,C), rho6(U,A), R7(A,B,C), L(A,B,C,U).
```

All these eight heads have tag0 and are not1. The ninth has tag2 and the tenth is the old top. The gate is the exact original full bundle with its original equality tests. U<=A holds by construction.

Two changes distinguish this interface from the inherited AX: B is the freely supplied y rather than h+y, and the sixth row is sampled at `(U,A)` rather than `(A,C)`. The former simply decouples an otherwise free axiom parameter from the theorem-valued old cache. The latter is complete by the quantified-matrix padding theorem.

## Soundness and logical completeness

Every emitted head is an axiom or a permitted theorem generalization of the old cache. The eighth row is dominated, the sixth is an ordinary sixth-row instance, and the gate remains an accepted bundle or truth. Thus AX preserves theoremhood for every raw payload; deleting the old cache contribution to B introduces no additional axiom.

For every desired retained row other than row6, clear top/counter/cache and choose U=0, x=A, y=B, c=C. This supplies its full unrestricted parameter range. For a desired dominated eighth row choose U with J(U), x=A-U, y=B and c=C. For a desired restricted sixth row `(i,m)` with i<=m choose U=i, x=m-i, y=0 and c=0. The arbitrary private parameter in the last choice is immaterial to that row. These choices include all zero cases, with J(0) empty.

Every unrestricted sixth-row instance has an exact finite derivation using one restricted instance with binder strictly below matrix, together with K/S, normality, theorem GEN and MP. Therefore the new sampled axiom calculus and the accepted native calculus have exactly the same theorem codes. This is a theorem-code comparison, not merely one direction of a model interpretation.

## Strong compiler with any fixed row permutation

Let S be the accepted transfer on normal returns, and define the same macros

```
D=AX(0;0,0);
H=D;S^11;
PUSH=D;S^9;MP(0);
DISCARD=MP(1);AX(1;0,0);S^10;MP(0).
```

The old proofs depend only on the ten-head interface, tags, saved top and zero-gate equalities used below. They still apply. In fact D now always has zero gate because C=B=0; its ninth head remains Q_U(h). The exact normal equations for H and PUSH are unchanged, with the previously chosen guard convention.

If the desired logical row occurs at stack position j, where 1<=j<=8, its general selection suffix is

```
S^(j+1);H^(9-j).
```

After the first shifts it is on top, with precisely 9-j temporary heads left above the original stack. The H macros preserve that top, remove the remaining temporary heads through the saved cleared zero, and restore the original stack with cache/counter0. This formula applies to the newly positioned sixth and eighth rows as well as the other six. It avoids assuming the old row order before the source emitter's actual order has been checked.

The full bundle block is still `DISCARD;AX(c;a,b);H^10` for an enabled triple. Its selected B is the independent input b. The GEN block stays

```
B_X;PUSH;J(i);S;AX(i;0,0);S^10.
```

Before AX its state is `(0,w,i,X)`. The new A=i, B=0, C=i force zero gate and its ninth head is exactly Q_i(X). Ten shifts return that head with the original stack. The original major-first MP block also remains correct: after successful MP(B), its cleanup call `AX(B;0,0)` has U=A=C=B, though its independent B-parameter is now0. The A=C gate condition still forces zero, and the ten-head counting still removes exactly the intentionally pushed zero.

The truth, theorem GEN and MP induction therefore gives the same strong compiler. First translate an unrestricted sixth-row proof by the explicit padding certificate, then compile that finite proof in the new sampler. The source's primitive command fields remain the old three-command fields, so its cofinal successful candidate construction and strict proof-pointer drain argument are unchanged. Protected-tail credit remains ten new heads for AX and minus one for each returning transfer.

## Remaining source obligations

The source must verify the exact eight-head permutation and the ninth/tenth positions; distinguish the old cache used by GEN from its later reused storage; construct rho6 while the old U is still available; preserve the full original bundle and its gates; and reset the same scratch, counter and cache registers. A source schedule and its runtime certificate are needed before this interface becomes a new consistency machine. Any independent constructor orientation justified by `constructor_orientation.md` can be combined with this sampler, since its logical transport and constructor-domination arguments remain valid.

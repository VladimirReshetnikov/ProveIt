# The directed193 product relation as a synchronized four-coordinate orbit

The actual context-absorbed193 matrix alphabet admits an exact unbounded preprocessing: remove the entire lower matrix block and its A/C/B phases, and use **96 synchronized transition choices on four signed integer coordinates**. The two row vectors need only meet at the endpoint. This works for arbitrary lengths, with both directions proved below; it retains the actual finite-input relation.

The new packet also pays for one complete local transition predicate. Its literal shared source has **2039=1103M+936A** operations, eight supplied signed coordinates and exact degree192. It is the product of96 sums of four squares, so it introduces no selector witnesses. This deliberately explicit local polynomial is not a cost improvement over the universal84 circuit. An unbounded sequence of its steps still needs packing, typing and a duration certificate. The ordinary-input Pell index also remains unpaid in this interface.

## 1. Exact reduction on the actual fixed alphabet

Read the [fixed-context parent](matrix193_context_absorption.md) with its193 generators. Write their upper blocks as

    A_i: H_i, B_i: G_i^(-1), central C: C,

where i runs over the96 retained tile identifiers. These are the context-absorbed blocks, not the original incoming coefficients. Every H_i, G_i and C belongs to the inherited group H'. Define the fixed matrices

    K_i=C^(-1) H_i C.

The receipt saves all96 pairs (K_i,G_i), reconstructed directly from the full actual193 array. They are integral determinant-one matrices; no variable inverse or coordinate division is introduced.

Let M belong to H'. For the intended ordinary-input target, M=B^(-x), with exactly indexed x. Let e1=(1,0). Start two row vectors at

    v_0=e1 C, w_0=e1 M.

Choose a common tile i at each step and update

    v_(j+1)=v_j K_i, w_(j+1)=w_j G_i.                 (1)

Then, for every d>=0, there is a d-step orbit with v_d=w_d if and only if the actual193 semigroup has a membership witness for diag(M,P) of the form

    A_(i1)...A_(id) C B_(id)...B_(i1).                (2)

To prove this, put H(s)=H_(i1)...H_(id) and G(s)=G_(i1)...G_(id). Induction in the actual right-action convention gives

    v_d=e1 H(s) C, w_d=e1 M G(s).

Both represented matrices lie in H'. Its inherited group-wide first-row injectivity therefore makes row equality equivalent to

    H(s) C=M G(s), or H(s) C G(s)^(-1)=M.             (3)

The upper block of (2) is exactly the last expression, and its lower block is P. Conversely the unchanged lower-marker theorem forces every positive product with lower block P into precisely (2), so no product witnesses are omitted. Reversing the B factors is essential. The proof neither assumes that the matrices commute nor changes their multiplication convention.

The d=0 orbit is allowed and corresponds to the nonempty product C. It succeeds exactly when M=C, by the same first-row theorem. This is not acceptance by an empty semigroup product. In the saved fixture M=I and C is nonidentity, so the empty orbit fails.

This theorem removes the lower-block arithmetic entirely from this alternative certificate interface. Synchronization of the96 choices is still essential; independent choices in the two row lanes would not be justified. Group membership and determinant constraints are not additional unpriced oracles along a certified orbit: they follow inductively from its fixed initial matrices and the actual transition matrices. The external M hypothesis must still be enforced by the intended target representation. A freely supplied Pell solution of an arbitrary index is not a substitute for M=B^(-x).

## 2. A fully paid local transition polynomial

Use eight signed ports

    z=(v0,v1,w0,w1), z'=(v0',v1',w0',w1').

For each i form the four affine-linear residuals of (1), with the fixed entries of K_i and G_i multiplied explicitly. Let E_i be their sum of four squares. Set

    P_step(z,z')=product_(i in the96 tiles) E_i(z,z'). (4)

Over the integers, and also over the reals, (4) vanishes exactly when at least one common i realizes both row updates. Each factor is nonnegative and vanishes only when all four of that tile's residuals vanish. Distinct tiles may realize the same particular transition; the existence of a choice is all the orbit theorem requires.

The emitter shares identical arithmetic registers across all96 branches, folds purely fixed expressions, and omits multiplications by0 or1. Every other fixed-coefficient multiplication is charged. It emits the complete branch sources and all95 final product multiplications. The independent coefficient interpreter checks all384 residuals and every full quadratic factor against the separately reconstructed matrix formulas. The finalizer is checked to multiply every factor, and every emitted gate is live.

All factors are homogeneous quadratics in the eight independent ports. The next-state coordinates have coefficient1 in their respective residuals, so no factor is the zero polynomial. Their product has exact total degree192, with no use of constraints valid only on zero sets. The declared source has2039 operations; it is not asserted optimal among finite-disjunction encodings.

The endpoint predicate alone is

    (v0-w0)^2+(v1-w1)^2,

costing5=2M+3A. The initial left row is fixed. The right row retains the parent's three-gate assembly `(chi+52500*psi,-29036*psi)` when chi,psi have their required index. Thus the reduction makes the varying target and local transition costs explicit rather than treating a finite selected table as free.

## 3. What is and is not a Diophantine certificate here

For each *fixed* d, supply the four signed coordinates at times1 through d, substitute the fixed initial vectors, and add the d instances of P_step to the endpoint sum of squares. Every summand is nonnegative on real coordinates, so the sum vanishes exactly on the desired d-step orbits. This gives a concrete finite-length Diophantine compiler. Copying the declared schedules without further specialization gives the paid upper bound

    2039d + 5 + d = 2040d+5

from a supplied target row, including d additions for the final sum. Computing that row through the three conditional Pell-target gates gives2040d+8. The degree is at most192 for d>=1; the local exact-degree assertion is not silently extended through fixed initial-value substitutions. Fixed-constant simplification or endpoint substitution may lower particular instances; these are explicit upper bounds, not optimal finite-length ledgers. The number of signed trajectory witnesses is4d.

That family does **not** by itself give a bounded-variable representation of arbitrary-length membership. Merely quantifying a length does not turn a variable number of row coordinates into one fixed polynomial. A next packing step must enforce the full local disjunction across all positions, signed-value bounds, synchronization and common duration, while preserving the initial and endpoint conditions. No such cost is hidden in2039 or in the four-coordinate state dimension. Positive witness conversion is likewise not charged in this signed local packet.

This differs from the older [PCP affine trace](matrix_pcp_trace.md), whose two word accumulators require selected weighted fields and typed common geometry. It specializes directly to the actual faithful matrix coefficients and uses the exact lower-marker/first-row theorems to remove the directed phases. The earlier [four-register matrix history](group_four_register_history.md) instead compiles an inverse-closed paired alphabet to controlled elementary shears and uses a length-dependent separating vector. Neither old helper was executed. Bracket-based separator deletion is already covered by [the existing GPCP proof](gpcp_bracket_anchored_history.md) and is not claimed as a new result here.

## 4. Actual fixture and bounded evidence

The saved parent uses fixed contexts `[110` and `A0]`. Its accepted ordinary parameter is x=0, corresponding to the genuine finite machine input `[110A0]`. The same83-tile sequence gives a complete84-state row trajectory. Every row state is saved, every local transition is evaluated in the full polynomial, and the final rows agree. Independently multiplying the original167 full4-by-4 generators recovers the same target diag(I,P). This is an actual accepted finite-input fixture; no universality of these particular contexts is claimed.

The helper also checks each of the96 branches on a separately chosen signed row state, sixteen whole signed/rational evaluations including six rational ones, and all96 matrix conjugation identities. Its sparse coefficient checks compare1,728 full quadratic coefficient entries and audit the whole local transition source, rather than just the fixture's visited tiles. The unrestricted equivalence is proved in Section1, not inferred from these tests.

The parent context trio is authenticated at SHA256:

| File | SHA256 |
|---|---|
| `matrix193_context_absorption.py` | `1304ea242ca6a5faafdb527ac3e56c6cd06b0276dca6441fc3477c7065054485` |
| `matrix193_context_absorption.json` | `73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436` |
| `matrix193_context_absorption.md` | `d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b` |

The Gamma1 proof and directed193 proof are additionally pinned by the helper. No predecessor source is imported or executed. The bounded CLI rejects duplicate/nonfinite JSON, uses explicit exception checks and compares receipts recursively with exact types:

    python3 /absolute/path/matrix193_synchronized_rows.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/matrix193_synchronized_rows.json

The writer uses the mutually exclusive `--output FILE`. Writer and fresh normal and optimized exact replays from `/` passed on the frozen source and receipt. No repository or frozen predecessor mutation is part of this packet.

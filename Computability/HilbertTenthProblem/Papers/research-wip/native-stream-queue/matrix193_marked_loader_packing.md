# Fixed-arity packing with an ordinary-input marked loader

A single inherited native AND/range kernel can encode an arbitrarily long matched matrix history, count its LOAD macros by an ordinary input, and test equality of the two final rows. The count does not require a supplied duration or a second geometry kernel. This note gives every interface binding and a finite compiler recipe. It also emits one complete, deliberately nonuniversal diagnostic polynomial: **187 operations = 86M + 101A, 27 positive integer witnesses, exact degree 1789**. Its language is all nonnegative inputs; restricting the external input to positive integers gives the corresponding positive-input statement.

The [helper](matrix193_marked_loader_packing.py) and [receipt](matrix193_marked_loader_packing.json) contain all 187 instructions, including the input prefix, six outer residuals, inherited native factors, and final output. The generic construction applies to the actual context-absorbed matrix193 interface, but its unit-shear controller has not been numerically expanded here. Therefore **187 is not a universal-polynomial bound**, and this packet does not improve the current universal 84-operation result. It supplies a paid fixed-arity route beyond the duration-dependent 133/140h interface; no local 133-gate transition polynomial is itself packed or reused for free.

All dependencies are authenticated by the exact SHA256 table in the receipt. They are read as inert bytes or JSON; no predecessor Python is executed or imported.

## 1. Actual matrix interface and a finite controller

The pinned [synchronized-row theorem](matrix193_synchronized_rows.md), [context absorption](matrix193_context_absorption.md), and [Gamma1 recoding](matrix193_gamma1_recode.md) provide 96 matched pairs `(K_i,G_i)` in `SL2(Z)`, a fixed initial row `e1*C`, and the fixed input block

```
B0 = [[-52109, 29036], [-94920, 52891]],
B0^-1 = [[52891, -29036], [94920, -52109]].
```

For every fixed context, the finite-input question is whether some common tile word satisfies

```
e1*C*K_word = e1*B0^(-x)*G_word.                 (1)
```

The pinned [ordinary unary-block interface](u15_unary_block_interface.md) identifies the designated initialized fixed-program instances with their ordinary-input computation languages. The particular saved context fixture is not asserted to be universal. The present transfer preserves (1) for each fixed context, so an initialized universal instance inherits that language; it does not assert universality of every context.

Start four signed physical coordinates at `(e1*C,e1)`. Use the following finite macro controller:

* At hub 0, repeat `LOAD: (X,Y) -> (X,Y*B0^-1)`.
* Take one compulsory identity SWITCH edge from hub 0 to hub 1.
* At hub 1, repeat any of the 96 `TILE_i: (X,Y) -> (X*K_i,Y*G_i)` macros and an identity IDLE edge.
* End at hub 1 and require `X=Y`.

Expand every fixed matrix into signed unit shears. This is an effective finite compilation, not an arithmetic oracle: determinant one implies the first column is primitive; Euclidean row operations reduce it to `(1,0)` up to sign, the remaining upper triangular matrix is a shear, and `-I` is a fixed product of signed shears. Expand each integer shear exponent into a finite repeated unit word. Invert the recorded row-reduction word to recover the given matrix. Apply the two independent row words consecutively for a paired action. A vacuous tile word may be represented by a label-0 identity edge.

Give each nonempty macro its own private path, with distinct internal states. Mark exactly the first edge ID of the private LOAD path; every complete LOAD cycle traverses it once. This is not an aggregate physical-letter selector: TILE words may use the same shear label, and those edges are not counted. Start/end are controller hubs, so no accepted path contains a partial LOAD or TILE. There is no transition from phase 1 back to phase 0. Number hub states 0,1, the remaining states consecutively, and all edges injectively. Choose a power of two `m>=8` at least the number of edges and larger than every state code. Physical labels 1..8 mean the signed shears on the four coordinates; label 0 means identity. Label-0 edges are included in the controller checksum and flow, and omitted from every physical shear selector.

This is an exact description of the whole finite controller from the actual fixed matrix table. Its size may be large. Fixed matrix entries, Euclidean quotients and controller constants depend only on the fixed context/program, never on `x`, a history length, or witnesses.

## 2. Paid outer bindings

Let the explicit controller have `n` edges. Supply positive hats `Ehat_e`, put `E_e=Ehat_e-1`, and compute

```
D = x + Hfix + height_slack,  c0 = D-1,  B = 16D,
J = sum_e E_e,                P = (B-1)J+1.       (2)
```

Here `height_slack>0`; the fixed integer `Hfix` is positive, exceeds the absolute value of each initial signed coordinate, and is at least `m`. Thus `D>x`, the initial shifted coordinates lie strictly between 0 and `2D`, and `B>m` before any native typing.

Supply four positive history words `H_i`, eight selected-source hats `Zhat_l`, a positive joint-bound slack, two shared positive final-coordinate fields `F_even,F_odd`, and a positive population quotient `Q`. Define

```
S_l = sum_(edge label l) E_e,  Z_l = Zhat_l-1,
C = sum_(e=0)^(n-1) E_e P^e,  R_j = 1+P+...+P^(j-1),
O = J R_m, O8 = J R_8,
Hb = (1+P)*(H1+P²*H0+P⁴*H3+P⁶*H2),
Mb = (B-1)*sum_(l=1)^8 S_l P^(l-1),
Zb = sum_(l=1)^8 Z_l P^(l-1),
T = P^(m+8), T2 = P^(m+16), M8 = (2D-1) O8,
H = Hb+P^8*C+T*Hb+B*T2,
M = Mb+P^8*O+T*M8+T2,
Z = Zb+P^8*C+T*Hb,
q = 32 B T2.                                      (3)
```

All powers and repunits have finite binary-square/product schedules. They are part of the variable DAG, not numeral compilation. Bind the six cut ports of the literal 63-row native cone to

```
selection__q                 = q,
selection__padded_A          = 16H+13,
selection__padded_B          = 16M+10,
selection__F3                = 16Z+8,
selection__Zglobal           = sum_i H_i + sum_l Zhat_l + bound_global,
controller__geometry_power   = P.                 (4)
```

The receipt lists all retained native instructions and all twelve independent positive native ports. In particular it retains the tail quotient, first-root gap, both index/linear signs, coupled auxiliary correction, strong factor, and joint bound. This is the actual `m8_private` native cone from [general separate range](group_projective_general_separate_range.md); its dependence on controller size is entirely through the explicit bindings (3). No native constraint is deleted.

For initial signed coordinates `v_i`, let `I_i=c0+v_i`. Let `F_i` be `F_even` for even `i`, `F_odd` for odd `i`. The four history comparisons are

```
B*(H_i + delta_i) = H_i + F_i*P - I_i,
delta_i = Z_(2i+1)-Z_(2i+2)
          - c0*(S_(2i+1)-S_(2i+2)).              (5)
```

Indices in (5) are 1-based physical labels. The shared terminal fields impose equality of the two rows. They are strictly positive shifted terminal values, not external signed target coordinates and not uncharged Pell terms.

If `a_e,b_e` are controller source and target state codes, the open-end flow comparison is

```
sum_e a_e E_e + P = B*sum_e b_e E_e.              (6)
```

The `+P` is essential: the path starts at code 0 and ends at code 1. Finally, for the marked LOAD edge `e*`, impose

```
(B-1)*Q = Ehat_e* + (B-1) - x - 1.               (7)
```

There is just one count comparison and one positive quotient, with no duration variable or population-range slack.

Let `U` be the retained native output `eight_units`, including its joint-bound factor. The full polynomial is

```
U*(1 + sum_(the six comparisons (5)-(7)) residual²) - 1.   (8)
```

All variable products, scalar multiplications, differences, squares and final additions in these formulas are paid. With independent eight hats the construction has `n+29` positive witnesses. For clarity, one straightforward unsimplified schedule has at most `9n+3log2(m)+210` operations: packing at most `5n+3log2(m)+85`, the 63-row native cone, at most 38 history producers, at most `4n` flow producers, four count producers, and the 20-gate finalizer. This is a conservative construction bound, not a numerical universal bound or an optimality claim. The diagnostic below uses literal common-expression sharing and absent-label specialization and is recounted directly. To make the packing bound auditable, writing `p=log2(m)`, the power chain costs `p` multiplications, the shared binary repunit products cost at most `2p-1` gates, and the two origin-mask products cost at most two more, totaling `3p+1`. Both the compulsory SWITCH and the hub-1 IDLE are label-0 edges. Consequently the grouped physical-selector sums require at most `n-2` additions (at most `n-3` when a physical label is present); using this bound rather than the crude `n` bound reduces a conservative packing ledger `5n+3p+87` to the stated `5n+3p+85`. The bound permits further sharing and zero/one simplifications without charging them as savings until a literal graph is emitted.

## 3. Native recovery, chronological typing and LOAD count

At a positive integer zero of (8), its positive sum-of-squares multiplier and integral `U` force every outer residual to vanish and `U=1`. Every integral unit factor is therefore a sign. The retained joint bound gives `P>=12` and bounds each `H_i` and each unshifted `Z_l` below `P`. Nonnegative edge words give `J>=1` and `B<=P`.

The scalar estimates and sign bootstrap of the pinned [separate-range proof, Section 3](group_projective_general_separate_range.md#3-exact-scalar-interfaces-and-positive-domain-transfer) apply to the actual bindings (3)-(4). Label-0 edges do not change those estimates: their edge fields remain in `C,J,O`, while `sum_l S_l<=J` still holds. The four truth fields are strictly positive with the prescribed residues modulo 16. The inherited tail proof treats both index signs before the large native-size recovery. It forces the native factors to +1 and `q` to be dyadic. Then `B,P` are dyadic and `P=B^t` for some integer `t>=1`.

The joined AND separates into the physical, controller, range and top regions. The controller lanes become Boolean radix-B indicators, and their checksum with `B>m` gives exactly one edge at each cell. The general weighted equation (6), rather than a private-path shortcut, recovers chronological continuity. Its coefficients are the initial source code, successive source-minus-previous-target codes, and final `1-target`; their absolute values are below `B`, so successive reduction modulo `B` recovers them exactly. It gives a path from hub 0 to hub 1.

The range region types every supplied history digit `X_i(j)` as

```
0 <= X_i(j) <= 2D-1,
-(D-1) <= X_i(j)-c0 <= D.                        (9)
```

Selected products are the exact source history digits at the selected cells. Reducing (5) cell by cell first recovers the fixed initial state, then every signed unit-shear update. Interior residual coefficients have absolute value below `3D+1<B`; the label-0 case is the identity recurrence. The final coefficient gives the actual terminal state, with the two shared terminal fields. No separate range bound on those final fields is needed for this induction. In particular the compulsory SWITCH edge has a **typed pre-state digit** containing the row after every LOAD and before any TILE, even when there are no LOADs or no TILEs.

Let `k` be the number of completed actual LOAD macros. At that switch, `Y=e1*B0^(-k)`. Its first coordinate satisfies

```
a_0=1, a_1=52891,
a_(k+2)=782*a_(k+1)-a_k.                          (10)
```

The determinant-one characteristic identity proves the recurrence. Inductively `a_(k+1)>a_k>=1`, with positive integral differences, so `a_k>=k+1`. Applying (9) at the switch gives `k+1<=a_k<=D`, hence `k<D`. This proof is uniform over contexts because context absorption leaves `B0` unchanged.

The marked edge has Boolean word `S=E_e*` and population exactly `k`, so `S congruent k (mod B-1)`. Equation (7) says `S congruent x (mod B-1)`. Since `0<=x<D`, `0<=k<D` and `D<B-1`, it follows that `k=x`. The physical path therefore gives (1), with the unchanged ordinary input. There is no deleted-index assumption and no finite-field substitute for exact integer products.

## 4. Positive completeness and edge cases

Conversely take a finite tile word satisfying (1). Run exactly `x` LOAD macros, the identity SWITCH, that tile word, and any desired number of hub-1 identity IDLEs. Choose a sufficiently large power of two `D`, exceeding `x+Hfix` and every absolute physical coordinate (including the terminal state) plus one. All shifted history and terminal fields are then positive. Choose the actual radix-B edge words and selected products, and `P=B^t`.

At every cell the four shifted digits sum to at most `8D-4`, and at most one physical selector is active, so the selected-digit sum is at most `2D-1`. Consequently

```
sum H_i + sum Z_l <= (10D-5)J,
bound_global = P+1-sum H_i-sum Z_l-8
             >= (6D+4)J-6 > 0.                  (11)
```

Thus the joint-bound factor equals 1. The joined truth fields are positive at the exact scale (3), and the pinned native converse supplies fresh strictly positive native coordinates at that scale. They are not obtained by assuming equality of the predecessor's entire numeric witness tuple.

For the count quotient, every marked place contributes `B^j>=1`, and

```
Q = 1 + (S-x)/(B-1)
  = 1 + sum_(marked cells j) (B^j-1)/(B-1) > 0.   (12)
```

All outer comparisons hold. For `x=0`, there are no LOAD edges and `Q=1`; the compulsory SWITCH still supplies the typed boundary. An empty TILE word is permitted precisely when its row endpoint equality holds. IDLEs may extend duration arbitrarily after the switch without changing `k`, the physical terminal state, or input `x`. Even with no LOAD and no TILE there is at least the SWITCH cell. Native witness count is independent of this duration.

These arguments establish equality of the positive-zero input projection with (1). They do not give a bijection between different native witness fibers.

## 5. The complete diagnostic source

The saved diagnostic has initial signed coordinates `(1,0,1,0)`, `Hfix=8`, `m=8`, and the following actual four edges:

| Edge | Source | Target | Physical label | Meaning |
|---|---:|---:|---:|---|
|0|0|0|8|LOAD: `Y1 -= Y0`; marked edge|
|1|0|1|0|identity SWITCH|
|2|1|1|4|TILE: `X1 -= X0`|
|3|1|1|0|identity IDLE|

It accepts exactly `LOAD^x SWITCH (TILE or IDLE)*` with exactly `x` TILEs. Every natural input is accepted. Its LOAD count proof is separate from (10): at the switch, `Y=(1,-k)`, so (9) gives `k<=D-1<D`. The actual matrix193 growth recurrence is not falsely applied to this different loader.

Six physical selected words are identically zero and their positive hats are specialized to 1. The remaining independent hats are `Zhat3` and `Zhat7` in the predecessor's zero-based names. Every history and native port remains paid. The global bound is correspondingly `sum H_i+Zhat3+Zhat7+6+bound_global`. Its minimal value is still 13, so the pretyping bootstrap is unchanged. `F_even,F_odd` and the population quotient are explicit positive witnesses.

| Part | Paid operations |
|---|---:|
| All packing/input/cut producers |78|
| Exact inherited native cone |63|
| Four history, flow and count comparison producers |26|
| Six differences, six squares, five joins, +1, native product, -1 |20|
| **Complete output** |**187 = 86M + 101A**|

All 187 rows and all 28 supplied ports, including external `x`, are live. There are 27 witnesses, independent of duration. The source is a complete acyclic polynomial array; there are no implicit equality-test costs or free affine input transformations.

For degree, every supplied coordinate has degree one and fixed numerals have degree zero. Here `P` has degree 2, `q` has degree 49 and the actual highest `F3` term `16*P^16*Hb` has degree 47 with nonzero leader. Thus the tail-native `a` has degree 195 and `c` has degree 51. The inherited, all-value-cancelled unit degrees are respectively

```
first 247, main 442, auxiliary 308,
index 196, linear 196, strong 392, joint bound 2.
```

Their sum is 1783. These follow from the seven literal cone leaders in the pinned separate-range proof; the first gap and all native ports remain independent here. In particular the main degree uses the polynomial expansion of its norm, never an on-zero unit substitution. The outer history residuals have degree at most 3, and the remaining residuals degree at most 2. Hence degree 1789 is an upper bound. A fresh coefficient-by-coefficient univariate substitution into the full 187-row DAG, modulo 1000000007, has degree 1789 and nonzero top coefficient, proving attainment for this exact fixed-numeral graph. The raw degree propagation bound 1839 is also recorded, rather than confused with exact degree.

## 6. Evidence and limits

The standalone checker pins 13 files, extracts the exact 63 native rows with six cut boundaries, emits the entire source, and checks closure/liveness and the full paid ledger. Sixteen arbitrary full-source evaluations, including four rational tuples, agree with separate direct formulas for all scalar ports, native factors, six residuals, and final output. These are off-zero identities, not asserted full positive Pell witnesses.

Twelve genuine diagnostic outer histories cover `x=0,1,2,3`, with 0,1,3 extra IDLEs each. They check all six literal comparisons, positive outer coordinates, the joined AND and positive native truth fields. Changing only `x` and compensating the height to hold `D` fixed makes the count residual nonzero. All 21,844 edge words of lengths 1 through 7 check the open-end flow equation against the actual controller language. Thirty-three exact powers of the actual `B0^-1` independently confirm the recurrence and growth lower bound. The general proof supplies the native positive extensions; their astronomical full Pell tuples are not materialized.

This packet does not numerically compile all 96 actual tile matrices into unit shears or count that actual controller's polynomial. It does give an explicit finite algorithm and full bindings for doing so, with no unbounded oracle in the resulting source. The dimension remains four physical history coordinates; the additional population witness is one scalar quotient. Runtime arithmetic, integer domain, all positivity restrictions and ordinary input are explicit. The result is fixed arity for each fixed program, without claiming a competitive universal operation count.

Replay from any directory, using the installed WIP root and receipt:

```
python3 matrix193_marked_loader_packing.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/matrix193_marked_loader_packing.json
python3 -O matrix193_marked_loader_packing.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/matrix193_marked_loader_packing.json
```

Use `--output` instead of `--expect` to regenerate a deterministic receipt. Fresh normal and optimized exact receipt replays from `/` both passed. Independent proof/source cross-reads found no requested mathematical correction; the generic packing ledger explicitly records the two mandatory label-0 edges.

# Directed matrix membership: an affine unary loader and a power-block obstruction

This bounded successor has two conclusions. The literal 193-generator source admits an **eight-operation ordinary unary-input target loader**, but its universality on that restricted input family is unproved. Separately, replacing arbitrary semigroup words by any fixed finite collection of power-block templates cannot preserve the source's universal finite-tape relation. The second statement is a decidability obstruction even if exact matrix powers were supplied without arithmetic cost. Neither conclusion changes the established complete 84-operation universal bound.

The attached fresh helper reads pinned JSON and notes as data; it executes no archived or predecessor Python. It reconstructs all 193 matrices as explicit pairs of free-group words and checks the complete eight-row loader. The unbounded obstruction is a mathematical theorem below, not a conclusion of bounded fixtures.

## 1. Actual source and authenticated interface

Immediate WIP dependencies, relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:

| File | SHA-256 |
| --- | --- |
| group_directed_semigroup193.json | `c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639` |
| group_directed_semigroup193.md | `75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e` |
| review_incoming_matrix_grill.md | `14c0c3042558b212db8ee5885338f9a7af983d57a702f0c7af2b3d352a657cb8` |

The recent Report 32 publication review supplies context, not an additional theorem premise. The present result is distinct from its already recorded growing-length SOS boundary.

Use the pinned source's free matrices

```
P = [[1,2],[0,1]], Q = [[1,0],[2,1]],
E_j = Q^(-j) P Q^j.
```

The inherited free-basis proof identifies their subgroup with the rank-two free group. Each actual generator has an explicit word in each block: `A_i` has `(Phi(h_i),E_i)`, `B_i` has `(Phi(g_i)^(-1),P^(-1)E_i^(-1)P)`, and `C` has `(Phi([J1]#)^(-1),P)`. The helper independently evaluates all these free-word recipes and compares every one of the 3,088 matrix entries with the saved array. The free-basis theorem, rather than those finite comparisons alone, supplies faithfulness.

For a valid input word `w`, the target also has known word coordinates: `(Phi(w#)^(-1),P)`. No algorithm decoding an arbitrary externally supplied integer matrix into a free-group word is assumed. This distinction is essential to the decision argument.

## 2. Complete eight-row unary target component

Every `E_j` is unipotent: writing `E_j=I+N_j`, one has `N_j^2=0` and therefore `E_j^x=I+xN_j` for every integer x. For fixed words U,V and `w_x=U 1^x V`, the upper target is

```
Phi(w_x#)^(-1) = L (I-x*N_2) R = T0 + x*T1,
L = Phi(V#)^(-1), R = Phi(U)^(-1),
T0 = L R, T1 = -L N_2 R.
```

On nonnegative integers this agrees with literal repeated-letter input. For the actual valid family `w_x=[1^x A0]`, the four scalar entries are

```
t00 = -18445239 + 60040312*x
t01 = -519466 + 1690910*x
t10 = 785463424 - 2556728544*x
t11 = 22120697 - 72004920*x.
```

The lower block is the fixed P and off-diagonal blocks are zero. The saved source computes each entry by one multiplication and one addition using fixed signed integer coefficients: **4M+4A, zero supplied witnesses, degree one**. This is the literal source cost under the same compiled fixed-integer coefficient convention used by the matrix packet, not an optimality claim or a count that charges the fixed coefficient compiler as runtime arithmetic. All coefficient values are given in the receipt; no runtime exponentiation or variable-length loader is hidden.

The determinant is identically one: the helper checks its constant, linear, and quadratic coefficients as `(1,0,0)`. It also checks literal word products at nine nonnegative x values through 128; the nilpotence identity proves the all-x statement. The existing semigroup theorem gives exactly

```
T_x belongs to S193 iff U15 halts on left tape 1^x and empty right tape,
```

with initial A scanning zero and blank tails. It does not say this one unary slice is universal. More generally the same eight-row formula applies to fixed U,V forming valid initial configurations; a compiler theorem giving suitable fixed contexts for every c.e. language is still required. The finite-tape universality theorem does not by itself establish that claim.

This component could be composed by direct substitution into a future exact unbounded matrix-membership checker, without adding target witnesses. A complete checker of cost C would give cost C+8 for this specific unary target interface. Beating 84 by that literal composition would require C<=75 and the missing universal unary-input theorem. No such checker or bound is supplied here.

## 3. The power-block decision theorem

**Theorem.** Given explicit word coordinates in `F2 x F2` for constants, bases, and target, solvability of any fixed finite system of equations of the form

```
c0 g1^n1 c1 ... gk^nk ck = T,       n_i in N,
```

with a Presburger condition on the exponents is decidable. One may share exponents between occurrences and equations, and take a finite union of such systems. Both the systems and target may be generated effectively from the input.

Here “fixed” describes the finite expression presented to the algorithm; the procedure is uniform in its length. Natural exponents include zero. Strict positivity is a Presburger constraint. The statement is about a flat product of powers of explicitly given constant group elements, not powers of expressions whose bases contain unknown exponents.

**Proof.** Initially give every exponent occurrence its own variable. For one free-group projection, use a distinct input letter a_i for each occurrence and a final delimiter. A pushdown automaton reads only words in `a1* ... ak* #`. On reading a_i it processes the fixed word for g_i by free reduction on its stack; at block boundaries it likewise processes the fixed constants, and at the final delimiter it processes the target inverse. Empty stack is exactly the projected group equation. This is an effectively constructed context-free language.

Its Parikh image is effectively semilinear. Crucially, each exponent vector specifies exactly one word in this ordered block language, so the Parikh image is exactly the desired solution set, not an order-forgetting relaxation. Constructive Parikh semilinearity is the imported general theorem; an explicit grammar-to-automaton construction is given by [Esparza, Ganty, Kiefer and Luttenberger, Theorem 1.1](https://arxiv.org/abs/1006.3825).

Repeat for the second projection and every equation. Intersect the resulting semilinear sets and impose the equalities identifying shared occurrences, along with the given Presburger condition. These effective Presburger operations preserve decidability, proving the theorem. As a separate primary-literature cross-check, [Lohrey, Section 5 and Theorem 8.1](https://arxiv.org/abs/1807.06774) establishes effective semilinearity for free groups as a special case of the hyperbolic-group result and explains the extension to shared-variable exponent equations. No complexity bound from that paper is needed here.

The bounded-language step and faithful known-word interface were independently challenged by another reviewer without a finding. This is an application of standard theorems, not a novelty claim about group knapsack.

## 4. Consequences for the actual universal semigroup

Suppose a proposed replacement for arbitrary positive words effectively produces, for each finite U15 input w, a finite family of the templates above and claims that one is solvable exactly when `T(w)` belongs to S193. The theorem decides each template, hence their finite union, and would decide the inherited undecidable finite-input U15 halting relation. Thus such a replacement cannot be correct for all valid inputs, under the same universality dependency as the parent.

In particular, no constant K suffices for all accepted targets when witnesses are constrained to at most K homogeneous generator runs. There is not even a total computable input-dependent bound K(w) on the required number of runs: enumerating the finitely many generator patterns of length at most K(w), with unbounded natural run lengths, would again decide membership. This also covers a fixed finite dictionary of compound macro words used as the bases. It does not assert a computable quantitative lower bound for a particular accepted target.

For a **fixed finite** template family and the unary target of Section 2, a stronger statement holds. Move the inverse target to the left-hand product and include x as one further exponent of the fixed E_2. The joint solution set in `(x,n1,...,nk)` is semilinear; projecting to x gives an ultimately periodic subset of the nonnegative integers. Thus this specific route cannot represent even simple non-ultimately-periodic unary sets, before asking for universality. An input-dependent template family still gives decidability but need not yield ultimate periodicity.

The obstruction persists if exact powers are implemented by efficient Cayley–Hamilton or Pell gadgets: when those gadgets have exactly the asserted power semantics and add only the stated Presburger restrictions, they do not change which templates are solvable. The unbounded word's order cannot be replaced by a computably bounded list of powered constant blocks.

## 5. What this does not exclude

This result is not a lower bound on general Diophantine representations. Arbitrary nonlinear constraints among exponent variables, witness-dependent group bases, nested exponent expressions, or a new nonsemilinear history representation fall outside the theorem. Such additional arithmetic can itself carry undecidability and must be proved and charged. The theorem likewise does not concern a different matrix substrate outside this faithfully represented product of free groups.

The established 84-operation polynomial already has a complete fixed-arity ordinary-input theorem on valid compiler slices. The new eight-gate component has neither a complete history checker nor the required universal unary-context loader theorem. It provides a concrete small interface to test, while the obstruction rules out one natural attempt to remove the history checker altogether. No generator count is compared to an arithmetic-gate count.

## 6. Bounded evidence and replay

The helper certifies only the actual word-coordinate source mapping and affine loader. It does not implement constructive Parikh elimination or test the universal theorem by enumeration. All its checks use explicit failures and run equally under optimized Python. Receipt comparison is type-exact.

```
python3 /absolute/path/matrix193_power_block_obstruction.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_power_block_obstruction.json
```

The writer and fresh normal and optimized replays from `/` passed. There were no repository mutations, archived-code executions, historical suite runs, or claims about full giant Diophantine witnesses.

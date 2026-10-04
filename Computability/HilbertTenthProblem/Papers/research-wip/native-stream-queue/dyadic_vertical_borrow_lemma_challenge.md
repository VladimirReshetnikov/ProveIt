# Independent finite-digit borrow lemma

**PASS.** The proposed contradiction holds with the block convention below. It needs no compiler, historical program, or external theorem. In fact, equality of the last three labels is stronger than necessary: after the first block, two consecutive underlying blocks with the same terminal-label status already give a contradiction.

## Definitions and precise indexing

Fix an even radix `V >= 4` and an integer block length `a >= 3`. Digits are processed from lower to higher position. The six observed blocks are `j=0,1,...,5`, each with positions `r=0,...,a-1`. In each block, the positive digit vector `P_j` is the sum of two one-hot vectors, allowing their labels to coincide. Thus every digit lies in `{0,1,2}` and `sum_r P_j(r)=2`.

Let the underlying negative one-hot blocks be `U_j`, with label `lambda_j` in `{0,...,a-1}`, for `j=-1,0,...,5`. Shift the concatenated sequence upward by one digit. The observed shifted blocks are therefore

- `N_j(0) = 1` exactly when `lambda_(j-1)=a-1`;
- `N_j(r) = 1` exactly when `lambda_j=r-1`, for `1 <= r <= a-1`.

These possible ones occupy distinct positions. Consequently,

`sum_r N_j(r) = 1_{lambda_(j-1)=a-1} + 1_{lambda_j<a-1} <= 2`.

In a cyclic six-block sequence, set `U_-1=U_5`. The argument also applies to a six-block window of a longer sequence with an arbitrary preceding block. Reversing the physical meaning of “upward” merely requires reindexing so that the displayed shift formula is the one actually used.

Let `beta_t` be the incoming borrow at global digit `t`, where `t=ja+r`, with arbitrary initial `beta_0` in `{0,1}`. Define

`raw_t = P_t - N_t - beta_t`,

`beta_(t+1) = 1` iff `raw_t < 0`, and

`d_t = raw_t + V beta_(t+1)`.

All raw values are in `[-2,2]`, so these are valid radix-`V` digits. Suppose every `d_t`, for `0 <= t < 6a`, is even.

## Local transitions and first-block reset

Since `V` is even, `d_t` is even iff `P_t-N_t-beta_t` is even. The complete permitted transition table is

| Incoming borrow | Negative digit | Permitted positive digit(s) | Outgoing borrow |
|---|---|---|---|
| 0 | 0 | 0 or 2 | 0 |
| 0 | 1 | 1 | 0 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 |
| 1 | 1 | 2 | 0 |

Thus **zero borrow is absorbing**. A borrow can persist only at a digit with `P_t=0,N_t=1`. In particular, encountering `N_t=0` forces any incoming borrow to reset. Since the first block has at most two negative ones and at least three positions, it has such a digit, so its outgoing borrow is zero.

The proposed stronger wording “before its end” is also valid, interpreted precisely as **the borrow entering the final digit of the first block is already zero**. If it were still one there, every preceding digit would have `P=0,N=1`. Since the block's total positive digit sum is two, the final positive digit must then be two. The table forces its negative digit to be one as well. That would give `a >= 3` negative ones in a block having at most two, a contradiction.

No cyclic boundary assumption was used. If cyclic subtraction additionally requires `beta_(6a)=beta_0`, the reset and absorbing property force `beta_0=0` too; the same parity condition then holds in every block.

## Last-five parity and last-three-label contradiction

At every digit of blocks `j=1,...,5`, incoming and outgoing borrow are zero. Hence `d_t=P_t-N_t`, and summing the even digits within a block gives

`2 - sum_r N_j(r)` even.

So each of those five negative block populations is even, necessarily zero or two. More precisely, writing `e_j=1_{lambda_j=a-1}`, the shift formula gives

`sum_r N_j(r) = e_(j-1) + 1 - e_j`.

It is even exactly when `e_(j-1) != e_j`. Thus the terminal-label indicators must alternate across every pair `(U_(j-1),U_j)` for `j=1,...,5`.

Now assume the underlying last three blocks `U_3,U_4,U_5` have the same one-hot label, as in a proposed `H,H,H` source pattern. Their terminal indicators agree. Both observed shifted blocks `N_4` and `N_5` therefore have population exactly one, contradicting the even-population condition. This proves that the six-block output cannot have every digit even, for either possible initial borrow.

Only one equal terminal-status pair among the indicated five pairs is needed. The stronger three-equal-label premise makes the two offending shifted blocks explicit and avoids any reliance on the unspecified predecessor block.

## Bounded corroboration and scope

A fresh, independently written inline checker exhaustively tested radices `4,6,8,10`, block lengths `3,...,8`, every positive block that is a sum of two one-hot vectors, every negative binary block having at most two ones, and both incoming borrows. All **23,984** local cases were evaluated. Each of the **704** all-even cases had zero outgoing borrow and zero borrow entering its final digit. Cases with zero incoming borrow also obeyed the stronger local classification: negative population zero forces a single positive digit two; negative population two forces `P=N`. The checker separately verified the shift-population and alternating-indicator identity for all **796** underlying label pairs across these radices and lengths. These finite checks only corroborate the quantified proof above.

This note does not establish that any particular compiler supplies these blocks, their order, a binary incoming borrow, or this subtraction with no additional terms. Those source-binding obligations remain separate. No predecessor or archived code was executed or imported, and no repository or Git mutation occurred. Only the fresh bounded digit checker ran; no compiled histories or large arithmetic witnesses were constructed.

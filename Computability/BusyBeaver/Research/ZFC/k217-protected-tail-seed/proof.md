# A protected-tail seed theorem for the exact candidate scheduler

## Result and scope

At a complete source-command root with `np = 0` or `np = 1` and `pl = 0`, the usual enumerator can be started with **any natural theorem-stack code**, provided its current formula `tw` and cache `h` are derivable. The additive parameter `d` is arbitrary. Its execution never reads the initial stack: every NIP pops a formula pushed subsequently. The abstract halting/refutation equivalence therefore holds for these seeds without assuming `Good ws` for the initial stack.

This is an ordinary all-natural combinatorial proof about the exact scheduler in `Enum222.lean`, not a new Lean result. The finite independent arithmetic check described below is supporting evidence only. Application to a binary table still requires a correct whole-source simulation and an actual finite startup/AX transport. In particular it does **not** repair the separately recorded relay runtime failure.

## 1. Exact schedule, including nested proof lists

Let `P(x,y) = (x+y)(x+y+1)/2 + y` and let `f(n)` be the second component of `unP(n)`. On a candidate `n = P(t,y)`, the first command has tag `t`:

- `t=0`: MP, conservatively assigned stack change 0;
- `t=1`: DROP, change +1;
- `t=2`: NIP, change -1;
- `t>=3`: AX, change +10.

The MP lower bound is valid in both branches: a successful MP pushes a zero, while failure preserves the stack. AX always pushes the old current formula, the generalized cache, and eight native rows. The bundle gate affects the new current formula only and never changes this stack count.

For the first three tags, the remaining proof-list pointer is `r=f(y)`; for AX it is `r=f(f(f(y)))`. If `r=0`, the candidate is finished. If `r>0`, the next packed command is `r-1`, because `fetch` reads `pl-1` without advancing `np`. Thus define the finite command word

`W(n) = [first command of n] ++ (if r=0 then [] else W(r-1))`.

Each suffix index is strictly less than `n`: `r <= y <= n`, and the subtraction is by one. Hence `|W(n)| <= n+1`. Every prefix of `W(n)` has conservative balance at least `-(n+1)`. In particular a suffix `W(r-1)` loses at most `r` units in any prefix.

A nonhalting run from `np=0,pl=0` follows `W(0),W(1),W(2),…` exactly. A nonhalting run from `np=1,pl=0` omits only `W(0)`. There is no resetting of the working stack between candidates. A halting run follows a prefix of this same schedule.

## 2. Prefix-sum preservation under unpairing

For a sequence `g(0),g(1),…`, suppose every finite prefix sum is nonnegative. Then the same is true of the sequence `g(f(0)),g(f(1)),…`.

Indeed, the sequence of second coordinates on successive complete Cantor diagonals is

`[0], [0,1], [0,1,2], …`.

A finite initial segment is a concatenation of such complete lists and one partial list `[0,…,k]`. Its sum is a sum of nonnegative prefix sums of `g`. Repeating the argument three times gives the same statement for `g(f³(y))`.

The finite form only needs the prefix-sum assumptions up to the largest argument used. This matters below: on diagonal `s`, all relevant arguments are at most `s`, and the already established candidate prefixes through `s-1` suffice.

## 3. Every schedule prefix has nonnegative conservative balance

Write `b(n)` for the complete balance of `W(n)` and `B(N)=sum(n=0..N)b(n)`. We prove, successively by complete Cantor diagonals, that every command prefix of the concatenated words has nonnegative balance, and hence that all the `B(N)` are nonnegative.

The first three diagonals, `n=0..5`, have words:

| n | command word | complete balance |
|---|---|---:|
| 0 | MP(0) | 0 |
| 1 | DROP(0) | 1 |
| 2 | MP(1) | 0 |
| 3 | NIP(0) | -1 |
| 4 | DROP(1) | 1 |
| 5 | MP(0), MP(0) | 0 |

Their global cumulative balances are `0,1,1,0,1,1`; all within-word prefixes are nonnegative globally.

Now consider diagonal `s>=3`, namely candidates `P(s-y,y)` in the order `y=0,…,s`. Its first `s-2` candidates (`y=0,…,s-3`) begin with AX. The last three begin with NIP, DROP, MP, in that order.

Put `g(0)=0` and `g(r)=b(r-1)` for `r>0`. For `t<=s`, its prefix sums are `0` at `t=0` and `B(t-1)` otherwise. These are already nonnegative: `s-1 < P(s,0)` for `s>=3`. By section 2, every initial sum of the AX suffix balances `g(f³(y))` is nonnegative. Consequently the balance of the first `k` complete AX words in this diagonal is at least `10k`.

During the AX word at position `y`, its first command adds 10, and any suffix prefix loses at most `f³(y)<=y`. Relative to the start of the diagonal, the balance is therefore at least `10y+10-y = 9y+10` after its first command; before it the bound is `10y`. Both are nonnegative.

After all `s-2` AX words, the relative balance is at least `10(s-2)`. The following bounds account for each of the last three whole words and every prefix within it:

- NIP at `y=s-2` costs at most `1+(s-2)`, leaving at least `9s-19`;
- DROP at `y=s-1` adds one and its suffix costs at most `s-1`, leaving at least `8s-17`;
- MP at `y=s` adds at least zero and its suffix costs at most `s`, leaving at least `7s-17`.

These bounds are positive for `s>=3`. At the start of any such word, the preceding bound is also nonnegative. The diagonal starts with an already nonnegative global balance, so every global command prefix is nonnegative. This completes the induction.

Finally, `W(0)` has conservative balance zero and no negative prefix. Omitting it leaves the same result for `np=1`.

## 4. Soundness with an arbitrary untouched tail

Fix the arbitrary initial natural stack code `S`. Represent the current stack as `pushL L S`, where `L` is a finite list of derivable formulas. Initially `L=[]`; initial `tw` and `h` are assumed derivable.

Every successful MP pushes truth; a failed MP leaves the stack. DROP pushes the derivable current formula. AX pushes ten derivable entries, since its old current formula and cache are derivable, GEN applies to the cache theorem, and all eight rows are axioms. The new gated bundle is a theorem or truth. These are precisely the existing command soundness facts, restricted to the explicit prefix list rather than to the whole tail.

The length of `L` is at least the cumulative conservative balance. More precisely it equals that balance plus the number of extra zero pushes caused by successful MP. Before any NIP, the conservative balance is at least one: NIP has delta -1 and the balance after it is nonnegative by section 3. Thus `L` is nonempty whenever it is popped. Its head is a theorem, and the arbitrary tail `S` is never inspected. The natural pairing zero alias causes no problem: `unP(P x z)=(x,z)` still holds, including `P(0,0)=0`, so a conceptual leading zero can be tracked even when its numeric encoding coincides with the tail.

If a NIP halts, its current cache equals falsum and is derivable. Hence halting implies a native refutation. This proof does not assume consistency while establishing the invariant.

Conversely, the usual block compiler and cofinal `START_U` family give halting from every initial working tuple when a refutation exists. Their proof is independent of initial stack theoremhood. It permits arbitrary `tw`, `ws`, `d`, `h`, and any finite cutoff `np`: `START_U` resets `d=h=0`, and the subsequent proof block runs above the retained tail or halts earlier. Thus for the protected-tail seeds in section 4, halting is equivalent to refutability.

## 5. Application to the interrupted relay AX

The observed physical frame at ordinal 148 has logical registers

`[np,tw,ws,ac,d,h,s1,s2,pl] = [1,9,0,2,0,1,0,2,0]`.

Reflection's independent trace reader checked 629 source transitions to ordinal 161 with `[1,2,67,2,0,1,0,0,0]`. At this point `h=1` is still bad. The value `2` in register 3 is `ac`, not the cache. **No sound-seed theorem is applied at this intermediate state.** The decoded stack `67` is `[Q_0(F),F]`, since `P(10,1)=67`, `P(1,0)=1`, and `Q_0(F)=10`.

The retained ordinary `L2Axioms219.e305` suffix contract clears the cache and additive/scratch registers, pushes eight row instances above this existing pair, and returns to the command root. Its final logical tuple is

`[1, gate(0,1,2), pushL([rho1(0,1),rho2(0,1,2),…,rho8(0,1,2,0),Q_0(F),F],0), 0,0,0,0,0,0]`.

The first tuple component is `np`, and the last is `pl`. Since `2!=0,1`, the current formula is the literal gated bundle at `(0,1,2)`, hence a theorem; cache is truth0. The stack tail is indeed not `Good` in the ordinary invariant, but section 4 permits this entire initial stack as an untouched tail. The complete AX has ten outputs; the suffix from ordinal161 adds only the eight rows because the generalized cache and old current formula have already been pushed.

This gives a new ordinary sound-seed route **conditional on the exact complete AX/source transport**. It does not assert that the bounded million-instruction continuation has reached that root, nor that the relay table correctly implements the source (its full runtime checker currently fails). The accepted primary218 source differs from the maintained `Dag219` word by inherited all-natural commutations/reassociations; the retained macro correspondence is an ordinary proof boundary, not a freshly compiled literal transport theorem.

## Supporting bounded check and provenance

`check_schedule.py` independently reconstructs only the exact command schedule and conservative balances from natural pairing. It invokes no delivered scripts, binary/source interpreters or proof compiler. Its saved `schedule-check.json` checks all 100,001 candidates `0..100000`, their suffix descent and every within-candidate prefix via recursive summaries, plus three finite prefix-sum transforms. These finite results are not used as a substitute for section 3's induction.

Source interfaces read in full or at the relevant complete declarations: `Enum222.lean` (`axStack`, `cstep`, `pack`, `fetch`, `execAt`, `enumStep`, `step_pl`, `step_start`, `drain`, `Inv`, `axStack_good`, compiler contracts), `Code254.lean` (pairing/code definitions), `L2Axioms219.lean` (`e305`), Source146 `general_seed_lemma.md`, and the exact frozen relay-seed review. The author did not run the relay, source continuation, or Lean.

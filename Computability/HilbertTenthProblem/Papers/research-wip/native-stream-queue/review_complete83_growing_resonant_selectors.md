# Independent review: growing resonant selectors

**PASS; no correction requested.** I independently read and challenged the complete frozen proof and read its entire helper as inert text. The shifted search proves simultaneous divergence and subpower growth of the selector quotient while preserving the earlier odd-scale construction. The proof keeps the doubled positivity threshold explicit and does not assume the unresolved binary condition.

## Frozen author bytes

| File in /tmp | SHA256 |
|---|---|
| complete83_growing_resonant_selectors.md | c005748a280f385c0278e6bfbf4c9f465e924ef9687ad773031d97d3a5760e15 |
| complete83_growing_resonant_selectors.py | 62f3a6750357f593f809f74fad63fae4fb7b716dc28a36333a32898f7b802d57 |
| complete83_growing_resonant_selectors.json | 141d51917d28d4ead733e722f0e466383d780ca130cb09222273d7f531e36718 |

A fresh read-only metadata check authenticated these three pins, the receipt's binding to the helper, all six dependency bytes and lengths, and all13 recorded outer-index rows against the inert actual83 JSON. It did not execute the source array or any author or predecessor helper.

## Mathematical challenge

1. **The exact residues are correct.** Modulo A=odd(q), the source gives `R=MC*J+z` and `mJ=-1`, hence `A|(R+1)` is equivalent to `mz=-Dmask`. In the plus shape A=Q+1 is2 modulo m, and in the minus shape A=2Q-1 is1 modulo m; m is odd, so the inverse exists. Direct substitution gives the author's plus representative `Q-(MC/2)rep` and minus representative `2Dmask*rep`. Both lie strictly between0 and A. The evenness of MC justifies the integer half in the plus formula. Thus every positive resonant z has the stated unique nonnegative quotient h_sel; this is not a free new coordinate.

2. **Shifting the search retains the congruences and pays the size factor.** The inclusion-exclusion lemma applies to every translated interval. On j=1,...,L, the affine quotient's slope remains a unit at all primes of A_out, since that set is disjoint from the primes supporting Cextra and from2,5. At the fixed prime set S, the stronger congruences already impose exact depths; they are preserved by the step M. Thus a successful shifted index restores all exact depths. From `0<z0<=M`, one obtains `M<z<=M(L+1)<=2ML`, including N=1,L=1. Since z_A>0 and z0 is positive in its residue class, `h_sel>=M/A=m0*g*Cextra` and `h_sel<2m0*g*Cextra*L`. No unshifted selector bound is silently reused.

3. **The three-adic lower bound supplies actual divergence.** On the plus subsequence n is a power of9, so D is divisible by3 and v3(D-1)=0. LTE gives `3^a3=3^v3(B+1)*n>=3n`. On the minus subsequence, `D+1=(d+1)v` with v a power of9, so v3(D)=0 and `3^a3>=3v`. In both cases e3=2a3. Using `v=(dn+1)/(d+1)` in the minus branch gives precisely the uniform quadratic lower bound(13). This holds for every successful shifted index, rather than depending on an additional favourable choice.

4. **Positivity and the odd input budget survive together.** The5-free interval comparison gives L no larger than the old square-root search length. Hence z<=2Zbound, and the explicitly doubled inequality(14) implies S0>q/2 for the chosen x0. The positive source-coupled bounds then establish R>u and positive quotient arguments before the carry theorem is invoked. The exact depths give at least a_p central carries outside S and at least3a_p at S. The old estimate `A_S^2>6ell` therefore still bounds `ell*Hreq<q/2<S0`; every necessary CRT representative fits the actual positive input interval. Neither transport nor the fixed compiler ports change when that input representative is selected.

5. **The upper and lower statements are compatible.** The exact Euler product bounds L by `C_epsilon*N^epsilon+1` for every epsilon>0. Because `g*Cextra=O(n^3)` with compiler-dependent constants, the quotient obeys `h_sel<=C'_epsilon*n^3*Q^epsilon`. Exponential growth of Q absorbs the polynomial for each fixed epsilon. Together with the quadratic lower bound, this proves both `h_sel -> infinity` and `log(h_sel)/log(Q) ->0` along the same chosen subsequence. The conclusions for z and F remain upper bounds; the proof does not assert z/Q tends to1 or add a matching asymptotic lower bound.

## Read scope and inherited premises

The following pinned dependencies were authenticated. The four mathematical family/lifting/bound notes were read in full in this review or the directly preceding proof work. Modified75 Section1 was read for the literal fixed masks and powers-of-five recipe. The actual83 JSON was read as data for its interface and the13 literal outer rows; its full circuit, native/Pell inverse and compiler theorem are inherited rather than re-audited here.

| Dependency | SHA256 |
|---|---|
| complete83_fixed_prime_quotient_carries.md | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| complete83_subpower_selector_bound.md | 3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4 |
| complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |
| complete83_nondyadic_outer_family.md | 42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23 |
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |

The helper and receipt correctly distinguish their36 relaxed residue cases,6,582 shifted affine intervals,2,592 endpoint cases and18 modular three-adic cases from authentic compiler instances. I inspected their definitions and scope as text; I did not rerun them or add numerical proof corroboration. Author-reported normal/-O passes are author evidence, not executions by this reviewer.

This is a bounded independent proof review. Only fresh metadata code ran; no supplied, committed, archived, frozen or copied predecessor/author program was executed or imported. No source array, half-binomial value or Pell tuple was evaluated. The result preserves odd-scale completion and supplies selector growth; a binary theorem and the inherited full-completion argument must be combined separately before concluding anything about full positive zeros. No universal83 or language-soundness conclusion is certified here.

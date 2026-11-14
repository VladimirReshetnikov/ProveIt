# Independent check of the bounded-input compiler proof

## Verdict

The bounded-input proof in `ax11h_preservation.tex` is mathematically sound for the explicitly defined abstract command evaluator, under the stated primitive-recursive coding and local command equations. It does avoid induction on an unbounded universal-store predicate. It does not establish physical-table simulation or PA-to-calculus calibration.

## Why the bound works

Fix one entire proof list e with N lines and one normalized input store code s0. All compiled words W_j are constructed bottom-up first. Their lengths and command codes are therefore fixed primitive-recursive data depending on e, independently of the runtime store. Let L be their maximum length and K the maximum command code.

The one-command store bound Phi_K(s)=1+max(s, max_{c<=K,u<=s} next(c,u)) is primitive recursive, monotone, and dominates every command in every W_j on every store bounded by s. Halts are totalized and absorbing. Every prefix of a W_j has length at most L.

With B(j)=Phi_K^(L*(N-1-j))(s0), an earlier premise i<j has B(i)>=Phi_K^L(B(j)). Thus every actual invocation of W_i made during W_j on a store bounded by B(j) is inside W_i's induction domain. The prefix may include execution of a different premise word; its entire length still is no more than L. If that prefix halts, the desired disjunct already holds and no later invocation is needed.

At the final line the bound is exactly s0, which suffices for the chosen initial store. Since s0 was arbitrary, universal generalization gives the all-store theorem.

## No hidden quantifier in the induction

The induction invariant is the primitive-recursive Boolean:

    for every line i<j and every numeric store u<=B(i),
    if u is normalized then evaluation of W_i at u halts or
    returns the specified conclusion with its underlying stack preserved.

Both bounded universal checks are finite Boolean folds. The word evaluator is a fixed primitive-recursive function; its output test is primitive recursive. Thus the induction formula is an equation between primitive-recursive terms.

The use of bounded quantifier notation can be eliminated within iPRA. Bounded elimination (a Boolean all-check implies the selected matrix) follows by quantifier-free induction with the selected index as a parameter. Bounded reconstruction follows by quantifier-free induction on the partial Boolean fold, with the bounded universal premise held fixed. No induction on an unbounded quantified formula is being smuggled in.

The proof-list checker is Boolean too. It verifies earlier-premise indices and exact numerical rule equations; no arithmetical truth predicate or reflection principle occurs. Code-zero aliases are handled by the local command contracts.

## Necessary limits

1. The construction works because W_j is compiled independently of the runtime store, giving the store-independent L. It does not automatically apply to every recursion with changing parameters, or to an upstream compiler whose termination/size bound has not been supplied.
2. `next` here is one abstract arithmetic command. Its being primitive recursive does not verify a physical register/Turing implementation.
3. The scheduler bound counts abstract commands. Physical macro costs require their own primitive-recursive bounds and exact simulation equations.
4. Soundness annotations check proofs in C4 or C4Q, not proofs in PA. Converting them to PA refutations still uses the separate calibration.
5. The result is an ordinary written iPRA argument. No new machine-specific Lean or Rocq endpoint has been compiled.

## Command checks actually rerun

The adapted free-term checker passed on both generated emitter grammars. It verified the optional sixth-head exchange, all eleven stack entries, no-push MP, cached-only Shift source shape, four-field AX decoding, selector indices, generalization at arbitrary parameters, MP early halts, and the Cantor zero aliases. Pop halts at preserved top 1; a final plain Shift does not detect top 1 with cache 0. The correct universal halting suffix is Pop.

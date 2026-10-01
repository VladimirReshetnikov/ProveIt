# Source ledger and attribution

Inspected 30 September 2026. This ledger records a bounded audit, not a comprehensive priority search.

## Repository baseline

ProveIt revision: `b8b0fa2184a044d46ce9ed0f25f88d7bb60fa042`.

https://github.com/VladimirReshetnikov/ProveIt/tree/b8b0fa2184a044d46ce9ed0f25f88d7bb60fa042/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/constrained-crossover-closure

Read `README.md` and `article.tex` through the GitHub connector. In particular, separately retrieved:

- The corollary **Decidable regular-input stabilization**, giving an EXPSPACE DFA upper bound and explicitly not claiming optimality.
- The Section 11 question **Sharp regular-input complexity**, asking for the exact DFA/NFA complexity and a better algorithm exploiting two-sided subset structure.

Credited existing results: aligned fragment rank, parallel rank threshold `2^k`, frozen-source threshold `k+1`, coordinate hull, and the relation of finite stabilization to bounded rank. The delimiter amplifier is also credited as an existing mechanism; its NFA hardness specialization is provided for comparison.

The broader reports index and the insertion-degree sibling README were examined when choosing the topic. The present article does not assert that the both-singleton insertion conjecture is solved.

## Primary external sources

1. Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1, 27 August 2026.
   https://arxiv.org/abs/2608.27755v1
   Used for the exact constrained-crossover definition and surrounding problem setting. The earlier ProveIt report already addresses its context-free one-step question; that result is not claimed anew.

2. Anthony Widjaja To, *Unary finite automata vs. arithmetic progressions*, Information Processing Letters 109(17) (2009), 1010–1014. DOI: 10.1016/j.ipl.2009.06.005.
   https://arxiv.org/abs/0812.1291
   Imported: corrected Section 3 arithmetic-progression representation, with singleton exceptions at most `2m^2+m`, positive periods at most `m`, and progression starting terms below `2m^2+2m`. The correction's PDF pages 4–5 were visually inspected. The article normalizes each unary path problem with two extra states and a length shift by two, then uses the safe common threshold `T_s=2(s+2)^2+2(s+2)` and period `lcm(1,...,s+2)`.

3. Jui-Yi Kao, Narad Rampersad, Jeffrey Shallit, *On NFAs Where All States are Final, Initial, or Both*, Theoretical Computer Science 410(47–49) (2009), 5010–5021. DOI: 10.1016/j.tcs.2009.07.049.
   https://arxiv.org/abs/0808.2417
   Imported: Lemma 6 in version 2, binary all-initial/all-final NFA nonuniversality is PSPACE-complete. Its PDF page 7 was visually inspected. Universality has the same completeness by complement closure. The two-unary-loop crossover reduction is proved in the new article.

4. Walter J. Savitch, *Relationships between nondeterministic and deterministic tape complexities*, Journal of Computer and System Sciences 4(2) (1970), 177–192. DOI: 10.1016/S0022-0000(70)80006-X.
   https://www.sciencedirect.com/science/article/pii/S002200007080006X
   Imported standard space simulation. The new article also explains the configuration-graph midpoint recursion used in this application.

## Search boundary

Queries included constrained crossover + PSPACE, crossover + finite stabilization + automata, recombination + regular languages + closure, unary arithmetic progressions, and all-initial/all-final NFA universality. Broad searches were noisy. No claim is made to have excluded every equivalent theorem in recombination, symbolic dynamics, or semigroup theory.

The asserted contribution is a proved extension relative to the pinned repository baseline. The article is not peer reviewed, and its theorems are not formally checked.

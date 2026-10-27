# Independent review of the conditional degree-preserving kernel target

Reviewed `research_runtime/CONDITIONAL_DEGREE_KERNEL.tex` against the source Appendix D proof. The implication is algebraically sound under the stated new interface, subject to making integer parameters and description-independent branching explicit:

- Fix integer size parameters s and K with s/log(s) <= K <= s.
- Replacing the Hermite degree parameter by K gives h=ceil(3K/u) and normalization/jet precision increments O(KD/u + K log(s)).
- Along active paths M>H, with H=ceil(sqrt(sK/log(s))), depth is O(loglog(s)) and u grows at least as a constant times (log(s))^(2/3). The extra 2^u factor absorbs inherited polynomial-log precision overhead, yielding p_t=O(KD/u).
- The hypothesized cM/D modes per weight then give exp(O(sqrt(MK/u))) branches. This exponent decreases geometrically by 1/2 per depth when M decreases by 1/8 and u by 1/2.
- Leaf cost exp(O(H)+O(s^0.9)) is within exp(O(H)), because H>=s/log(s).
- The number of nodes/evaluations/groups per call must be polynomial in s independently of the initial description length L. Local per-call work may be polynomial in s+L. This distinction preserves a fixed polynomial in description length rather than L raised to O(loglog(s)).
- M<K at a deeper active call is not a problem: the recovery lemma, with degree parameter K, needs K>=u, not K<=M.

For s=Theta(n loglog(n)) and K=Theta(n), the conclusion is exponent O(n sqrt(loglog(n)/log(n))), a sqrt(loglog(n)) improvement over the paper's general-density upper bound. It does not improve the paper's fixed-density exponent.

No new encoded class satisfying the interface has been constructed. In particular, low degree in incidence-selection variables does not imply low degree in a binary combinatorial rank code; mode multiplicity must scale with compressed wires, not original incidences; and recursive child closure is essential. This review certifies neither the missing interface nor a faster 3SAT algorithm.

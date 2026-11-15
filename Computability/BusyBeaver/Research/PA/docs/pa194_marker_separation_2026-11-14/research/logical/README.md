# Additional source and grammar reduction experiments

These are unsuccessful, explicitly bounded experiments performed against the pinned ProveIt snapshot `793c68737d94bffa4e32a75bce6cc8058d6d22f0`. They contribute no new accepted machine with fewer than 194 states and no additional proved 194-state consistency machine. The positive baseline is the existing PA194AX11G source and raw table.

## Reproducible finite screens

Run `python3 -B replay_prices.py` from this directory. The archive freezes all 4,222 scored trees, their exact expected prices, the baseline literal rows, and the small inherited compiler. The completed replay is `recorded/finite_replay.json`. The input list has a mixture of controls, semantically justified proposals, and proposals whose completeness has not been established. It must not be interpreted as a collection of accepted consistency machines.

For each tree, the checker counts the 134 fixed controls (136 in the coefficient-seven experiment), interns the AX reader pairs, and subtracts a maximum disjoint matching of available local contextual fold opportunities. That subtraction is an **optimistic price**. The finite-screen checker does not assert that every matched fold can be applied simultaneously, that every source path is executable, that the blank startup is correct, or that the changed command protocol is complete. Timed searches use a stronger simultaneous two-cell fold check near the frontier, but still require the missing complete source, startup, and logical verification before nomination as a machine.

| Finite screen | Cases | Minimum optimistic price |
|---|---:|---:|
| Existing AX11G control | 1 | 194 |
| Double negation of guarded top, including repeated variants | 8 | 196 |
| h3/h4 antecedent exchange on fixed AX11G shape | 108 | 203 |
| h3/h4 exchange on 1,191 distinct historical 190-token shapes | 3,573 | 200 |
| Generalization at a negative-code binder: all Catalan prefix associations | 429 | 197 |
| Additive binder c+d: two evaluation orders, all Catalan prefix associations | 84 | 197 |
| Coefficient seven with a shared triple-increment equality tag | 8 | 204 |
| Implication-only terminal contraction, completeness unproved | 1 | 195 |
| Visible-top generalization after deleting the saved-top copy, completeness unproved | 10 | 194 |

The 108 exchange cases are three nonempty choices of the two exchanged heads times six independent variable permutations in each head. The 3,573-case sweep applies three exchange patterns to 1,191 distinct parsed historical shapes. Each historical input has its source-relative path and SHA-256 retained inside the compressed case list. This is a sweep of these recognized 190-token grammars, not all programs in the repository.

The negative-binder prefix has eight leaves, hence Catalan(7)=429 associations. The additive-binder prefix has six leaves, hence two times Catalan(5)=84 associations. These arithmetic counts are exact; the subsequent state prices are compiler results.

## Timed grammar searches

`timed_summary.json` records completed runs, and the full logs are retained under `recorded/`. The C++17 programs and exact input templates are included. Each run was given 600 seconds, with the recorded fixed PRNG seed. The number of iterations in a rerun depends on machine speed, so elapsed-time replay is not a promise to reproduce the final iteration count.

The original reassociation search rotates a selected shared binary subtree. The joint variant additionally permutes the parameters of the six independent theorem heads, uses an adaptive pool, and uses a modestly larger annealing temperature. Structural penalties discourage source paths that exceed the inherited scanner constraints. The radix-seven variant also permits native controls 41 and 99 in the finite contextual-fold matching, because the inherited coefficient-five/six constructions use that additional fold.

Example reruns, from this directory:

```sh
c++ -O3 -std=c++17 code/search.cpp -o /tmp/pa-search
/tmp/pa-search inputs/nn_templates.txt inputs/leaf_attrs.txt /tmp/pa-nn 600 202611141753
/tmp/pa-search inputs/exchange_templates.txt inputs/leaf_attrs.txt /tmp/pa-exchange 600 202611141822
c++ -O3 -std=c++17 code/search_joint.cpp -o /tmp/pa-joint
/tmp/pa-joint inputs/exchange_templates.txt inputs/leaf_attrs.txt /tmp/pa-joint-run 600 202611141833
c++ -O3 -std=c++17 code/search_radix7.cpp -o /tmp/pa-radix7
/tmp/pa-radix7 inputs/radix7_templates.txt inputs/radix7_leaf_attrs.txt /tmp/pa-radix7-run 600 202611141852
```

## Mathematical scope and attribution

Exchanging the antecedents of `A -> (B -> C)` is justified by the same finite restricted-rho/MP exchange theorem used by the existing Q family. This observation is **not new**: the pinned `pa194_sel_ax11gh_research_2026-11-14` packet already reports searches for h3, h4, and joint exchanges, with best objectives 196, 196, and 199 respectively. The contribution here is the additional fixed-shape and historical-shape screens and the explicitly recorded fresh runs, not discovery of antecedent exchange.

Replacing a valid guarded theorem by its double negation preserves derivability in the classical numerical calculus. The emitted guarded top is replaced after the guard; even the guard-failure truth branch becomes double-negated truth. This semantic fact alone does not supply the changed physical table or compiler. The current search objective remained 196.

The additive-binder proposal saves `U(c+d,h)` instead of `U(c,h)`. The source preserving-copy tails add one input register to the visible top, and the ordinary generalization compiler would still choose d=0. The initial prefix price was 197. This is a source proposal with straightforward intended semantics, not a verified machine at that price.

The negative-binder proposal saves `U(N(c),h)` for `N(c)=I(c,1)`. There is an interesting possible restricted-generalization compiler: rename proof variables into the range of N; the fresh property label in the pointed-separation argument is already a negation code; and use a double-negated equality formula when a fresh neighborhood label is needed. A complete proof would still have to establish the internal proof translation, all exceptional label and contradiction-target cases, a primitive-recursive bound, and the command/tape correspondence. None of those missing obligations is asserted complete here.

Deleting the initial saved-top copy can preserve a 194-state optimistic price, but changes the cache-generalization interface and removes the exact old-top save used by the established Push/Pop words. The prior total cleanup proof consequently does not apply. These rows are retained as **unproved research inputs**, not successful fallback machines.

No finite screen or timed search gives a lower bound for arbitrary 193-state consistency machines, for other instruction encodings, or for unexplored initializers.

The inherited compiler, symbolic helper, and licensing notices are in `reference/`. `PROVENANCE.json` gives their origin and byte hashes. No inherited arithmetic-box oracle is used by the optimistic price replay: that replay only examines literal transition rows and grammar shapes. It also does not prove any arithmetic-box lemma.

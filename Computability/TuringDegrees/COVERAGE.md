# Coverage of the Turing-degree article

This ledger tracks the mathematical claims in the
[13 May 2026 revision of the Wikipedia article](https://en.wikipedia.org/w/index.php?title=Turing_degree&oldid=1353991718).
“Lean” means a theorem in `Lean/TuringDegrees`; “Rocq” means a theorem in
`Coq`, sometimes specialized from the pinned
`coq-synthetic-computability` development.  A conditional theorem keeps every
effective-enumeration, encoding, or logical principle as an explicit
parameter.

| Article claim or notion | Lean | Rocq |
| --- | --- | --- |
| Set Turing reducibility by a characteristic oracle | `SetTuringReducible` | `turing_reducible` |
| Turing equivalence is an equivalence relation | `setTuringEquivalent_equivalence` | `turing_equiv_Equivalence` |
| Degrees are equivalence classes and form a partial order | quotient `SetTuringDegree`, `instPartialOrder` | setoid equality/order, `turing_degree_PartialOrder` |
| All computable/decidable sets have the least degree `0` | `of_eq_bot_iff`, `instOrderBot` | `empty_set_least`, `all_decidable_sets_same_degree`; converse explicitly assumes `MP` |
| Exact even/odd join formula | `setJoin`, `evenCode_mem_join`, `oddCode_mem_join` | `turing_join_spec` |
| Join is the least upper bound; degrees are a join-semilattice | `join_reducible_iff`, `instSemilatticeSup` | `turing_join_is_lub` and the semilattice laws |
| A set and its complement have the same degree | `compl_equivalent` | not wrapped |
| `0'` is the halting degree and is nonzero | `zeroJump`, `bot_lt_zeroJump` | `zero_jump`, `zero_jump_nonzero` |
| Jump respects degree equality and is monotone | no general jump in Mathlib | `jump_respects_degree_equality`, `turing_jump_monotone` (EPF/encoding parameters) |
| Every degree is strictly below its jump | only `0 < 0'` | `turing_jump_strict`, including iterates (EPF/encoding parameters) |
| Every degree is countably infinite | `cardinal_degreeClass` | not represented as a quotient cardinal |
| There are continuum many degrees | `cardinal_setTuringDegree` | not represented as a quotient cardinal |
| Every lower cone is countable | `lowerDegrees_countable` | not wrapped |
| Every strict upper cone has size continuum | `cardinal_strictUpperCone` | not wrapped |
| Incomparable degrees exist; the order is not linear | notion plus pure-order consequence | `kleene_post_from_epf`, `turing_degrees_not_linear` (EPF and finite-string coding parameters) |
| Minimal degrees imply failure of density | `IsMinimalDegree`, `minimalDegree_not_dense`; existence not proved | `is_minimal_degree`, `minimal_degree_not_dense`; existence not proved |
| Pairs without a greatest lower bound imply failure of lattice structure | `HasGreatestLowerBound`, `no_glb_not_all_binary_infima`; existence not proved | `has_greatest_lower_bound`, `no_glb_not_all_binary_infima`; existence not proved |
| Exact pairs imply no LUB for strictly increasing sequences | corrected `IsExactPair`, `exactPair_no_lub`; existence not proved | `is_exact_pair`, `exact_pair_no_sequence_lub`; existence not proved |
| Low relative to a degree | `SetTuringDegree.IsLowRelative` (parameterized jump) | `is_low_relative` (parameterized jump) |
| Post's theorem / finite jump hierarchy | no general jump hierarchy | `standard_iterated_jump_sigma`, `posts_theorem_sigma_many_one_complete`, `posts_theorem_oracle_ce` (explicit hierarchy hypotheses) |
| A degree is c.e. iff it contains a c.e. set | `SetTuringDegree.IsComputablyEnumerable` | `is_ce_degree` (with representative-level `computably_enumerable`) |
| Every c.e. degree is below `0'` | `computablyEnumerable_le_zeroJump` | `ce_degree_turing_reducible_zero_jump` |
| A set is c.e. iff many-one reducible to `0'` | `re_iff_manyOneReducible_haltingSet` | `ce_iff_many_one_zero_jump` |
| `0'` is c.e.-complete and its complement is not c.e. | completeness in Lean | both clauses in `zero_jump_ce_complete` and `complement_zero_jump_not_computably_enumerable` |
| Shoenfield limit lemma | corrected approximation notion only | `shoenfield_limit_lemma` (restricted excluded middle and definiteness explicit) |
| Corrected two-argument recursive approximation and `n`-c.e. hierarchy | definitions and monotonicity | definitions and monotonicity |
| Friedberg–Muchnik/Post problem: an intermediate c.e. degree exists | not proved | `posts_problem_solution`: c.e. `P` with `0 <T P <T 0'`, under explicit `MP` and the constructive Post-problem principle |

## Deliberate nonclaims

The development does **not** postulate the remaining deep existence and
classification theorems merely to obtain a longer checklist.  In particular,
it does not currently prove minimal-degree existence, density of the c.e.
degrees, jump inversion, continuum antichains, arbitrary countable-poset
embeddings, nonlattice witnesses, exact-pair existence, the r.e.-degree lattice
embedding/nonembedding theorems, or the first-order-theory completeness
results.  Also outside the present scope are incomparable partners for every
nonzero degree; the `V = L` maximal-chain result; infinite antichains inside
each interval from a degree to its jump; relative-low extensions and descending
jump-control sequences; first-order definability of jump; existence of a
non-c.e. degree below `0'`; the article's finer `n`-c.e./weakly-`n`-c.e.
classification results; and its concluding simple-low construction.

Two formulas in the article need care before formalization:

1. A recursive approximation is a two-argument function `g stage input`, and
   convergence is pointwise in the input.  The article's displayed
   one-variable formula conflates the two arguments.
2. The useful exact-pair theorem has non-strict common lower bounds and
   separately says every sequence element lies strictly below both members of
   the pair.  This is the formulation used by `exactPair_no_lub`.

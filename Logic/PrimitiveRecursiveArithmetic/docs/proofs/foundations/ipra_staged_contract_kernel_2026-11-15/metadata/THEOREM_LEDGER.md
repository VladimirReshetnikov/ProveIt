# Theorem ledger

| Result | Human proof | Python | Lean object proof | Kernel checked here |
|---|---|---|---|---|
| Finite-code closure | complete | supporting implementation | plan | no |
| Bounded Booleanization | complete | partial primitives | precise plan | no |
| Least bounded search | complete | implemented/tested | target specified | no |
| Complete bounded enumeration | complete | implemented/tested | target specified | no |
| Instantiation and context alignment | complete | modeled | supplied `Prf PRAAx` proof | no (Lean absent) |
| Proof schedule step | complete | implemented/tested | supplied `Prf PRAAx` proof | no |
| Staged graph compilation | complete | implemented/tested | node compiler supplied | no |
| Loop compilation | complete | modeled by traces | supplied using `PRA.qfInd` | no |
| Acyclic demand soundness | complete | implemented/tested | plan | no |
| Bounded cyclic demand closure | complete | implemented/tested | target specified | no |
| Finite viability and least path | complete | implemented/tested | target specified | no |
| Exact stable-observable erasure | complete | implemented/tested | generic combinator supplied | no |
| Diameter-stable erasure | complete | implemented/tested | plan | no |
| Gap-based exactness | complete | modeled | generic wrapper supplied | no |
| Mixed-radix lexicographic fuel | complete | implemented/tested | plan | no |
| Height-to-list / list-to-height | complete | implemented/tested | plan | no |
| Cardinality is not height | complete | n/a | elementary target | no |
| Cubic bisection bracket theorem | complete | implemented/tested/demo | application plan | no |
| Native export | inherited checked theorem | n/a | wrapper supplied | no new build |

No row marked “supplied” is claimed compiled in this runtime. The final column
will become “yes” only after running Lean in the pinned ProveIt workspace and
recording `#print axioms` output.

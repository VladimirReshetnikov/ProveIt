# Independent review of compiler parity padding

PASS on the frozen mathematical construction and the inspected source interface. No correction was requested. This is a compiler-recipe transformation preserving the ordinary-input language. It is not a bijection between the old and new arithmetic tuples, and it does not modify the frozen parity-dependent small-prime theorem.

## Reviewed inputs

The complete [author note](gamma_parity_padding_scout.md) was read and authenticated at SHA-256 `0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c`. All eight source/proof hashes recorded in its final section were independently matched to the local inert bytes. Its separate small-prime dependency is the revised proof SHA-256 `b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e`.

The following predecessor files were read as inert text; none was executed or imported:

| File | SHA-256 | Read scope |
| --- | --- | --- |
| `../../verification/explore_fixed_raw_universal_76.py` | `011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0` | `compile_windows`, lines 94–148, and adjacent layout verification |
| `../../verification/explore_fixed_raw_universal_78.py` | `10d5ed5809ccaf49b6006cf5758a40ed4f2bd05fed3f4747add3ea4c5d0b1639` | inherited `Compiled` representation, `bits`, `truth`, and constants, lines 72–159 |
| `complete75_half_binomial_compiler.py` | `d6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2` | full file read; wrapper and effective exporter, lines 21–57, are the relevant API |
| `../../1980/FIXED_RAW_UNIVERSAL_80_PROOF.md` | `655128efc0b03d44cd9ba0ba62857ae888e7a583371a40ae3861d4fd521a1076` | exact overlaps and center clauses, then soundness occupancy and positive-completeness passages |
| `../../1980/FIXED_RAW_UNIVERSAL_77_PROOF.md` | `292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41` | Sections 4–5: Start recovery, alignment, occupancy, and subsequent marker uniqueness |
| `../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87` | raw doubled-input interface and Sections 3–4 decoding/temporal soundness |

The modified-compiler proof and exact compiler-parity table were also checked during the immediately preceding [small-prime review](review_complete83_gamma_small_prime_digit_rules.md), which records their pins and the final author theorem. This review inherits the established arithmetic decoder and fresh positive-converse theorems; it does not rerun their historical verification suites or allocate their large fixed numerals.

## API and exact transformation

Start from the actual valid ordered window list, with old Start at selector 0, old End at selector 1, alphabet `range(a)`, and at least two distinct 9-tuples. Choose the least odd `a'>a`; then `a'<=a+2`. Reserve the fresh symbol `*=a`. Keep the entire old ordered list. If its length `k` is odd, append exactly the constant 9-tuple `(*,...,*)`; otherwise append nothing. Thus `a'` is odd and the new list length `k'` is even, with `k'<=k+1`.

The actual `compile_windows` predicates require distinct tuples of length nine, entries in the declared range, and `k>=2`. They do not require every declared symbol to appear. The old list still satisfies these predicates over the larger alphabet. If appended, the all-fresh tuple is distinct from every old tuple, and it leaves selectors 0 and 1 unchanged. When `a` is odd, the additionally unused symbol `a+1` is harmless. No selected old window contains either new symbol, so the linked copy clauses force their copy bits to zero.

The sparse payload, clause coefficients, anchors, dummy positions, radix, cell width, and program numerals must be recomputed by the existing recipe. The modified wrapper still selects its first dummy, enlarges the radix using its actual coefficient bound, and exports the modified native masks through `new_constants`. The source continues to form `MF_source=MF_native+B-1`. Reusing cached old masks or old fixed numerals would not implement this transformation.

## Why no new marked history is admitted

The center clauses alone allow either one selected window with its exact one-hot tile copies, or no selector with all copies zero. They do not assert occupancy in advance. The horizontal copy equalities are imposed at six overlapping physical positions. At any such position an occupied window has a one-hot symbol vector, while an empty cell has a zero vector. Therefore horizontally adjacent occupancies agree.

Horizontal shift by one is a single orbit on the cyclic index set, regardless of the temporal stride or whether that stride divides the length. The origin has the old Start selector after the inherited pre-semantic arithmetic decoding. Hence every cell is occupied. This propagation applies equally to the appended window: it also has one symbol at each physical position.

If the all-fresh window is appended, it cannot be horizontally adjacent to an old window in either direction. Its overlapping entries are all `*`, while every old entry belongs to `range(a)`. A single overlap equality already contradicts such a mixed adjacency. Connectivity of the horizontal cycle makes the window type constant between the two classes. The old Start at the origin selects the old class, so the all-fresh window never occurs.

This exclusion precedes any invocation of the old machine semantics or marker-bijection theorem. Every decoded window is therefore an old window with the original horizontal and vertical overlaps. Start and End retain their selector indices and physical positions. The old marker argument and same-run theorem now apply exactly as before; End remains at distance `2x`, so the ordinary input is unchanged. The argument covers wrap-around edges and does not require a separate rectangular presentation. An unmarked all-fresh periodic word exists when the extra window is present, but it cannot satisfy the required old Start at the origin and therefore is not an accepting marked history.

## Completeness, costs, and the filter consequence

Every old accepting window history is also a history over the padded alphabet and window list. Recompile its cell encoding with the new fixed numerals and choose fresh canonical spatial/time padding and dummy control as required by the existing completeness theorem. The current bounds, five-adic alignment, positive slacks, and positive Pell extension are then those of the newly compiled layout. No claim is made that the old arithmetic witness tuple or old radix can be reused unchanged.

This finite transformation depends only on the fixed old window program, not on `x` or a chosen accepting history. It adds at most two declared tile symbols and one allowed window. It leaves the generic arithmetic source schedule and its operation convention unchanged, while allowing its program-dependent fixed numerals to grow. The note does not charge this as variable-input preprocessing or claim a reduction in those numerals' bit sizes.

Language preservation here concerns the genuine marked compiler relation and the established positive 84-operation representation. It is not a separate claim that the unresolved 83-operation chart has the same language across different numeral slices.

The existing compiler-parity theorem consequently applies to the freshly compiled layout with even `k'` and odd `a'`. The frozen small-prime theorem can then be applied to accepted inputs of this equivalent compiler. Its `d`, `h`, `E`, `Delta`, and period quantities are the new compiler/history quantities. This removes the parity restriction as an existence restriction on the choice of equivalent compiler recipe; it does not strengthen the theorem for every original fixed numeral slice or identify old and new period gcds. It supplies no full bound on the remaining period divisor and no resolution of independent-gamma83.

## Review boundary

No API guard, source-generation, or compiler execution claim is made beyond this direct read of the relevant literal definitions. No universal alphabet was enumerated, no new arithmetic source was emitted, and no accepting Pell tuple was materialized. The proof is the local one-hot/overlap argument plus the authenticated inherited decoder and positive converse. Within that scope, no additional gap was found.

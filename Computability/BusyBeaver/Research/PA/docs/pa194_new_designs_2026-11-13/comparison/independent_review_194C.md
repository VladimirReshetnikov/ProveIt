# Independent review of the cached194 composition

Reviewed `proof_cached.tex`, `build_cached.py`, `baseline_tools.py`, `compiler.py`, `verification/check_cached.py`, `cached_commands.tex`, and the inherited logical calibration fragments in `work/theory/pa194_cached/`. This is a mathematical/code review, not a fresh proof-assistant elaboration or another execution of the full physical runtime suite.

## Conclusion

I found no material logical gap in the new cached-controller preservation argument or in its explicit command compiler. The proof correctly distinguishes the unconditional common-source halting transfer from the inherited ordinary PA consistency calibration. The latter remains a named mathematical dependency; it is not upgraded to a new Lean, Rocq or iPRA theorem by the executable certificates. I did not identify an additional concrete gap in the inherited calibration that must be added to that stated dependency boundary.

One finite evidence issue was identified during review: the first builder version replayed the child startup but inherited the pinned 195C startup while saying all machine-specific facts were independently checked. The author added and freshly executed the parent startup replay: `b.startup(parent, ps[25][0])`, exactly 57,922 transitions, with `parent_startup` retained in the construction receipt. This resolves the wording/evidence mismatch without changing the machine or mathematical proof.

## The preservation theorem

The two tables need not have equal literal source-address bit strings. The relevant relation is equality of ordinal source instructions together with their table-specific canonical frames. The builder compares the complete opcode/register/branch-successor map to the frozen195C map, not merely the 190-token word. The independent checker resolves the supplied site paths in two separate ways and compares their full instruction graph to that pinned map. Every physical source branch is then checked on the 194C literal table, and the parent map is freshly validated as well.

The inverse direction uses a valid bounded determinism argument. If a literal run halted after T transitions but its source had not halted in its first T+1 steps, concatenating the positive physical source segments, following the exact startup, would supply a nonhalting literal prefix longer than T. This contradicts deterministic execution and the absence of outgoing halt rows. It does not require an inverse decoder for arbitrary intermediate tape configurations or assume the source nonhalts forever. All finite trace builders and primitive loop bounds used here are formalizable in PA. The source-frame relation includes the entire register and spare list, so the increment's extra spare block is not lost from the statement.

The seven local folds are checked in the simultaneously modified table. Incoming histories establish each two-cell precondition; retained ordinary rows follow the alias projection. Thus the argument does not add pairwise fold savings without checking their interaction. Dense/native conjugacy is also checked exactly. No state-count claim is inferred from source length alone.

## The cached command interface

The ten-entry AX stack contains nine generated entries followed by the saved top. Shift tests only the old cache. After AX the cache is zero; the first ten Shifts consequently test zero and the nine generated entries, never the saved top. Generated implication heads/gates have residue 0 modulo4 and the universal entry has residue 2, so none can be false code 1. This justifies the exact9/11/10 exponents in Push/Pop/Discard.

Push is total on arbitrary stores, including top 1. Its final MP fails because an implication code of residue 0 cannot equal the universal code of residue 2. Pop deliberately detects preserved top 1 and is not incorrectly claimed total on that value. Discard begins from zero caches, and its two failed comparisons are strict positivity facts, not assumptions that theorem codes are nonzero.

The generalization word is valid even when the input formula is code 1: the Shift before AX tests cache 0, places the formula in the cache, and AX clears it before another Shift can inspect it. The selectors discard the correct number of entries and preserve the original stack. The restricted-head selector enforces its numerical dominance premise with the offset u and parameter a-u; no unrestricted substitution into the dominated schema is assumed.

The modus-ponens suffix needs the dummy zero underneath the two premises. It returns the consequent while retaining the original stack, and correctly halts early if a premise or the conclusion is code 1. The entire calculation remains valid at `pair(0,0)=0`, since it uses total projection identities rather than an injective length annotation. The proof-tree compiler maintains its stated all-top/all-stack invariant. Prepending AX clears both caches and appending Pop detects a refutation, giving a halting word from every incoming store. That all-store property is exactly what the carried-store scheduler needs; the argument never assumes reset between unsuccessful trials.

For soundness, proofs annotate both visible formula registers and the canonical live stack entries. Zero padding uses one fixed proof of code 0. The offset is intentionally unannotated. Successful MP produces a proof of the new cached formula; failed MP produces zero. Shift exposes only a proved formula as its halt witness. This is a proof-transforming invariant and not a forbidden internal truth/soundness principle for PA.

## The inherited logical endpoint

The inherited forward proof replaces equality-vacuity interfaces with reverse membership rewriting and neighborhood equality using numerical code freshness. Its negative-specialization use is membership-only; it does not reintroduce the removed equality-vacuity premise. The coincident-label and bound-variable cases are stated explicitly. The separate/bundled diagonal conversion uses fixed classical propositional templates and a guard-satisfying numerical parameter choice, so the ten-entry source retains the same proof strength after changing its stack protocol.

The reverse proof interprets membership by finite binary membership. Formula-dependent finite comprehension is generated as a syntactic PA proof via the appropriate induction instance; it does not uniformly assert the truth of all input formulas. The constructor alias `I(0,0)=0`, the stack alias, capture avoidance, and the case of coincident source/object labels are explicitly handled in the retained calibration. These are the main potentially dangerous interfaces, and the written treatment is coherent on review.

The report should therefore say: the new unconditional result is the PA-formalizable exact-table halting equivalence with pinned 195C; composing it with the supplied ordinary syntactic calibration yields the stated PA-provability biconditional. It should continue to say that no new complete kernel-checked arithmetic endpoint was produced. A reader who declines to import the supplied logical calibration still receives the fully specified preservation theorem and literal machine, not a purported independently established consistency theorem.

## Inventory conclusions reviewed

The fresh corpus has 36 top-level ZIPs,49 distinct ZIP bodies,606 literal byte forms and437 classified root-free graphs under its declared strict parser. Four194 graph classes consist of three positive manuscripts and one explicit rejected scanner experiment. The only recognized sub194 tables are synthetic six- and nine-state controls. The new cached194 is absent from all four existing 194 graph classes even under arbitrary control relabeling/root change, tape reflection, bit complement, or both. The standalone novelty check also recognizes the old primary194 as its positive control.

The report should preserve the distinction between the three existing 194 graphs, especially the independently found68-reader/eight-fold construction. The current 15 graph classes at 195 divide into six positive main/intermediate manuscript families, three auxiliary implementations/search witnesses, and six rejected diagnostics. The intermediate separate195 in the second194 archive has 3,673 sites by its concrete receipt; the report's isolated diagonal/3,700 row is a clerical discrepancy and is not used in the comparison.

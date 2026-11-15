# Independent review of symmetric witness preservation

## Scope and conclusion

Reviewed the new `symmetric_preservation.tex`, the root report, the exact new source arrays and tables, the literal source-template checker, and the recorded construction/source/physical audits. The review found no substantive defect in the new relative transformation or in its positive-clock iPRA preservation argument. It does not independently reprove the inherited absolute PA calibration.

Two presentation clarifications were recommended to the report author: define a clean scheduler entry explicitly by `A=X=Y=0`, with arbitrary `N,T,W,D,H,L`; and identify `T(0)=57768` as the new child's physical startup clock, while each asymmetric parent has startup `57922`. The author agreed to add both to the release copy.

## Exact source identity

The old literal `instructions.json` and `grammar.tree.json` were read directly from the pinned incoming witness ZIP, independently of the new constructor's assertions. For each pair:

- The entire emitter grammar is identical.
- The old instruction array exactly equals `full_templates(word, symmetric=False)`.
- The new instruction array exactly equals `full_templates(word, symmetric=True)`.
- Every instruction before the Shift entry is identical, including outgoing edges.
- The Shift entry is 3666 for H5X/H5XS and 3672 for JH5X/JH5XS.
- The old Shift tail has 11 instructions and the new tail has eight.
- The removed transfer consists of `dec X`, `inc H`, and the jump back; the subsequent increment changes from `inc X` to `inc H`.

The complete old/new tails and exact hashes are retained in `symmetric_peer_checks.json`. The parent/child site counts are 3677/3674 and 3683/3680. Both child tables have 194 working controls and 194 blocks under ordinary immediate-action bisimulation, supporting the corresponding statement in the root report.

## Comparator identity and step saving

Independently derived the comparator cost from the actual ten-row primitive CFG, rather than relying on its numerical test cases. For input `(H,X)=(u,v)`, each complete joint-decrement cycle costs three instructions. When the two values are equal, the terminal zero tests add two. If `u<v`, the residual X-drain tail gives `3v+2`. If `u>v`, the positive-H/zero-X branch and H-drain tail give `2u+v+4`. Thus

\[
C(u,v)=\begin{cases}3u+2&u=v,\\3v+2&u<v,\\2u+v+4&u>v.\end{cases}
\]

Every unequal branch clears both compared registers and preserves all other registers. The equal branch also has both compared registers zero before its halt exit.

After clearing T and duplicating H into T and X, the old implementation restores H from X and increments X; its precomparison triple is `(T,H,X)=(h,h,1)`. The new implementation increments the now-zero H; its triple is `(h,1,h)`. Both equality decisions are exactly `h=1`. On an unequal result the complete register files agree, and they execute the same stack-pop suffix. When `h=1`, the precomparison triples already agree, so the halted files agree as well.

The old transfer costs `3h+1`; substituting the exact comparator costs gives savings of zero at `h=0`, four at `h=1`, and `2h+4` for `h>=2`. This proves an unbounded source-time improvement without claiming a uniform physical-tape speedup.

## Relative iPRA argument

The clear, duplicate, transfer, and comparator identities have direct quantifier-free counter-induction proofs. The arithmetic source templates and their clocks are primitive recursive: the inverse Cantor pairing is defined by iteration bounded by its numeric input, and the AX word is a fixed finite composition. The new templates preserve the same clean scheduler state for arbitrary carried values, including canonical zero-stack aliases.

The backwards simulation correctly handles a physical or source halt inside a segment. If a machine had halted by time t but the first t+1 abstract states were all nonhalting, strictly positive segment durations would produce a later nonhalting encoded boundary. This contradicts absorbing halting. The needed finite search is bounded, so no unbounded decidability principle or Markov principle is introduced. A whole-tape startup endpoint at a nonhalting state likewise excludes a hidden earlier halt during initialization.

At the physical layer, the proof explicitly interprets the finite symbolic rules as equations and quantifier-free inductions on finite run lengths or list codes. The published affine coefficient maxima dominate each local duration; the positive-decrement parameter is bounded by the original register value. Iterating the primitive source and summing the primitive-recursive durations yields total primitive-recursive witness maps. The source-frame closure checks and evolving spare-file/header components are included, avoiding an assumption that those resources stay fixed.

The absolute consistency corollary is correctly separated from this relative argument. It invokes the exact witness packet and the revised written AX11H calibration. Neither the graph checks, the numerical clock samples, nor the new finite certificate replay is described as an end-to-end proof-assistant check of that inherited arithmetic theorem.

## Evidence boundaries

This review independently reconciled the concrete old/new source transformation, derived the comparator formula, checked the clock argument for intermediate halting, and confirmed the stated candidate counts and ordinary bisimulation sizes. The fresh full literal symbolic replays were inspected through their exact bound receipts; they were not duplicated solely for this review. The full transitive PA proof compiler remains an inherited written mathematical dependency, with its own focused review and unfinished Lean formalization.

> Historical working notes. The main report and the final search receipts supersede interim numerical prices and pending statuses. Some paths below identify the original investigation workspace rather than portable package commands.

# Theory audit and alternative constructions

Pinned repository: `VladimirReshetnikov/ProveIt`, commit
`7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`.

## Completed useful results

1. **Split-gate relative proof.** `agent_gate_relative_proof.tex` gives the
   complete new relative argument, with source closure, exact source identity,
   literal verification requirements, and positive primitive recursive clocks
   yielding both directions in iPRA. It preserves the logical calculus.
   Independently checked for `gate_split_work/candidate`: 3,671 instructions
   identical to AX11H; exactly sites 3523--3571 have changed addresses; old/new
   maximum address length37; initial site25/address1000000 identical; raw
   controls split133fixed+68grammar, sevenfolds gives194. The removed native
   macro entry is221; existing entries196 and217 implement node146/node149.
   No comparison or freshness guard was removed. The parent is separately
   running the stronger oracle-free literal verifier and duration audit.

2. **A sound genuinely different numerical syntax.** `agent_tag_swap/` contains
   `tag_swap.py`, `tag_swap_proof.tex`, parent grammars, twelve output grammar
   seeds, exact token words and source-check receipts. Swap tags2 and3 of
   universal quantification and equality, leaving implication and membership
   tags0 and1 unchanged. The recursively defined code-and-label map is an
   involution fixing0 and1. Mapping labels as well as formulas is essential:
   the diagonal axiom uses one number in both roles. The map commutes with all
   six logical heads, the diagonal head, and the guarded gate. Numerical order
   is not preserved, so restricted-rho transport uses the already supplied
   unrestricted rho8 derivation rather than silently mapping `u <= D`.
   Exact free-term source evaluation passes for AX11H and AX11GDH, including
   cache, fourth operand, all stack entries and scratch registers. Word length
   increases190→202 (15universal constructors gain an increment and3equality
   constructors lose one). Initial pricing by the root found only199states,
   so this is an established logical alternative but **not** a successful
   ≤194machine. Do not present it as one.

3. **Arithmetic proof of physical-relative transfer.** For unchanged resolved
   source program P, literal instruction equations with strictly positive PR
   durations and exact blank startup yield physical halt iff source halt by
   QF induction. A physical halt witness t maps to source witness t because
   cumulative clockT(t)≥t and halt is absorbing; source witnessn maps to
   startup+T(n). This avoids hidden minimization or stronger induction.

## Important proof status distinctions

The pinned PA README expressly says that neither physical iPRA direction is
established in the Lean development. It separates standard finite source and
clock bridges from the missing model-length physical simulation and
PA→numerical proof compiler. Revised AX11H written papers separately claim
an ordinary iPRA proof, decomposed over ten proof components. New machines
inherit this written calibration through a new relative theorem; they do not
complete Lean merely by passing a Python certificate checker.

The scalar `construction/vendor/symbolic_runtime.py` is useful during search,
but it contains an arithmetic register-box oracle. The retained independent
literal verifier derives the four list traversal lemmas from literal rows and
replays all4778symbolic outcomes over arbitrary registers, gaps, and finite
spare lists. The latter, plus endpoint/duration checking, is the appropriate
finite instantiation of the written iPRA soundness argument.

## Exact provenance for the unrestricted-rho repair

`Computability/BusyBeaver/Research/PA/docs/pa194_lcfast_tagged_research_2026-11-14/research/tagged3/recoding.tex`
already explains simultaneous formula/label recoding and why numerical order
cannot be transported. Its rho template refers to
`M6.Logic.RestrictedImplication.rho8All`, source SHA256
`00af59bb2f970f780b834b721cccd06c4ed5b5ee13fbfddb0deb0139b4c62581`.
The fixed generic expansion has68,268rows:32,455primitive guarded-rho rows
and35,813modus-ponens rows. Compressed template SHA256:
`9fd2d5082a97dc051e4b56cb6e705f1d6f4f9bcabe82eff7fcbb954c6d285278`.
Our tag-swap argument preserves the implication constructor, so the generic
template's syntactic subtree bounds are available unchanged. It must be
included or cited accurately if the optional syntax alternative is published.

## Investigated directions that remain unproved or uncompetitive

- Replacing Brouwer's h1 (diamond boxA→A) by modal reflexivityT plus explosionX
  is not justified by normal modal reasoning. K+T+X does not implyB/symmetry.
  I initially considered it but withdrew the proposal. This is not a proof
  that the full numerical calculus fails; it is a warning that the proposed
  transfer argument does not work. Do not claim this is a safe head swap.
- Force a gate property code above both labels, e.g. by numerical padding,
  to eliminate guard comparisons. Propositional padding can give a formula
  equivalent to an arbitrary requested property with a sufficiently large
  code. However the standard completeness proof also needs gate conclusions
  at arbitrary labels and variable transport. I did not complete a
  noncircular translation of that restriction. It remains a speculative route,
  and the successful split-gate construction does not use it.
- Direct top generalization is already studied in incoming AX11HC4 research:
  its simple189-token implementation gives196states; a188-token no-saved-top
  variant has an optimistic195count but an open proof-stack completeness
  argument. Combining it with MP-push would need its own proof and pricing.
- Existing BA/BP/generalized modal-head searches in the14November packet
  reach nominal199states, despite188-token words; shorter source words do not
  imply smaller compiled machines.
- Further safe positive implicational currying of h3/h4 is possible using
  K/S, but was not implemented or priced here. It is not a delivered result.

## Ideas from the other requested trees

- ZFC research supplies applicable physical methods: contextual folds,
  source-tree rotations, macro exposure, register allocation, and exact
  startup verification. These can transfer at the compiler level. Its logical
  consistency calibration is for ZFC; changing that target toPA is substantive.
  State savings from separate packets are not automatically additive.
- DiophantineConsistency optimizes arithmetic representations of consistency,
  including variable and operation counts. Those counts do not directly give
  a small blank two-symbol TM, because evaluation, coefficient construction,
  enumeration and initialization require a priced binary-machine compiler.
- ConciseIPRA gives small presentations of the metatheory. Replacing a
  PA-proof search by an iPRA-proof search changes the target consistency
  statement. Its compact calculus is not itself an unproved shortcut to
  Con(PA); a PA-strength refutation equivalence is still required.

## Files most directly supporting the delivered new design

- `agent_gate_relative_proof.tex` — independent new relative proof fragment.
- `gate_split_work/build.py` — original concrete split-gate constructor.
- `gate_split_work/candidate/{tree.json,nodes.json,sites.json,instructions.json}`
  — source and exact graph used for the independent check.
- `gate_split_work/candidate/{machine.tm,machine.native.tm,raw.native.tm,labels.json,folds.json}`
  — initial194witness literal objects; final optimized winner may supersede it.
- Revised AX11H proof components under
  `incoming_extracted/pa194_ax11hc4_c32_research_2026-11-15/pa194_ax11hc4_c32_research_2026-11-15/references/ax11h_calibration/proof/`.
- Oracle-free engine and two source resolvers under
  `incoming_extracted/PA194ORH_research_2026-11-15/PA194ORH_research/verification/vendor/`.

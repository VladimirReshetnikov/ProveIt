# Audit of the current ConciseIPRA proposals

Pinned repository commit: `fa9d969919315b97796a1dd288f431cd3e41ffca`.
Audit scope: current top-level README, the two incoming archives, and the authoritative specifications/claims of canonical_recursors, initializer_equality, computational_equality, and template_free. This is not a file-by-file audit of all 9,970 Research tree entries.

## Most recent material

Both incoming archives were fetched by the GitHub plugin with base64 encoding and extracted under this directory:

- `ipra_clausal_canonical/`: five-rule, Eq/D-only, successor-seeded canonical R calculus.
- `ipra_scalar_uniqueness/`: replaces literal-equation induction by unconditional scalar iterator uniqueness; proves the scalar bootstrap and full equivalence, but has a larger matched checker.

## Existing reductions that must not be presented as new

| Proposal | Actual reduction | Complete-checker limits |
| --- | --- | --- |
| Clausal canonical, incoming | R successor computation; one-term crossed transport; clause use; paired elimination; one witness-directed paired introduction. Q is D with unused witness coordinate. Clause use unifies hypothesis use and QE. | 3,305 normalized bytes / 946 significant tokens / 1,072 AST nodes / 1,073 gzip-9 bytes. Matched control 3,820 / 1,107 / 1,266 / 1,136. Closed Eq/D goals from empty context. Not a global size record. |
| Computational equality | Raw initialized I syntax unchanged; Refl and Eval replace I0, IS, Tr. Eval has root, zero-computation, and successor-computation cases; source at successor is the whole preceding iterator value. Six total rules. | 3,039 vs 3,121 matched bytes; gzip grows 957 to 966. Accepts arbitrary open native sequents. |
| Initializer equality | Zero-normal initialized I, with independent S. Equality changes only an initializer (including root replacement at zero iteration); ordinary orientation. General congruence uses two IS and two Seed nodes. | 3,979 vs 4,029 bytes. Six rules, no global record. This is NOT successor-seeded R despite the abbreviated top-level README table. |
| Canonical recursors | Successor-seeded R, S(a)=R(0,a;0), zero-counter bodies erased by canonical syntax. Six rules. | Transparent checker 4,611 vs 4,923 bytes; compact guarded profile reaches 516 bytes. Different public contracts must not be conflated. |
| Template-free | Simultaneous root-first exact-subterm replacement of s by t in an equation side. Oversized zero-computation marker recovers arbitrary congruence. | Seven rules; 3,147 vs 3,181 bytes. No compact record or absolute minimality. |
| Scalar uniqueness, incoming | From Gamma |- f(Sz)=h(f(z)), derive f(t)=I(t,f(0);h). No induction hypothesis. Scalar predecessor and faithful equality reflection supplied before pairing. | New checker 3,393 vs induction control 3,322 bytes. Eight rules. Separate 866-byte refinement retains the old calculus and is not a uniqueness checker. |

## Comparison cautions

1. All these packages disclaim absolute simplicity or a universal lower bound. A matched reduction does not beat the current lower envelope.
2. Clausal canonical normalizes by removing all docstrings, then using CPython 3.12.14 `ast.unparse` and one LF. Without docstring stripping the 3,305-byte checker is 3,652 bytes. This environment runs exactly CPython 3.12.14.
3. Its matched control retains restricted two-sided transport and root-reversing QE; the 515-byte gain combines Q removal, clause contexts, and unrestricted one-term transport, holding the variable encoding fixed.
4. The compact 516-byte module and fully validated Eq/D 788-byte profile have different public acceptance contracts from the transparent checkers. A theorem/proof interface must be stated before comparing sizes.
5. New equivalences in these reports are written proofs with finite executable checks, not new Lean/Rocq formalizations. The broader repository contains separate formalizations of earlier layers.
6. Erasing the last computation rule after full normalization does not by itself produce a smaller complete calculus: interpreting every equation atom as false makes the remaining clausal rules sound. No equality theorem follows without a reflexivity/conversion seed. Clausal canonical already states this local obstruction.

## Directions not solved by this audit

- A genuinely smaller complete, validated implementation of the five-rule clausal interface; the incoming report explicitly leaves this open.
- A substitution-stable introduction whose complete checker is at least as small as witness-sensitive DI.
- A mathematical reduction to unary zero-test atoms using faithful equality reflection, with a noncircular bootstrap and complete rewritten equality rules. This is only a direction, not an established candidate.
- Any further arithmetic reduction must go beyond recursion uniqueness itself, since the incoming uniqueness report already closes its predecessor/reflection bootstrap.

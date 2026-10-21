# Smaller K215 proofs and a checked M124 transfer

**Results:** a smaller checked proof of the existing K215 source correspondence,
new Lean and Rocq all-tape equivalence proofs for the existing M124 215-state
machine, and new invariant-based reduction research. **No valid 214-state
machine was obtained.**

Read `report.pdf` or edit `report.tex` for the full argument, candidate comparison,
evidence boundaries, and further research questions. This packet is prepared for
incorporation in ProveIt and is pinned to commit
`e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`.

## 1. A concrete shorter source proof

`source_proof/Source215Simple.v` proves, for every natural-valued register file,

```coq
rm_halts p215 ([], R) <-> rm_halts dagPerm ([], R).
```

It uses the repository's exact program definitions, an ordinary bisimulation
checker, one forward certificate, and a reusable symmetry theorem. All 2,240
offsets in the old certificate are zero, so its signed-offset machinery is
unnecessary for this theorem.

The positive-integer path codec plus compact certificate occupies **173,003
uncompressed bytes**, versus **1,499,170 bytes** for the original certificate:
**88.4601% smaller**. A compiled equality proves that decoding produces exactly
the original ordered certificate. The final definition materializes the expanded
data; compression is in the source representation, not a claimed reduction of
the entire proof object or overall endpoint build time.

The source theorem and certificate identity compile with closed assumptions in
Coq 8.18.0. The exact original dependencies and a proved 8.18 compatibility shim
are bundled. The original 9.1 sources are retained for integration. The recorded
recursive-check scope and interrupted early experiment are explicit in
`source_proof/verification/` and its README. This packet does not rebuild the
whole existing ZFC endpoint.

## 2. The easiest inspected additional 215-state proof

M124 is an **existing** machine from
`DR215_research_2026-10-21.zip`, not a new machine construction in this packet.
The new contribution is its checked short proof in both assistants.

It changes four native rows, merging old roles 124 and 127 at new 124 and reusing
127 as a selector. Only two invariants are needed: the cell to the left is 1 at
old 124 and 0 at old 127. Every old step transfers in one or three new steps with
the same tape and corresponding control. Positive block length supplies the
reverse halting argument.

`m124_rocq/` contains three compiled proof modules, closed assumption reports,
and a successful recursive `coqchk` receipt. `m124_lean/` independently checks
the exact table, its 215 working labels, reachable-state closure, and the complete
halting transfer. Its only reported axioms are Lean's `propext`,
`Classical.choice`, and `Quot.sound`.

The all-tape statements start in control 0 and quantify arbitrary tapes. They
do not claim equivalence from every internal control. M124's calibrated blank
prefix takes **95,840 steps**, compared with K215's **95,714**; the additional 126
steps are exactly twice the 63 exceptional old steps. `checks/replay_marker.py`
checks every synchronization boundary and the complete terminal tape.

These are **table-to-table equivalence theorems**. A formal model bridge or a
direct port to the existing zipper semantics remains before importing the full
repository ZFC endpoint. The ordinary ZFC calibration transfers through the
proved equivalence; this is not advertised as a newly integrated complete
Lean/Rocq ZFC endpoint. The inherited parent proof remains a dependency.

## 3. What the 214-state investigation establishes

`research214/` contains a generated and independently checked finite inductive
invariant over the atoms `{0}`, `{1}`, and `{2,3,...}` for each source register.
It checks 6,170 abstract edges and establishes 4,194 zero facts, including three
unreachable source ordinals and five impossible guarded cases.

Three sound source prunings reduce expanded instruction counts but raise
distinct subtree counts from 202 to 203, 204, or 205. They are not physical state
reductions. A bounded reassociation beam inspected 13,097 trees without improving
the first pruned variant below 203 shared subtrees.

The saved searches cover 947,720 fold specifications across twelve frozen final
tables, and 856 one-row replacements attempting to delete M124's selector. No
candidate passed the bounded proof tests. Bound exits are unresolved, not
counterexamples or lower bounds. The two composed tables are isomorphic, so the
twelve inputs are not claimed to be twelve inequivalent machines.

`checks/quotient_m124/` gives independently replayed distinguishing read words
for all 23,005 working-state pairs, length at most 10. This excludes ordinary
output-preserving quotients under arbitrary read inputs. It does not exclude
tape-invariant transformations, alternative encodings, or any 214-state
consistency machine.

## Reproduce

Python 3 and its standard library suffice for finite package checks:

```sh
python3 -B verify.py
```

This checks the manifest, exact machine and generated-source bindings, M124's
complete calibrated prefix, the quotient witnesses, the independent abstract
invariant, and saved source reassociations. It does not silently run every search
or claim a proof-assistant build from Python results.

For fresh proof builds, use the commands in `report.pdf` and each proof
directory's README. The actual recorded versions are Lean 4.32.0 and
Coq 8.18.0 / OCaml 4.14.1. The upstream full endpoint uses Rocq 9.1.0; the documented
9.1 compatibility route has not been run here.

Compile the report with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Integration priorities

1. Replace the old Rocq source interface with the compact one-sided plain proof,
   preserving its public theorem name, and rebuild the complete endpoint.
2. Port M124's two marker lemmas and two short blocks to the repository tape
   semantics; import K215's established endpoint.
3. Parameterize Lean's ordinary decoder bound before applying the same zero-offset
   specialization there: the comparison needs 176-bit paths.
4. Separate generic program encodings from old program data and replace Rocq's
   linear successor lookup with a verified balanced representation.
5. Pursue a joint reachable-phase transformation and selector allocation for 214,
   with a positive-length local simulation certificate.

## Attribution

The original machines, calculus, compiler, and baseline proofs remain inherited
work. Their notices and licenses are preserved in the component directories.
M124's original construction and ordinary argument are included under
`m124_rocq/UPSTREAM_NOTICE.md` and `upstream_marker_proof.md`. New proof and
research material follows ProveIt's MIT No Attribution terms. No blanket
relicensing of third-party adapted sources is intended.

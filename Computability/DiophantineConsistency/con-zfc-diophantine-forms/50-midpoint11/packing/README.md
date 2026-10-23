# Support-aware quadratic encodings for Con(ZFC)

The explicit support-aware weights reduce the largest exponent label from
799 to 190 while keeping the number of final witnesses unchanged.

| Equation | Domain | Exact degree | Live binary operations |
|---|---|---:|---:|
| `data/polynomial.json` | 10 unrestricted integers | 56,593,864 | 653 |
| `nine/generated/multitarget_nine_positive.json` | 9 positive integers | 30,947,584 | 651 |
| `nine/generated/multitarget_nine_natural.json` | 9 nonnegative integers | 30,947,584 | 654 |

The same measures for the reviewed wave-6 source constructions are respectively
237,520,456 / 782 (package40), 129,875,980 / 788 and /791 (package45).
The degree reductions exceed 4.19; live operation counts fall by 129 and 137.
These are improvements of the stated constructions, not global lower bounds.

From this directory run `python3 verify.py`. Alternatively, invoke the script
by its absolute path from any working directory. Only Python's standard library
is required. The driver rebuilds the new final circuits and checks the exact
source support, fixed tuple bytes against pinned hashes, two parent
presentations, all 71,808 source/expansion pairs, literal formula replays, and
exact-degree certificates. No ProveIt checkout or network connection is needed
for this finite verification.

The arithmetic circuits contain only fixed integer leaves, named witness
leaves, and binary `add`, `sub`, `mul` nodes. All exponents are fixed and expanded
into multiplication gates. Register names do not introduce extra witnesses.
Every coefficient is fixed from the four coherent binary payloads under
`coefficients/payloads/`; the coefficient builders and provenance are included.

The new theorem is proved in `SUPPORT_PROOF.md`. A LaTeX section for the main
article is `support_section.tex`. Bundled inherited source and finalizer arguments are identified under
`upstream/`, with original attribution in `licenses/`. Historical relative
references within those verbatim notes refer to their pinned repository
layouts; `upstream/README.md` supplies their origins. Those source citations
are not local runtime dependencies.

The declared consistency equivalence uses the pinned compiler/K215 endpoint
and Jones ratio theorem, plus Sun's ten-integer reduction for the unrestricted
integer equation. The new transformation is proved mathematically, with exact
finite verification artifacts. No new end-to-end Lean/Rocq verification is
claimed. This does not prove either consistency or inconsistency of ZFC.

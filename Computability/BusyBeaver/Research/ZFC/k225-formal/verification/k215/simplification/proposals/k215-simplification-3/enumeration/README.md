# Enumeration completeness: fixed candidate and generic length padding

## Useful conclusion

The common-NIP literal cutoff1 completeness proof can use ONE fixed universally
halting candidate instead of a varying-Y START family. The existing compiler
already supplies U=STORE0;STORE0;B1;R;R. Its first command is AX with opcode2,
so its code is positive and the ordinary consecutive scheduler reaches it.
If a generic bound is preferred, the existing credit proof already gives
|W(n)|<=n+1, hence code(U)>=|U|-1>=21. No additional length induction is needed
for that particular machine. The sealed delivered packet was not modified.

For an arbitrary cutoff N, any N-command prefix followed by a nonempty universal
U still universally halts (each command must terminate or halt), and its code
is at least N. A generic code-length lemma follows solely from decode_pack and
decode_le, without new Cantor arithmetic or arity cases. The exact positive
continuation wrapper is preserved; zero terminal commands do not disappear.

## Deliverables

- `LENGTH_PADDING.md`: complete ordinary theorem, fixed-code application,
  shortest reuse of the existing word-length bound, even shorter AX-first
  positivity argument, precise dependencies, and source-grounded assessment.
- `LengthPadding.uncompiled.lean`: a small reusable adapter sketch against the
  pinned latest EnumPerm. No Lean executable was available; not kernel-checked.
- `review/length_padding_independent_review.md`: independent proof/source review.
- `report_paragraph.tex`: concise report-ready statement of the simplification.
- `check_length_padding.py` and `check_result.json`: portable finite codec and
  prefix-algebra corroboration plus source/hash checks.
- `inputs/` and `INPUT_PINS.json`: exact local source and proof snapshots.

Run `python /path/to/enumeration/check_length_padding.py` from any directory.
It uses only this folder and the Python standard library, writes JSON to stdout,
and rejects optimized Python execution. The finite check passed 2,334 command-
word round trips and 245,364 prefix/store cases across 4,096 total Option-valued
transition systems. These counts are corroboration, not the all-natural proof.

## What this does not claim

The latest phase-four EnumPerm is already concise: encL_ge is four source lines
and complete nine. It already has the shared symbolic executor and general
halts_iff. A generic library replacement is not currently a demonstrated local
line-count or build-time improvement there. Its command tags are also different
from the common-NIP machine, although the coding lemmas have the same form.

Ordinary exhaustive candidate visitation is essential: an unbounded successful
family can be skipped by a biased scheduler. Universal means every natural
command-boundary work-store, not only normalized/theorem stores and not every
raw binary tape. Soundness, protected credit, primitive termination, startup,
and the inherited numerical-calculus comparison remain separate obligations.

Source baseline: e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad, EnumPerm SHA256
ad5ad3357ae811827a1661b2b671c0cf61da4ade6fe7615b4655a2a4c38f93cd.

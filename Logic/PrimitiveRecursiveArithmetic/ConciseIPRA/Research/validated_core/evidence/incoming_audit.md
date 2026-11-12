# Incoming ConciseIPRA audit

Pinned repository commit: `a4e5e96c456303cf231eab2aeeb3291d8889833f`.
All six incoming ZIPs were read through the GitHub connector, decoded locally, and extracted under this directory. The ZIP byte counts match the GitHub directory metadata. The package authors compare against earlier commit `1517d9d79ce33f631e0f82960c849427cbba23bf`.

## Current measured envelope

The smallest incoming compact checker coordinates are **257 significant tokens / 279 AST nodes / 522 normalized UTF-8 bytes**, attained by three different programs in `ipra_guarded_source_2026-11-11/ipra_guarded_source_2026-11-11/code/`.

| Program | Tokens | AST | Bytes | gzip 9 |
|---|---:|---:|---:|---:|
| checker_tokens.py | 257 | 285 | 568 | 338 |
| checker_ast.py | 261 | 279 | 603 | 345 |
| checker_bytes.py | 264 | 301 | 522 | 328 |
| checker_strict.py | 490 | 561 | 1202 | 571 |

These were independently recomputed with CPython 3.12.14, `ast.unparse(ast.parse(source)) + "\n"`, all AST nodes, significant lexical tokens, and `gzip.compress(...,compresslevel=9,mtime=0)`. The code has no docstrings in these four files. Full recomputed source table is `recomputed_metrics.json`.

The compact contract assumes canonical public goals and allows administrative auxiliary proof formulas. It does not strictly reject all nonpublic goals. All code for JSON input and acceptance output is counted, but the shared runtime and JSON standard library follow upstream convention. The strict public grammar validator is a distinct larger program. No single profile attains the entire envelope.

## Ideas already delivered

1. **Deterministic auxiliary / guarded source.** Combine transport restricted to nonliteral-zero source, with source zero selecting Q elimination, and atomic-progress/compound-case introduction selected solely by the root. Public atomic D matrices are guarded `I(y,0;u.h)=I(y,0;u.k)`; unguarded auxiliary D matrices have progressive ordinary reading `exists x forall y (E(x,y) -> E(x,Sy))`. This yields old canonical guarded consequences. Unguarded auxiliary induction repairs zero-source equality before logical padding. Guarded source improves the root classifier from `not len(a)%2` to `len(a)==2`; this is a smaller spelling under the proven successful-trace syntax, not an additional theory theorem.

2. **Guarded orbit.** Closely related combined calculus, with explicit administrative iterator-orbit formulas and stable-left equality bootstrap. Shows naive guarded-only intermediates plus restricted source cannot derive `0=x |- x=0` through a counterinterpretation. Same 258/281/525 direct envelope as deterministic auxiliary; strict guarded 1205 bytes.

3. **Protected core.** Public equality is wrapped as `W(s)=W(t)` with `W(r)=I(0,r;u.0)`; both term roots are iterators. This supports a source-stable completeness proof. Same compact programs as above, 258/281/525; strict protected grammar 1251 bytes. It deliberately does not claim unrestricted zero-source intermediate normalization.

4. **Mirror guard.** Atomic D matrix is `a(x,y)=I(y,a(x,y);u.h)`, with initializer on the left and inside the iterator. True base, deterministic root introduction and restricted transport coexist; 258/281/525 compact envelope, strict 1503 bytes. It has a substitution-free induction bootstrap and both public formula composites.

5. **Reversal core.** Change Tr and QE to return root reversal of the endpoint: equality swaps sides, Q/D root unchanged. Constant templates and an iterator-headed retraction `J(a)=a` yield arbitrary equality reversal. This makes source restriction admissibility induction-free. A general retraction criterion is proved. Contextual consequence relation is identical to native Eq/Q/D, and it inherits the whole-domain iPRA bi-interpretation without formula-language restrictions. Reversal is six bytes more than the same refactored unreversed checker; most size gain comes from neutral-zero protocol and shared parser. Complete typed public Eq/Q/D checker is 1055 normalized bytes; unreversed matched version 1049. Untyped strict full-goal validator is 879 bytes, Eq/D-only 830. These should not be compared unqualified with the compact canonical-goal envelope.

## Mathematical scope observed

The new arguments are written mathematics; none of these ZIPs supplies a newly compiled Lean/Rocq verification. Reversal includes an explicitly uncompiled proposed Lean module. The native/iPRA bridge is an inherited proved input, not rerun here. The canonical/auxiliary distinction is explicitly stated, so it should be retained in every comparison.

The equality-free distinction in the repository README needs care: equality of restricted and native consequence relations implies substitution is admissible indirectly; direct induction on a restricted derivation can fail when substitution turns a nonzero source into literal zero. The incoming reports correctly identify that distinction.

This audit did not establish a new mathematical flaw in the written soundness/completeness arguments and did not run all package reproduction scripts. The exact metric claims above were independently rerun; other validation counts are package claims.

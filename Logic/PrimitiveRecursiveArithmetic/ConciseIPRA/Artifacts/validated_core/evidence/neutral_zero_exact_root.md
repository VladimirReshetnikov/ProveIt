# Neutral scalar truth with exact-root introduction

## Precisely proposed modification

Start with `ipra_guarded_source_2026-11-11/.../code/checker_bytes.py` and change the initial retained resource from `g=[[]]` to `g=[0]`. In the AST loop profile change `g=([],)` to `g=(0,)`. Keep `len(a)==2`, every normalization bound, the order of major verification, and freshness allocation unchanged. In canonical completeness certificates use major `m=0` for computation and introduction packets formerly using `m=[]`.

This composes two independently delivered changes: exact-root introduction from guarded_source, and scalar administrative truth from reversal_core. It is a new composition of those sources, not a new arithmetic/logical principle. The meanings of public formulas and the canonical public grammar are unchanged.

## Soundness, including additional raw accepted inputs

Use guarded_source's auxiliary reading: atomic equations mean actual equality; Q means anchored closure; D of an equation means existential progressive closure; D of a compound means existential anchored closure. On canonical guarded public formulas this agrees with the ordinary inherited reading. Administrative raw scalars at formula sort and harmless padding formulas denote truth. In particular both raw `0` and raw `[]` at formula sort denote truth; numerical `0` and the contradictory equation `0=S0` are different syntax positions.

The initial context changes one true administrative resource to another. All pre-existing primitive instruction cases and the sanitizer are unchanged. The exact-root test is especially transparent: with no proved major, a literal binary equation matrix gets its predecessor instance; a nonbinary matrix gets its zero instance. Thus an unrestricted compound progressive induction is not introduced.

One new successful raw trace possibility must be checked explicitly. A nonzero scalar major m can now normalize to the retained formula truth 0 and return immediately. This is harmless: the elimination matcher compares m with a nonempty list, so it cannot match such a scalar. Its exported resource is `m*3`, another scalar, hence another administrative truth. It therefore cannot generate an equation or anchored closure. Other positive major cases are exactly the old ones: a unary list D exports the diagonal Q resource; a binary equation or a triple Q exports only a padding list, besides any independently checked elimination; still longer arities export padding. Falsy scalar 0 selects the same computation/introduction cases as empty-list neutral truth did. The bounds/freshness phase is unaffected, because initial contexts still have length one and the same k=0.

Consequently the inherited accepted-trace induction works with initial decoded context {truth}. Every newly accepted canonical public goal is provable in iPRA under its ordinary guarded reading. By the inherited guarded formula round trip and completeness, it was already a canonical consequence of guarded_source. No additional canonical consequences are obtained.

For exact integer/list certificates this is immediate from the displayed decoder. For the compact all-JSON convention, the same noninteger successful-trace restrictions as the parent remain needed; the new scalar-major case cannot pass the list-valued matcher and only exports scalar truth. Do not silently claim strict type validation: the compact modules still have none.

## Completeness

The canonical proof compiler can use the same construction as guarded_source, replacing each administrative dummy major [] by 0. Only that packet field changes; an indiscriminate recursive replacement of all empty arrays is unnecessary. For these generated proofs the two kernel executions correspond at every rule:

- Both neutral majors are falsy and accepted directly from the respective initial contexts.
- Neither matches a nonempty equality or Q major.
- Their threefold products are falsy, so the computation/introduction resource is identical.
- The source classifier and exact-root introduction choice are identical.
- The negative-variable floor and all freshly allocated labels are identical.

Every canonical guarded derivation therefore still has an accepted certificate. Combining completeness and soundness gives exactly the same canonical public consequence relation, so both inherited iPRA interpretations and both formula composites transfer unchanged. This is stronger than mere equiconsistency.

## Measurement interpretation

The byte profile saves one normalized byte, significant token, and AST node. Expected result: 521 normalized bytes, 263 significant tokens, 300 AST nodes. The tuple loop profile saves one of each: 602 bytes, 260 significant tokens, 278 AST nodes. The global-floor token profile begins with empty context and does not gain from this single replacement, so the best token coordinate remains 257 unless a separate improvement is found.

The neutral truth change has already been described in the incoming reversal package. The new claim is only that it safely composes with exact-root deterministic introduction; it must not be presented as a previously unknown equality theorem or a substantial foundational breakthrough.

# CurrentWordTopBounds2011 author receipt

This is the controller_certificate author's self-review and bounded fresh-build receipt, not an independent review. The packet constructs exact final-field identities and stronger size bounds for the actual assembled word. It does not assert whole high-mask acceptance, controller choices, a source solution, or native completeness. Existing frozen dependencies were used unchanged; this is not a fresh replay of their whole closure.

## Frozen files

| File | Lines / bytes | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentWordTopBounds2011.lean` | 259 / 11896 | `7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f` |
| `Lean/DiophantineConsistency/CurrentWordTopBounds2011Checks.lean` | 85 / 4069 | `d90115c218fc12fc7f9667089392bafb4e7777cc7452f9422544fdf8065d4b20` |

The only direct import is frozen `CurrentWordClause2011`, SHA256 `df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc`. The author also wrote that clause packet and the assembled-word/kernel dependencies; no independence is claimed for those components.

## Exact content and scope

For arbitrary numeric dummy and marker maps, the actual folded-kernel convolution at field 2009 is exactly `2 * weight (inl 0) * marker j`, and at field 2010 is zero. All three bare terms and every reflected term are accounted for. The sole surviving reflected position at 2009 is identified using the proved physical-position injectivity, not a guessed tile ordering. Spatial wrap is eliminated through actual field residues.

With Boolean controls and actual displacement `47 * (2011 * s)`, the temporal contributions at both fields vanish. The actual coefficient bound and the existing carry bound 57 imply outgoing carry zero at 2009. The recurrence then gives outgoing carry zero and normalized digit zero at 2010 in every cell. No high mask or matching condition is used.

The final cell's field 2010 has canonical index `N*2011-1`; this remains valid for `N=1`. A generic finite-prefix bound therefore yields `F < radix^(N*2011-1) = radix^(N*2011)/radix`. Independently, Boolean source digits and actual support at most 1004 give `C < radix^(N*2011-1006)`. These are bounds on the actual word encodings, not on unrelated representatives. The focused existential check obtains the same actual normalization and positive F from the already-constructed clause endpoint, then adds the new bounds; it does not assume a desired strict representative.

Focused checks cover the empty prefix, all earlier digits equal to radix minus one, a nonzero excluded suffix negative control, last-cell indices for one and two cells, numeric controls 17/23 for the raw identity, seventeen whole periods at `N=1`, the separate source bound, and the same normalization with all top digits zero.

## Fresh validation

The entire final main and checks sources were read. Each was compiled directly and serially with `lake env lean -M6000 -j1`, with `Elab.async false`, into its own new module object. No prerequisite build or object replacement was requested.

- Final main: exit 0, 6.17 s, peak 3,290,404 KB; no Lean diagnostics.
- Focused checks: exit 0, 3.38 s, peak 3,251,372 KB; all sixteen axiom reports use only `propext`, `Classical.choice`, and `Quot.sound` (the last-index theorem requires only the applicable subset).
- The checks emit one benign exponentiation-elaboration notice for exponent 1005 exceeding the evaluation threshold 256. This is not a proof failure; empty diagnostics are not claimed for checks.

| Artifact | SHA256 |
| --- | --- |
| Main `.olean` | `e9a8ad9d137e9493351a846ea4946714f6d0a3878b2e39a596ae30334df911ac` |
| Checks `.olean` | `80dbaaaeded2c8d6e071031c0816044747778e0af1c63f6c3c7cebfb97e92fcc` |
| `/tmp/current-word-top-bounds2011-main-stage3.log` | `b25bd99fffce655989d501648c26e7134a2136e120c4997f9ee5ba1bd452f2f6` |
| `/tmp/current-word-top-bounds2011-checks-stage1.log` | `7d5fa367b964e4bf3c9f8ff6e1d74f900f717ea92fd9a696f78b8ac0ea8eaa7d` |

Development failures were local elaboration issues: an equivalence coercion, natural-cast rewrite shapes, and ambiguous open names. A subsequent sum proof retained a leading `0 +` and hit the deterministic heartbeat limit; removing that redundant addition before applying the generic finite-sum lemma resolved it. No heartbeat limit was increased, no closed table computation was introduced, and none of those failed attempts is reported as an accepted build. Final source premises were not strengthened to bypass a target conclusion.

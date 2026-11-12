# Incoming ConciseIPRA audit

Snapshot: VladimirReshetnikov/ProveIt, commit a4e5e96c456303cf231eab2aeeb3291d8889833f.
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming.
All six ZIPs authenticated against current Git blob SHA1s. Three preexisting local ZIPs exactly matched; three fetched through GitHub base64 API. Selected text/code files extracted under each ZIP stem.

| Package | Blob SHA1 | Main contribution | Compact envelope (tokens/AST/bytes) |
|---|---|---|---|
| deterministic_auxiliary | ca1d595bc3b95e4337ac61fc991b413fd3048f71 | Combine guarded public syntax, source dispatch, deterministic introductions using unrestricted auxiliary atomic progress | 258/281/522 |
| guarded_orbit | 2f2bbfc62253b8017ef1623a82629707b6a9c578 | Administrative iterator-orbit induction repairs failed guarded-only zero-source bootstrap | 258/281/525 |
| guarded_source | 7b88478e276a2e8dd7ea04232fb477354ab84d9a | Pure-equational source-elimination theorem composes with canonical guarded transport; exact binary root test | 257/279/522 |
| mirror_guard | 10bea5cab44e2764256664b8ef230ba83767f449 | Atomic D matrix a(x,y)=I(y,a(x,y);u.h), initializer on LEFT; no auxiliary unguarded progress needed in conceptual calculus | 258/281/525 |
| protected_core | d0ec6b4455fe346c8bae097c0ae1459a2fb184da | Protect public equality as W(s)=W(t), both sides I-headed, W(r)=I(0,r;u.0); completeness in stable-source fragment | 258/281/525 |
| reversal_core | 14280baf9ddbe82201b5bc23ebd93100ec973915 | Crossed equality/Q elimination reverses atomic goal; equality restoration via retraction, with no induction | 259/282/525 (unreversed compact profiles); reversed byte profile 531 |

Coordinate envelopes combine DIFFERENT standalone programs.

## Independent measurements

Remeasured from supplied source under CPython 3.12.14 using ast.unparse(ast.parse(source)) plus newline, significant tokens excluding comments/whitespace, all ast.walk nodes, and gzip.compress(level=9,mtime=0).
For guarded_source:
- checker_tokens.py: 257 tokens, 285 AST, 568 bytes, gzip9 338.
- checker_ast.py: 261 tokens, 279 AST, 603 bytes, gzip9 345.
- checker_bytes.py: 264 tokens, 301 AST, 522 bytes, gzip9 328.
- checker_strict.py: 490 tokens, 561 AST, 1202 bytes, gzip9 571.

Reversal strict variants:
- strict Eq/D public goal: 830 bytes (gzip9 466).
- strict Eq/Q/D public goal: 879 bytes (gzip9 482).
- fully exact-integer/list whole certificate plus Eq/Q/D public goal: 1055 bytes (gzip9 545).
- same validator/kernel refactor without reversal, reported in CLAIMS: 1049 bytes.

The 830/879 modules validate exact public goal types but do not globally reject all non-integer/list nodes in auxiliary certificate data. Do not conflate with fully tree-typed 1055-byte contract.
Other guarded strict validators: auxiliary/orbit 1205, protected 1251, mirror 1503.

## Already-present mathematical ideas to avoid repeating

1. Dummy-witness D expansion of Q, guarded atom padding, root-determined introductions.
2. Composition with source-selected elimination, including broad auxiliary proof language.
3. Public/auxiliary distinction: naive canonical-only two-sided guarded/source combination fails. Counterreading makes every bare equation 0=t true, other equations actual, and invalidates contextual symmetry.
4. Protected atoms W(s)=W(t).
5. Mirror guard a=I(y,a;h) (one-sided initializer identity).
6. Crossed equality: from s=t and F(s), infer F(t)^dagger, s not literally zero. Dagger swaps ONLY equality endpoints. A constant F plus c=I(0,0;0)=0 yields reversal of any equality. Retraction J(a)=I(0,a;0)=a then yields reflexivity, safe joins at zero, unrestricted transitivity/congruence, and ordinary equational transport with NO induction.
7. Shared strict parser with depth parity: formulas even, terms odd; child depth changes by 5-arity.
8. Scalar 0 rather than [] as retained administrative truth.

## Limits

All packages compare old 1517d9d... snapshot; current source includes their results in incoming. They claim written metatheorems plus finite executable fixtures, no new completed Lean/Rocq verification. Existing formalized Native/iPRA bridge is inherited and was not rebuilt. Strict grammar costs are charged separately. No package proves an absolute minimum.

## Possible small refinement (not a breakthrough)

Protected public equality can plausibly require an iterator head only on its LEFT, not both sides: encode s=t as W(s)=t. For any public p=t with I-headed p, safe source transport takes W(p)=p through p=t to W(t)=p; symmetry at I-headed W(t) gives p=W(t). Thus the one-left-head public atom is interderivable with a two-head protected atom without a literal-zero transport. This could shorten strict grammar and formula encoding but is not yet implemented or fully proof-checked here.


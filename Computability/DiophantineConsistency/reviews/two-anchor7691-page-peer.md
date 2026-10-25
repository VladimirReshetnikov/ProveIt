# Two-anchor7691 complete page and second visual review

Date: 2026-10-25. Reviewer: `/root/complemented47_review`.

**PASS for the exact source and render below.** I read the whole candidate
TeX, compared its complete unchanged portions with the pinned radix55 page,
checked every changed coefficient formula, and viewed the actual full PNG.
I authored the new ordinary two-anchor proof, so this report is not an
independent mathematical approval of my own theorem. The separate full
ordinary peer review has that role. ROOT authored the new candidate source
and renderer run; this is a second source/render inspection of those files.

## Exact complete source

The reviewed candidate is
[`equation.tex`](../candidates/one-page-two-anchor7691/equation.tex), 5083 bytes,
SHA256 `45a9aa06b18b936199d267e503c0371555417b9404d3fa34b747dc3655f9e9f9`.
Its native reference is the frozen complete
[`PROOF.md`](../research/two-anchor-independent/PROOF.md), SHA256
`6df09c6637d32be89b60f767a876f70c1b2be5cf9d047b1add07252a257abe23`.

An exact byte comparison confirmed that the whole arithmetic front and
the whole indexed table, action decoder, alphabet and 436-character seed
are unchanged from the pinned radix55 page. All fifteen unknowns remain
strictly positive. The complete 66-operation P66 formula, including the
once-shifted source-mask port, is unchanged. Font declarations remain
9-point body and 7.7-point seed/footer on the same Letter page settings.

The new source correctly specifies `rho=2^47`, `B=rho^7691`, and
`beta=B-1`. K has precisely the bare terms at 30, 62, 1100 and
`7733=7691+42`, plus the two complete reflected coefficient bands.
The deleted bare exponent 2201 is absent. The source mask starts with
`B+3`, has the same two `2^46-2` clause masks, all 17 copies, only the
anchor test at 2195, and the new padding
`2^26*rho^6726-rho^6708`. This agrees with the proof's native mask
plus beta exactly once.

The additional printed factoring uses

    Psi(x,t)=x^1003*(x^20+t^17)*G8(tx)
             +t^8*x^983*(x^30+t^17)*G9(tx)
             +t^34*x^1095*(1+t*x^1100).

At t=2, multiplication by `2^10` gives every one of the proof's
34 label coefficients and both weighted anchors: `2^44` at 1095 and
`2^45` at 2195. Thus the printed selector sum plus `2^10*Psi(x,2)`
equals the complete Phi from the proof, with every index retained.

At t=1, Psi is exactly the sum of monomials at the nonselector nonzero
positions. Its four label groups and two anchors have disjoint support.
Consequently `G943(rho)+Psi(rho,1)` is the whole nonzero-support sum,
including selector 1. The printed

    MC=beta+rho-(rho+3)*rho^1063-G943(rho)-Psi(rho,1)

therefore equals the proof's MC, including the forbidden-selector
restoration and both dummy corrections. It replaces the longer floor
indicator by a full support identity; it does not change any coefficient
or add a Diophantine unknown. The lower-case t in the defined finite
polynomial Psi is a bound formal argument, evaluated only at fixed 1 or 2.

## Finite status and attribution

I also read the complete final ROOT-authored finite verifier, SHA256
`85cf6b14aab797c3b607b800ebbb3d6e9b51f1be2a3dedf08b8a56fe5da4116c`,
and the certificate, SHA256
`7d3db2089a55cefed6afa9e7df8ee5ffcc64d94a628cbffc261abf352dfa5c3e`.
Both my normal and `-O` default checks with `-B` exited zero and
reproduced the exact certificate. No `--write` mode was used.

The certificate discharges Pc2 with prime 2122441, H residues
18, 6993 and 1324284 modulo 47, 7691 and that prime, and valuation-one
lift quotient 1096353. It binds the exact full proof and source page.
It checks every copy, both clauses and their predecessors, the full
zero-padding band, the final field and the unique difference 1181.
It supplies 180987 total minimal unsigned big-endian bytes for the four
new fixed integers. These finite checks do not replace the unbounded
proof or its retained syntactic/foundational calibration.

The footer consequently has no unresolved Pc2 condition. It retains the
ordinary-proof and Lean-calibration boundary and says the page is a
complete finite specification rather than a proof of unsolvability.

## Actual render inspected

I displayed the entire PNG at
`/tmp/diophantine-two-anchor7691/equation.png`. The full arithmetic front,
boxed product, all four constants, complete Phi and Psi, entire indexed
table and decoder, alphabet, all eight seed lines, and final scope text
are visible. The shortened MC and factored Psi are readable without
overlap or clipping. Signs, exponent groups, subscripts and delimiters
remain distinct. I found no omitted formula or misleading line break.

`pdfinfo` confirms one Letter page, 612 by 792 points, 159652 bytes.
The complete TeX log contains no Overfull, Underfull or error diagnostic.
The actual inspected artifact hashes are:

| Artifact under `/tmp/diophantine-two-anchor7691/` | SHA256 |
| --- | --- |
| equation.pdf | `37e2863874130656f92eee2511d661c6e7bc68c2f052031616bfa2bef081462f` |
| equation.png | `51150e1c69acc01768aeefee1076a74a0967846d1d45782f317ef30fb2d5a79f` |
| equation.txt | `f2855cf40a8cbf6c45cd30a1dfee58cff4a02be39eeb40a03d6b828053865c27` |
| equation.log | `d3563b680106bce1ab58cb871c023edb78b5be4737fd4068fb0ee8e9ce2cdb49` |

The new `pdftotext -layout` stream has 2707 nonwhite characters. Using
the same convention, the preceding complemented three-anchor page has
2734, a reduction of 27; source TeX shrinks 5145 to 5083 bytes. These
are exact extraction/source metrics at unchanged declared font sizes,
not a global minimum or an exact mathematical-glyph count.

## Complete independent builder review

I read all 250 lines of the final separately authored `build.py`, SHA256
`696c710cdc27670313e7cec6eda415edcb464061793beabce4d57fde45e88c9c`,
then ran its default read-only check in both normal and `-O` modes with
`-B`. Both exited zero and reproduced all eight generated files byte for
byte. I used no `--build` option and made no builder or generated-source
edit.

The source reconstruction starts from the hash-pinned complete preceding
page, requires each exact replacement once, and supplies the complete new
Phi/Psi block. The independent printed-polynomial expansion includes all
3297 coefficients and checks the entire zero tail, both weighted flags,
the 36-position Psi-at-one support, and all 981 physical positions.
The separately expanded signed MC, MF, and positive-power K equal the
reviewed finite verifier's complete integers, including minimal unsigned
big-endian bit counts, byte counts, and hashes. Each gzip payload uses a
fixed timestamp. The three negative controls are simple coefficient-array
corruptions checked against the entire canonical array; they are not a
general TeX parser or a mutation-testing framework.

The builder authenticates and reruns the exact finite verifier and
certificate named above, propagating optimization mode, and binds the
whole frozen ordinary proof hash
`6df09c6637d32be89b60f767a876f70c1b2be5cf9d047b1add07252a257abe23`.
The complete parent 66-operation DAG is hash-pinned and retained; all
15 witness and four fixed-input leaves, operation types, backward wire
references, uniqueness and full output reachability are checked. This
authenticates the unchanged circuit and its revised coefficient binding;
the exact degree claim continues to use the retained leading-coefficient
argument, as the audit explicitly states.

The resulting full DAG hash is
`08162db9ea87f5fe05917106838ce1710fc388e0f1a374f622e980a893e41aff`.
The source manifest binds the builder, candidate README, generated TeX,
four complete gzip ports, DAG and build audit. Its deliberately separate
rendering boundary is accurate. I independently checked that the stable
candidate `equation.pdf`, `equation.png`, `equation.txt`, and `build.log`
have exactly the hashes of the inspected temporary artifacts above.
The final source remains
`45a9aa06b18b936199d267e503c0371555417b9404d3fa34b747dc3655f9e9f9`.
No builder defect or unresolved binding discrepancy was found.

## Review boundary

This report establishes source agreement and a successful second visual
inspection for the exact bytes above. It does not supply an independent
ordinary review of its author's proof, a new symbolic degree derivation,
or a new K215/foundational formal replay. No source or frozen proof was
changed by this page review. Later byte changes require a corresponding
source/render check rather than reusing these hashes by name alone.

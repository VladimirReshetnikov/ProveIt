# Independent audit of the actual printed arithmetic

Verdict: **PASS for the renderer/template/README transcription and universal
binding to the complete zero98 evaluator.** PDF rendering, visual layout,
exact extracted glyphs/seed, full tuple reconstruction and promotion are
separate root-owned checks. The ordinary proof is reviewed separately.

I read the complete fresh renderer, template and README, the full zero98
graph and ordinary proof, and the inherited short10 constant body. The
independent PEER_FRONT_AUDIT.py tokenizes the ACTUAL TeX arithmetic, imports
no renderer or source producer, and checks all39 displayed definitions
individually against their literal registers. The entire boxed polynomial
matches the complete98-gate graph over ten free input symbols and four
independent free coefficient ports, using only exact integer arithmetic
and associativity/commutativity of addition and multiplication. Every98
gate, ten input and four coefficient ports is live. This is a universal
symbolic identity; no numerical samples or expanded-polynomial hash imply it.

The page's A is Am1=A_full-1, so H=4A-1=4A_full-5 and
Delta=A(A+2)=A_full²-1. The zero-offset X=wq, L=kI+b' and whole expanded
center are exact. q_- is bJ; K is K0; K_2 is Kpos; M/Z/S are Mtot/Znum/fs.
The tail aliases Sigma1/Sigma2,P,U,V_N,E are respectively U/ab,Po,sc,aXb,Pe.
The single printed output is the literal N. Mutations of L back to HI+b',
the A offset, Delta and the Z transport sign are independently rejected.

The entire body following 'The four fixed integers' is byte-verbatim
from one-page-short10: SHA256
b79195aceca6d0a3340388676f32cae9635c86dfe743d849efa457040dab8011.
This includes all coefficient recipes,943 tiles, arithmetic ranks, corrected
initializer,430-action decoder and footer. The inherited full436-character
seed and ordered62-symbol alphabet are exact; the generated page seed
bytes match the old seed. The actual four generated payloads match the
whole BFS tuple byte-for-byte, with K mapped to K0 and MF_source copied
once to MF. Its values satisfy the uniform coefficient box. Original and
BFS K0 are different; no single-port mixing or pointwise tuple identity
is asserted. The entire generated polynomial.json additionally equals
zero98.json with precisely the declared page metadata and whole BFS
binding changes; parent-polynomial.json is the exact zero98 byte string.

The README's 58 multiplications,22 additions and18 subtractions agree with
every actual gate. Its degree360 leading form and selected coefficient
are correctly transcribed from the author's separate proof. The positive
completeness shear uses n_new=n_old+(k-H)I*Bt, without an arbitrary-positive
inverse claim. Root corrected the initially incomplete glyph list; it now
includes all displayed Greek symbols and the ell alias. Exact glyph and
seed extraction from the PDF remains a separate rendering assertion.

The reproducible audit uses ROOT=Path(__file__).resolve().parents[2],
requires --output, authenticates its own full bytes, records Python mode
and refuses a different existing output. Normal and -O receipts were first
written to separate /tmp paths and then copied unchanged into this packet.
They agree except for optimized_python. The independent output controls
also verify idempotent identical replay and rejection/preservation of a
different preexisting file. PEER_FRONT_CONTROLS.json records those controls.

Reproduce from the repository root, choosing fresh receipt paths:

```sh
python -B Computability/DiophantineConsistency/candidates/one-page-index-weight10/PEER_FRONT_AUDIT.py --output /tmp/index-weight-peer-front-normal.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-index-weight10/PEER_FRONT_AUDIT.py --output /tmp/index-weight-peer-front-optimized.json
```

Reviewed renderer SHA256:35f942f8a035137cd9d11ef111af581644f32f39ff5696f28761ce8eb6b61d6e.
Template:68514a9ab239be8f9d74776331670c2fe963cc6c70f144035de9364fb3827526.
README:7358f9de341c5bd0e24d9185f32eca1654f276f9f07939558c7d13ee51dcc2d7.
Actual zero98:bd7ae70e69288cb035f24a564f99e9ea4282b5f647558e52ad34170f73795f82.
The receipts retain every source and audit hash plus all39 aliases.

Only the five authorized PEER_FRONT files were added by this review.
No renderer, template, README, canonical, frozen or Lean file was edited.
There is no remaining needed formula or alias correction. Root owns the
complete page seal and promotion.

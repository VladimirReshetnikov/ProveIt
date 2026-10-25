# Initial ordinary review: changes required for the coordinate binding

Reviewed the complete frozen code-free proposal at
`research/direct-tile-coordinate-coefficients`, manifest
`ab52be2eb1b608de1709556451101d17939a4734888f95cd63db8661b2e12e40`.
Both payloads are unchanged: README `dbf0399e…` (13499 bytes) and
SOURCE_PINS `29382208…` (4357 bytes). No author, parent, page, main,
centering or fast-overlay file was edited. Only inert text/JSON/hash/length
inspection was used; no application, helper, import of repository code,
compilation, AST, numerical tuple, Lean or TeX/PDF execution occurred.

## Finding: east-coordinate e_i collides with the existing seed digits

The new table header explicitly defines the indexed families
`t_i=(w_i,n_i,e_i,s_i)` for all i=0..942. The unchanged seed paragraph also
defines `e_0,...,e_435` as the base62 digits of the literal seed. These are
not compatible as one global family: tile0=(2,435,3,1) makes east e0=3,
whereas the first seed character B has value11 in the printed alphabet.
Changing the summation letter from i to j does not distinguish the two
families. The old payload's local tuple coordinate e did not introduce this
global indexed collision.

Use a fresh indexed letter such as p_i in **both** the table header and
the direct selector, or explicitly introduce and charge distinct namespaces.
Uppercase E_i is unsuitable without further scoping because decoder E_0
already denotes the high flag word. A fresh one-letter p_i has the same
source/glyph length as e_i, so the existing savings need not change.

The current full printed recipe is therefore not approved as unambiguously
bound. This is the sole requested change; it is not a defect in the
polynomial identity. Author payloads remain frozen pending ROOT direction.

## Mathematical identity and retained scope: pass

For independent west/north/east/south coordinates W,N,E,S, distributivity
gives

    1+2^10*(2^34-W-2^8*N-2^17*E-2^25*S)
      =1+2^44-2^10*W-2^18*N-2^27*E-2^35*S.

Applying this coefficientwise at every one of943 fixed indices and using
G943=sum x^i proves the **whole** Phi identity, before actual tile
specialization. All four control groups are literal unchanged text, so
there are no omitted high coefficients, support or carry changes. MC's
digit/indicator expression and K's evaluation at1/rho receive identical
Phi values. Beta and MF remain literal. With collision-free coordinate
names, all four indexed integers and the complete fifteen-positive
66-operation/degree157 polynomial therefore remain identical, including
the accepted whole-tuple native/Pell witness maps and proof boundary.

The entire proposed body retains every table row/domain/index, all430
decoded actions, the436-character seed/alphabet, Lambda, masks, G_m and
footer. The action symbol v_j remains defined; only the separate payload
function v(t) is removed. The dependency order seed -> actions -> sets/ranks
-> tuples -> Phi -> MC/K is acyclic. The existing bound indices are local;
the fifteen equation inputs are unchanged. No new arithmetic endpoint,
consistency result, coefficient packet or runtime acceptance is licensed.

## Complete body and charged comparison: pass, unrendered

Authenticated all13 external hashes, the one own-core hash and the entire
compact66 parent manifest `ce9915c9…`: exactly62 payloads/559504 bytes.
The old literal native body is exactly the suffix of the accepted5244-byte
TeX, after its1425-byte prefix. Extracting the full proposed body from the
note gives SHA `aa5949fa…`, 3793 bytes and3535 nonwhite source characters.
It is **exactly** the three declared edits to the old3819-byte/3555-nonwhite
body: selector plus continuation, complete header, whole payload paragraph.
Thus the claimed net26 bytes and20 nonwhite source characters are correct.
The isolated selector counts55/86 omit their common final LF; including
that LF gives56/87, with the same31-byte growth and unchanged net result.

The charged flat spelling also checks: selector30 ->45, header22 ->26,
payload42 ->0, hence2307+15+4-42=2284, a23-character proxy gain. It is
explicitly unrendered. No new PDF extraction, fit, font, wrapping or visual
claim follows, and any later actual-TeX audit must bind the corrected
coordinate family as well as the complete unchanged decoder/body.

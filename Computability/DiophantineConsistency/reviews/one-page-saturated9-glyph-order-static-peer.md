# Independent static review of the two PDF glyph-order corrections

Reviewer: `/root/reduce_ten`. Date: 2026-10-24. **Static approval; no
unresolved finding.** I read the complete763-line auditor,145-line renderer,
309-line validator proof,94-line toolchain instructions, README and mapping
prose, the complete v7 failure record and the actual retained TeX/text.
Inspection used inert file/JSON reads, diffs, whole-file hashing and byte
comparisons. I did not import, compile or execute a corrected module, run
TeX/PDF tools, run a parent/source program or run Lean. This record supplies
no new runtime, rendering, control or final-page PASS. Root owns execution
release after both static reviews.

## Exact executable delta

The current auditor is
`fb30c9a7b09e24cf64adaeb7e6c78468d1e180fd27cae6052da64a7ab7bb50ba`.
Whole-file comparison against the archived v7 auditor
`83bee8007521b3ad79c1e1bf066089e4b506fdf6c3254e8ea909307d3bd86650`
finds exactly one new comment and this one statement in math_glyphs:

```python
text = text.replace(r'W_1^2', r'W^2_1').replace(r'V_0^2', r'V^2_0')
```

It follows clean_math and precedes the existing Greek-command replacements
and glyph strip. No other executable statement, import, parser, ring
operation, mathematical comparison, context assignment, control, process
argument or output policy changes. In particular the complete polynomial
parser still consumes the whole expression; the previously proved N0=B^117
substitution remains in both environments; the R+1 bridge, every-node
coverage, all free-port coefficients and all native-payload checks remain.

The actual frozen TeX contains W_1^2 exactly twice, in Q_r and E_0, and
V_0^2 exactly once, in a_0. The retained whole extracted text displays W2
then1 at both sites and V2 then0 at the third. The two literal replacements
therefore produce the expected extractor order W21/V20, preserving each
symbol and numeral. They neither permute arbitrary strings nor remove an
exponent. Actual retained PDF text has no underscore, so neither new
replacement changes the actual-text side. No other simultaneous indexed
power is normalized. The separate exact TeX/parser comparison still binds
the mathematical indices and exponents before PDF checking.

check_pdf itself is byte-identical to v7. It continues to check complete
consecutive ordered front blocks: boxed expression, all40 definitions,
31weights,22targets and all three kernels. Punctuation ignored by its
glyph strip remains checked by the mathematical parser. All seven native
formula blocks retain their entire numeral streams, with the already
reviewed large-sum limit ordering. Complete seed/alphabet, nine-positive
signature, cost/degree, one Letter page, no-overflow diagnostics and exact
retained extraction checks remain. Native operator glyphs and legibility
still require separate visual review; no automated visual claim is added.

## Whole unchanged mathematical and rendering inputs

I compared the whole actual TeX, polynomial.json, FORMULA_MAP.json, renderer
and all five live derived artifacts byte for byte against v7. Each matches.
polynomial.json also equals the entire accepted saturated_positive.json.
Both external pin dictionaries are identical to v7. README/MAPPING/proof/
instructions and pins change only release-history/scope prose and the new
archive bindings; their mathematical sections retain the same equation.

The accepted433-operation graph has464 nodes,85 kernel records over the
four native ports and11 fixed leaves, with nine strictly positive inputs
and inherited exact degree1628768. No new mathematical identity, coefficient
tuple, initializer, port transfer or domain change is introduced. The
original complete compact54 tuple and722-symbol seed remain the declared
objects. The prior v7 math/native/control completion is historical partial
execution, not a final audit success. The archived traceback records its
stop at the PDF front glyph comparison; no final audit receipt exists.

| Final reviewed object | SHA256 |
| --- | --- |
| FRONT_AUDIT.py | fb30c9a7b09e24cf64adaeb7e6c78468d1e180fd27cae6052da64a7ab7bb50ba |
| TOOL_PINS.json | 16d4fea7986ea2b9ae9eb12db3552f4f31179096ef040ef2c46d2218c803a20f |
| SOURCE_PINS.json | 2c5fbec46fa9ae18fedbf993f39f94bf8c15acf2db938d59a1ec69e3063cf128 |
| VALIDATOR_PROOF.md | 2d73102bb196749b9b4caf458478b888448dff94b98f9307f449e5804a9fd7b7 |
| TOOLCHAIN.md | a68624889dfb1f133816d9542c7b0b31c02e4effba882f7f2f567d6ab1e3efd6 |
| render_saturated9_page.py | e710f96fdddc1c994af56036c9651bb9dd1cc01af5d059f43bb1e6d0b8bf30ed |
| equation.tex | e8a590cd71859fdddbd749ddc656b2507187cdae49990fa40de5db0875f8abef |
| equation.pdf | 4ae1bdee9aa57c074f14f0790823791724c6032baca42e4b724245476ea554d7 |
| equation.txt | de7b872d034d4ee9b6d6edbe3d9e15e1ff377b1f7c1ae19ed7d6f1660093050d |
| polynomial.json | bf0907fb36ab78830922f61e5bfbacbd80786ebd375a11b4d0cf6b1bfb7c12b3 |
| FORMULA_MAP.json | 38ff5906f608fbd1d52edf18b736d7f71bed2f3069329b74e46646660c037b61 |
| history/v7/MANIFEST.json | 040393797e24855c9d21739ab6ca7ea13d717287d0ef46e6a2f202bbbde2c037 |

## Closure and remaining release boundary

I authenticated every whole-file hash and byte count:56 external,141
preparation/history and4 core records in TOOL_PINS;51 external and5 own
records in SOURCE_PINS. All seven historical inventories have exactly
their declared members/hashes/bytes. The new v7 inventory has21 payload
members, including seven complete render records, empty failed-auditor
stdout and the full failure traceback. No failed or partial command is
relabeled successful. No old member was dropped from the preparation pins;
the22 added entries are exactly the v7 payload and manifest.

I requested one minor prose correction: the ambiguous historical sentence
"This corrected module has NOT then ran" now reads "That corrected module
then ran after both reviews". The final proof and its TOOL_PINS core record
were refreshed; executable and SOURCE_PINS bytes did not change. The next
paragraph explicitly leaves the present glyph-corrected module unexecuted.
That wording finding is resolved.

The reviewed correction is sufficient for the identified literal-order
mismatch at these three actual sites. This static conclusion does not
predict that later actual PDF checks or rebuilds pass. The released five
commands, retained complete receipts/stdout, independent replays and visual
review remain required before the author closes/accepts the page. No page
seal, canonical change, source execution or broader compiler authorization
is supplied here.

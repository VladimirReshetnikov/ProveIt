# Source review of the standard-iPRA AQ29 draft

This review covers the same-language presentation and uncompiled AQ29 client
at source snapshot `55a84e6cc0e5fd58607e42f346d1dcc4303ec70a`, plus the
provisional extension receipt recorded in commit `7e41cc613d`. It is not a Lean
replay or a proof audit.

`IPRAStandardTheory.standardTheory` shares `PRALanguage.language`, the
primitive-recursive defining schemes and successor/order basic axioms with
the native candidate. Its explicitly different schemes are atomic rather than
full-formula equality substitution, and successor-step rather than `x+1`
quantifier-free induction. The source states `provable_iff` in the direction
`standardTheory ⊢ φ ↔ nativeTheory ⊢ φ`; it derives full Leibniz replacement
and uses the existing two induction conversions. This is a comparison of
these explicit same-language presentations, not an independent equality-only
language comparison or a proof that their shared schemes match every textbook
formalization. No source-authenticated coherent replay of the new comparison
is recorded here.

The uncompiled `IPRAStandardAQ29` client uses `.2` in the correct direction
to transfer both the native AQ29 no-zero equivalence and the selected
Foundation consistency comparison. It composes those equivalences in the
correct direction. The latter refers specifically to the Gödel–Gentzen
translation of the mapped Foundation consistency sentence; it is not a
general comparison with arbitrary alternate ZFC proof codings. These statements
have not been elaborated against a coherent provider.

`verify.py` independently checks the pinned survey and parent-manifest hashes,
all six additional source bytes against both the receipt and their Git blobs,
their ordinary single-line import headers and declared order, and reachability
in the two recorded source graphs. It obtains 1,209 parent modules, the single
omitted parent checks module, six additions and no new recorded direct external
import. Parent source bytes, workspace drift, Lean's actual dependency parsing,
provider identity and dynamic loads are not checked. In particular, neither
this finite source review nor the survey establishes a theory theorem or an
equation endpoint. The frozen parent build was still in progress when reviewed.

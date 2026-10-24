# Provenance, attribution, and proof boundaries

The common source snapshot is
[VladimirReshetnikov/ProveIt at commit 08200eb10fde2db408c69dffd840d6920a569b1f](https://github.com/VladimirReshetnikov/ProveIt/tree/08200eb10fde2db408c69dffd840d6920a569b1f).
The delivery was prepared on 24 October 2026 with ChatGPT assistance for
incorporation into ProveIt. The machine-readable inventory is
[provenance/SOURCES.json](provenance/SOURCES.json). All local paths in that
inventory are relative to this delivery's root.

## Two constructions with separate ancestry

The **direct quartics** in `direct/` and `direct/small_height/` encode the
literal C222 proof calculus over nonnegative integers. Their semantic
calibration uses the numerical constructors and refutation endpoints listed
below. The new work supplies the shared arithmetic certificates, literal
quartic materializations, and elimination of nonnegative affine gates.
These quartics do not obtain their calibration by running K215 or by
instantiating a Jones universal polynomial.

The **integer coordinate family** in `coordinate_family/` reduces the degree
of three polynomials with 21, 20, and 19 unrestricted integer unknowns.
It starts from the literal incoming 25-variable octic and transports its
zero set through explicit integer-polynomial coordinate maps and elementary
row operations. Its earlier native compiler, Pell arguments, determinant
guard, and K215/refutation calibration are inherited. This second
construction therefore does retain the K215 ancestry of its source family.
The new points are 21 variables/degree 16, 20/18, and 19/40. The other
polynomials supplied in this component are identified baseline reproductions.

## Incoming archives inspected

All six archive roots in the pinned repository's `docs/incoming/` directory
were read for overlap. Additional low-variable formulas and proofs were
inspected where relevant. The inventory below records the exact archive
bytes downloaded. It does not assert that every verifier in every incoming
archive was run. The original large ZIP files are not duplicated in this
delivery; relevant root texts and the literal octic baseline are retained
under `coordinate_family/`. See
[provenance/new_incoming_comparison.md](provenance/new_incoming_comparison.md)
for the comparison and its limits.

| Repository archive name | Bytes | SHA-256 |
|---|---:|---|
| `ConZFC_Structural_Reductions_Round11_2026-10-24.zip` | 1,623,600 | `83bccd59ab691f7076a36c2b03cf84f05f8f7b2c04490ede94c389c29ec2034d` |
| `ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | 17,386,624 | `291af5f4266ba5e0759273282ef4c6c5941f0bd2c3813e0481b721b08605b159` |
| `con-zfc-budget-and-centering-2026-10-23.zip` | 736,449 | `a23fb49828081f072375f00eeaa37e7d45f6d1bcfbb9ec0eb8850d124600e34b` |
| `con-zfc-centered-pell-norms.zip` | 927,726 | `6b176f4e5db4b8a4ec7a7357f3ab3f8356cc811ad7fe65b0ac748c1047812fcd` |
| `con-zfc-radical-guard-descent-2026-10-23.zip` | 1,684,114 | `ccb67b2ddaf49287079d9f4758915c8866db12008eb656ecaf6c34b81a5ef084` |
| `report.zip` | 13,973 | `4130601f3f13426318c4266a87e2d6ce9cf7205c711a9c226782e87744be2754` |

`coordinate_family/INCOMING_PINS.json` uses the download alias `round11.zip`
for the first archive; the table above gives its repository filename.
The final archive contains only `report.tex`. Claims reported by that
manuscript are distinguished from reproduced equation/certificate artifacts.

The coordinate family's literal baseline is the member
`ZFC_Diophantine_Joint_Guards/joint/joint25_octic.json`, delivered as
`coordinate_family/incoming_joint25.json`, with SHA-256
`9124c179d40cc52e5ce11515555e370f370bd6d74d6dce68d2273e408bb211d8`.

## Direct calibration and arithmetic sources

The following files are retained in `direct/provenance/`. Their complete
repository paths, Git blob identifiers, byte lengths, upstream hashes, and
delivered hashes appear in `provenance/SOURCES.json`. The earlier compact
calibration index is `direct/provenance/CALIBRATION_PINS.json`.

| Source | Role in the inherited argument |
|---|---|
| `Code254.lean` | Literal numerical formula constructors, distinguished contradiction code, and schema constructors. |
| `KCode222.lean` | The sealed C222 numerical calculus, including `growG` and the helper-free bundle clause. |
| `KEndpoint.lean` | The theorem `c222_iff_zf_refutation`, connecting C222 derivation of code 1 to the specified ZF refutation predicate. |
| `ConstructibleChoice.lean` | The theorem `zf_refutation_iff_zfc_refutation`, connecting the chosen ZF and ZFC refutation predicates. |
| `Bridge.lean` | The chosen `ConZFC` predicate, defined as absence of a derivation of bottom from `ZFCax_s`. |
| `PellRepresentation.lean`, `PowerRepresentation.lean` | Pell and power representation source interfaces. |
| `FactorialRepresentation.lean` | Factorial representation source interface. |
| `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean` | The inherited bounded-certificate and bounded-quantification interfaces. |
| `COMMUTATIVE_CERTIFICATES.md` | The finite nonnegative single-conclusion flow/derivability argument. This source alone does not provide a fixed ordinary Diophantine equation. |
| `inherited_onestack_section.tex` | Earlier accumulator and one-stack arithmetic construction. |
| `direct_flow_large_carrier_README.md` | The preceding large-carrier candidate and its stated arithmetic and formalization status. |

The full transitive Lean dependency tree is resolved by the pinned repository
commit; it is not duplicated here. These source texts were inspected and
retained. The new construction was not compiled as a new end-to-end Lean
development. The article supplies the ordinary mathematical argument and
identifies its inherited representation and calibration dependencies.

### Original source versus generated source

`direct/affine_shared_step.json` is the byte-identical upstream file
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/affine_shared_step.json`.
It has 502,148 bytes, Git blob
`e660c84e22630ee9edb546417d296fd7cde1e0f2`, and SHA-256
`c858ecd4f87f06e16d9f7b075ccdfe911af22d928e722a470ca292ec731fdc03`.
It specifies a local affine accumulator step, with 23 local witnesses; it
is not the finished global consistency equation.

`direct/wire_eliminated_source.json` is a newly generated transformation of
that file. It has 89,409 bytes and SHA-256
`1e7cf2f3ea9397e138c7543d47ccd00a967b8fbb2fd4c8d58f176c409033c1bb`.
Its constructor-wire definitions are arithmetic expression nodes, rather
than additional quantified coordinates. The eliminated definitions are
triangular and have nonnegative coefficients, so their restored values are
natural on natural inputs. `direct/SOURCE_AUDIT.json` records exact checks
of the 56 defining identities, together with finite branch controls.

The final direct builder uses the literal numerical constructors in
`direct/direct_calculus.py`. `direct/CALCULUS_AUDIT.json` records exact
compositional comparison with the source definitions. The generated
wire-eliminated source is retained as an independently inspectable bridge.
`direct/BUILD.json` and `direct/small_height/BUILD.json` bind the final
builder, source, literal calculus implementation, and exact equation bytes.
The generated files are not represented as unmodified upstream artifacts.

### Retrieved text normalization

Thirteen retained direct source texts were independently retrieved as
base64 byte payloads and authenticated against their Git blob identifiers.
Seven delivered copies are byte-identical. Six delivered copies differ
only by **one additional trailing LF byte**: `PowerRepresentation.lean`,
`FactorialRepresentation.lean`, `BoundedForallCertificate.lean`,
`PellRepresentation.lean`, `BoundedForallRepresentation.lean`, and
`COMMUTATIVE_CERTIFICATES.md`. Both upstream and delivered hashes are given
in `provenance/SOURCES.json`. No mathematical text differs. The existing
delivered files were left unchanged during this provenance audit.

## Fixed coefficient payloads

The coordinate family supplies all six fixed numerals as gzip-compressed
unsigned little-endian byte strings. Together their decompressed payloads
occupy 615,883 bytes. `coordinate_family/COEFFICIENT_BINDING.json` binds the
actual delivered numerals; `NEW_BINDING.json` specifies the determinant
scales. The source34 compiler, machine input, tile data, binding, and proof
are included under `coordinate_family/upstream/source34/`.

`coordinate_family/SOURCE_PINS.json` identifies the earlier source files.
Where a local coefficient is renamed or transformed, those pins identify
its ancestry, while the delivered binding and replay recipe specify its
actual value. In particular, the delivered `MF` is the shifted coefficient;
it must not be confused with source34's `MF_source`. Gzip container bytes
can vary with platform metadata during reconstruction; equality of the
decompressed numeral bytes is the mathematical binding.

## Verification and semantic boundaries

The delivered scripts audit exact finite algebra, byte identity, degree,
coefficient height, coordinate liveness, source matching, and the stated
restoration maps. Independent arithmetic engines were used for the direct
expansion and the integer coordinate maps. Finite regression checks and
exact symbolic identity checks have distinct scopes, stated in their
receipts. Neither kind of finite check replaces the universal arguments in
the article or the inherited semantic calibration.

The integer maps preserve the relevant zero sets through explicit
polynomial bijections; the two direct quartics are related by projection
and nonnegative affine restoration. Their ambient domains remain different:
the direct unknowns are nonnegative integers, and the coordinate-family
unknowns are unrestricted integers. The source dependencies are ordinary
mathematical premises proved in the identified earlier developments, not
additional unknowns or free parameters in the delivered equations.

This delivery asserts the stated consistency equivalences through those
arguments. It does not decide whether any delivered equation has a zero,
prove ZFC consistent or inconsistent, provide a new fully checked
end-to-end Lean/Rocq certificate, or contain a separately encoded
object-language ZFC derivation. It claims improvements relative to the
inspected repository snapshot and six incoming archives, not a global
minimum or established priority over all prior work. Independent reviews
here were separate tasks in one AI-assisted collaboration, not external
human peer review.

## Licenses and inherited notices

Newly prepared prose, constructions, and checking code follow the
repository's MIT No Attribution license; see [LICENSE](LICENSE).
Inherited material retains its own license and attribution context.
The coordinate component includes `upstream/licenses/LICENSE`,
`LICENSE.ProveIt`, `LICENSE.Wade`, and the original `NOTICE71.md`.
The Wade license preserves the Andrew James Wade copyright notice.
`NOTICE71.md` is an inherited historical notice: its references to what was
new in source71 and to that earlier source snapshot do not describe the
new contribution of this delivery. This provenance file does not relicense
any inherited material or claim authorship of inherited constructions.

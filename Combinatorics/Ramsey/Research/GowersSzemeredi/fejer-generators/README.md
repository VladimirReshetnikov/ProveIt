# Generators of the Fejér-route modules (Notes L.16d–L.16e)

Most modules of the Fejér route are copies of corpus modules with the
printed θ₁, Bohr radius, Lemma 15.6 threshold and class degree replaced.
These scripts made the copies. Each one reads its corpus original(s),
applies exact-string and word-boundary substitutions, and asserts a guard
regex that no printed name survives (`section16ThetaOne`, `section16Zeta`,
`lemma156ExplicitThreshold`, `globalBudget`, `stepP`, `uDeg68`, …).
The substitutions are the record of how a copy differs from its original,
which is what the planned fold-in refactor needs (notes L.16e, "Refactor
map").

| script | output module(s) | original(s) |
|---|---|---|
| `assemble_fejer.py` | `Proofs15FejerSelection` | `Proofs15Restriction` (+ hand-written Fejér part) |
| `assemble_fejer156.py` | `Proofs15FejerProduct` | `Proofs15ProductToRestriction` (+ hand-written part) |
| `assemble_l5with.py` | `Proofs16Lemma5With` | `Proofs16Lemma5`, `Proofs16ArrangementSelection` |
| `assemble_dswith.py` | `Proofs16DenseSelectionWith` | `Proofs16DenseSelection`, `Proofs16CommonBase`, … |
| `assemble_pptwith.py` | `Proofs16PolyPieceTwoDataWith` | `Proofs16PolyPieceTwoData` |
| `assemble_pctfejer.py` | `Proofs16PolyCoverTwoFejer` | `Proofs16PolyCoverTwo` |
| `assemble_seedexp.py` | `Proofs18FejerSeedExponents` | `Proofs18LengthSixCounts`, `…Exponents` |
| `assemble_uctfejer.py` | `Proofs16UniformCoverTwoFejer` | `Proofs16UniformCoverTwo(Bounds)`, `Proofs16PowerUniformClass` |
| `assemble_cpwith.py` | `Proofs16ClassPiecesWith` | `Proofs16ClassPieces` |
| `assemble_csfejer.py` | `Proofs16ClassStepFejer` | `Proofs16ClassStep` |
| `assemble_csdfejer.py` | `Proofs16ClassStepDegreesFejer` | `Proofs16ClassStepDegrees` |
| `assemble_ssfejer.py` | `Proofs16SplitStepFejer` | `Proofs16SplitStepBounds` (+ hand-written recursion) |
| `assemble_spcgw.py` | `Proofs16SinglePieceCoverGlobalWith` | `Proofs16SinglePieceCoverGlobal` |
| `assemble_spcinvf.py` | `Proofs18SinglePieceCoverInverseFejer` | `Proofs18SinglePieceCoverInverse` |
| `assemble_coverf.py` | `Proofs18Cover{Modulus,Density,Exponents}Fejer` | `Proofs18Cover{Modulus,Density,Exponents}` |
| `assemble_headf.py` | `Proofs18CoverFejerHeadline` | `Proofs18CoverDegrees`, `…TightBase`, `…ThresholdsSharp` (+ hand-written closed forms) |
| `mk_fejer_low_short.py` | `Proofs18CoverFejerLowDegrees`, `…ShortLengths` | `Proofs18CoverSharperLowDegrees`, `Proofs18CoverThresholdsSharp` |
| `assemble_l163sharp.py` | `Proofs16BaseCaseRestrictionSharp` | `Proofs16BaseCaseRestriction` |
| `assemble_febq.py` | `Proofs18FejerEnvelopeBaseQ` | `Proofs18GenericEnvelopeBase` (atom `2^(k+5)` ↦ `5k+14`) |
| `assemble_coverq.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerQ` | the `…Fejer` modules (`uDegQ`, `fixDegQ`) |
| `assemble_headq.py` | `Proofs18CoverFejerHeadlineQ` | `Proofs18CoverFejerHeadline` (+ hand-written closed forms) |
| `assemble_polyf.py` | `Proofs16PolynomialFejer` | `Proofs16PolynomialStructure`, `…Corollary` |
| `mkstub_fejer18.py`, `mkstub_auditfejer.py` | stub checks of `Proofs18CoverFejerAllDegrees` and the Fejér block of `CompletionAudit.lean` | — |

Hand-written modules (no generator): `Proofs15WalshGeneral`,
`Proofs15DegenerateRange`, `Proofs16TightRadius`, `Proofs16SplitFejerDegrees`,
`Proofs18FejerSeedCounts`, `Proofs16ClassStepBoundsFejer`,
`Proofs18TightClassesFejer`, `Proofs18TightClassesFejerQ`, `Proofs18FejerEnvelopeBase` and the bridge
`Proofs18CoverFejerAllDegrees`.

Caveats:
* The scripts hard-code the worktree path where they ran, and some outputs
  were edited by hand after generation (compile fixes). The committed
  modules are authoritative; the scripts document the substitutions.
* Two scripts read session-local inputs that are not committed: the
  hand-written Fejér parts of `assemble_fejer.py` / `assemble_fejer156.py`
  (now contained in the output modules), and `StubAll18.lean` for the stub
  checks. That file states the heavy corpus theorems as axioms, so it is
  deliberately kept out of the repository.

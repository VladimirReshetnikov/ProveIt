# Source audit and attribution

The requested Wikipedia article supplies the subject boundary. The report
develops proofs rather than relying on Wikipedia as a proof authority.
`coverage_map.json` records 59 selected immediate outgoing topic links,
including the parent-link identifiers, target URLs, theorem IDs, scope
qualifications, and topics deliberately left unproved. It is not an
exhaustive census of every link or statement on the page.

## ProveIt

`proveit_source_audit.json` pins the inspected source to commit
`3eb195cab4cc3d552a9eca78880c6d428f3e44f9`. Each entry records its path,
Git blob identity, precise inspection scope, stable revision URL, and intended
reuse. The root toolchain is Lean 4.32.0.

The useful existing interfaces are the finite PR syntax and iPRA derivation
calculus, bounded-formula compilation and induction, and the diagonal-clock
arithmetic estimates. The earlier November 20 complexity packet supplies
compatible foundations and a prior object-proof roadmap. Its README's
statement about a checked semantic core is recorded as the packet's own
claim; it was not independently rebuilt in this work. The repository's
intake README likewise distinguishes delivered research packets from
verified derivation modules.

The new report does not conflate an inspected source file with a successful
local kernel build. It also does not use the proof-graph theorem
`ReachableFrontier.lean` as an arithmetic configuration-graph theorem.

## External mathematical sources

The complete bibliography, with primary-paper and official-source links, is
in `sections/bibliography.tex` and the PDF. The subject-specific manifests
record the NP/completeness, space, and randomized/lower-bound source checks.
The main historical anchors are Cook and Karp on completeness, Savitch on
space simulation, Immerman and Szelepcsényi on space complementation,
Hartmanis–Stearns on hierarchy arguments, Chandra–Kozen–Stockmeyer on
alternation, Adleman and Lautemann on random computation, Shannon on
circuits, and Adleman–DeMarrais–Huang on quantum simulation.

The report supplies its own finite proof constructions, constants,
encodings, and arithmetic interpretations. Named classical results are not
claimed as original discoveries. Primary papers and official author/course
notes were used to check the established statements and distinguish the
restricted versions proved here from stronger theorems.

## Access limits

- The full Adleman 1978 paper was not retrieved. Its bibliography is historical
  attribution; the finite advice proof was developed explicitly and checked
  against official instructor notes.
- Lautemann's and the quantum-computability paper's publisher abstracts were
  retrieved. Their complete proofs are not represented as having been read.
- Shannon's official publication record supplies bibliographic attribution.
  The report independently specifies a Boolean basis and explicit constants.
- Access to the author-hosted Arora–Barak draft was inconsistent. It is an
  orientation reference, not a dependency of an omitted proof.
- Shi's quantum universality result and Babai's graph-isomorphism result are
  context only. Their iPRA reconstructions are not supplied.
- The large main ProveIt Derivations README was not returned in readable full
  form. The audit claims only the individual source files and selected
  directory information actually inspected.

## Verification boundary

`../CLAIMS.json` separates the human-readable proof status of every result
from the uncompiled Lean outline and the absent completed new object-iPRA
certificate. `../validation/` records finite implementation checks and PDF
verification. No test result is used as a substitute for a general proof,
and no repository build or repository modification is claimed.


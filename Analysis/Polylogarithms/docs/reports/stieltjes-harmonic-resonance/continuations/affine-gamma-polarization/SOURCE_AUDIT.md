# Source audit and provenance

Repository: VladimirReshetnikov/ProveIt.
Final metadata anchor: `92ee3aaf3087c0e0c29b9ed952e777de5d6accd0`.
Inspection date: 11 October 2026.

## Direct proof inputs

The canonical normal-form and differential-polynomial chapters were read as
repository TeX. The immediate predecessor is *Exact Harmonic-Tail Reconstruction
and Variational Gamma Identities*, especially its complete u0,u1,u2 sector and
Section 8 research question 5. Its relevant source identity was checked at the
anchor. Some initial reads used the default branch; the returned blob identifiers
are preserved in `data/source_manifest.json`.

The source question asks for the next Gamma projection including u3^2 with
arbitrary u1,u2 powers. This continuation proves the b=0 family in
u0^a u1^k u2^b u3^2, and its analogous square sector at every higher derivative
order. It does not claim the entire question is solved.

The predecessor already supplies the pure-square and r=2 cases, as well as the
normal-form decomposition, f0, and relevant parity. They are not new claims.

## Incoming archives: metadata only

Five archives were returned by the repository directory read. The GitHub
connection does not return their binary contents and the runtime network was
unavailable, so these ZIPs were not extracted. Their names, sizes, and Git blob
identifiers are recorded in the manifest. Their presence does not establish
that their proofs have been reviewed.

Matching-title Library TeX abstracts were read for *Higher Quadratic Spectral
Jets*, *Beta Polarization of Higher Spectral Defects*, and *Finite-Difference
Determinants*. Their file identities and read scope are recorded. No identity
between these Library files and the incoming ZIP members was established.
Other title searches did not provide matching sources; no claim about their
nonexistence follows.

## Primary literature

Guo, Regensburger, and Rosenkranz provide the classical functional-monomial
background. NIST DLMF supplies standard special-function conventions and
identities. Espinosa and Moll's primary preprint abstracts were checked for the
established definite/indefinite Hurwitz-integral literature; the full papers were
not systematically compared formula by formula. Consequently individual explicit
integrals here are not claimed to be historically unprecedented.

The manuscript's bibliography cites these sources, and the report provides its
own proofs for all new assertions. The single-zeta selector necessity statement
is over C(s), not an arithmetic-independence claim at fixed values.

## Corrections and limits

No false inherited numbered theorem was established in the targeted audit.
An apparent duplicated full-Cayley/1,032-input first-X-family overview paragraph
in the inspected canonical README is an editorial observation; verify against
the current file before deleting a copy. The package's mathematical safeguards
are not presented as accusations that earlier sources ignored them.

No repository writes, commits, branches, or pull requests were created.
Git blob identifiers identify source content in Git's object format. They are
not falsely labeled SHA-256 hashes of locally acquired source files.

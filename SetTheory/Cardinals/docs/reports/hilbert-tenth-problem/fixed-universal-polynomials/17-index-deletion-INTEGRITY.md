# Integrity and assurance boundaries

## Trust chain

The externally supplied archive SHA256 is the authenticity anchor. After
checking it independently, the root verifier pins the exact enclosing
`MANIFEST.json`. That manifest allowlists every payload path, length, mode and
SHA256; the verifier's one self-pin line is normalized to 64 zeros solely for
its manifest entry. `SHA256SUMS` records actual bytes, including the actual
pinned verifier and the manifest. Neither inventory lists itself recursively.

The separately frozen 9-member smooth-radix packet is preserved under
`smooth/`, with its own manifest/proof pins and explicit root/author attribution.
It inherits the unchanged factorial proof and does not replace its source.

The complete 49-member scientific packet is preserved byte-exactly under
`evidence/`, with its original source manifest pinned separately. Every source
member is checked before any copied mathematical checker runs. Symlinks,
special files, missing or extra files/directories, changed modes, duplicate
JSON keys, nonfinite numbers, altered receipts and unexpected checker scripts
are rejected. The original independent proof/audit/checks retain their exact
historical attribution; author-attributed final-byte replays are separate.

The original preliminary proof contains a j=2 strict-upper-bound endpoint
erratum: equality holds there, strictness starts at j=3, and the non-strict
bound starts at j=1. Relevant source applications j=4,5 and full-family
indices p>=55,n>=40 are unaffected. The article corrects it and documents it;
no frozen scientific member is silently replaced. See README and the source
review record for the other recorded peripheral endpoint correction.

## Execution and output contracts

Only newly authored mathematical checkers are allowlisted. The verifier
inspects stored source rows structurally; it never interprets/evaluates their
arithmetic schedule or imports upstream programs. Historical `.py.txt` and
nonallowlisted Python programs remain inert. Finite receipts do not replace
or prove the universal symbolic theorem, nor do they materialize the giant
full witness tuple. No network, package installation or public mutation is
performed by these release tools.

The supported enclosing replay is `verify_release.py --replay`. It captures
stdout and can export receipts only into a fresh external directory. Frozen
checker `--output` guards are relative to their scientific packet, not the
whole enclosing release: direct checker output into the enclosing root is
therefore outside the supported contract. The wrapper never uses checker
`--output`. Guard QA exercises direct checkers only in authenticated disposable
copies and verifies that valid external files exactly match their stdout.

All successful root tool stdout is one deterministic JSON value with sorted
keys, two-space indentation and a final newline. Scientific checker receipts
retain their original exact canonical formatting and ordering. Failures raise
explicit exceptions or return nonzero and do not depend on Python `assert`.
Expected receipts are compared recursively by exact JSON type (including
bool versus int and float versus int), key set, length and value, plus exact
saved bytes. Original bytes, modes and mtimes are checked for nonmutation.

## Threat model and limits

The tools defend against accidental changes and hostile received archives,
not an active privileged process racing writes in the local filesystem or a
compromised Python/TeX runtime. Verifying Python is itself trusted only after
external authentication. The checker inventory does not establish scientific
truth. PDF/ZIP byte reproducibility is scoped to the recorded build/runtime
environment; toolchain upgrades may change bytes. Final article approval is
author/coordinator QA, not a claim of independent security review or a second
independent mathematical review of all final bytes.

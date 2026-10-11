# Complete Cayley ideal and the bounded S6 obstruction

This contribution proves that the existing weight-seven S6 target lies
outside the **full convergent Cayley shuffle ideal plus the inherited
5,131-row finite relation span of depth at most four**. The additional
ideal is unrestricted in depth and includes all shuffle multiples of all
convergent Cayley rows. The actual polylogarithm identity for S6 remains
conjectural; this theorem does not assert that its numerical residual is
nonzero.

The new step is exact verification that the inherited separating
functional kills every `w - Pi_up(w)` on the complete 2,546-element
weight-seven, depth-at-most-four, conjugation-odd word basis. The projector
kernel theorem and depth preservation then identify the whole ideal
intersection. This closes the specific projected search proposed at the
end of the prior depth-projector article.

## Replay

From this directory run:

```sh
python code/verify_complete_cayley.py
```

Python 3.10 or later and its standard library are sufficient. A fresh run
takes about 30 seconds in the preparation environment and writes
`verification.json`. All row entries, the functional, and the target
pairing use exact integers or rational fractions. The proof does not use
modular ranks, cached matrices, numerical polylogarithms, or PSLQ.

The replay performs the following checks:

- SHA-256 integrity of both pinned source modules and the functional data.
- Independent enumeration of all 5,131 inherited rows and exact zero pairing.
- All 2,546 complete-ideal basis differences, with admissibility, weight,
  conjugation parity, and depth checks.
- Exact nonzero pairing against the reconstructed formal target, normalized
  as 128,588 times the real conjectural residual before multiplying by `i`.
- Independent consecutive-cut Eulerian checks on all 780 words through
  weight four, 2,150 shuffle-product checks, and projector convention checks.

The exact target pairing is:

```text
-186660627289236812620583691130496682078843750753489297279472069700354208
```

This integer is a formal linear-functional pairing. It is not a decimal
approximation to a period.

## Files and provenance

- `section.tex`: manuscript-ready statement, complete algebraic argument,
  finite certificate specification, and research consequences.
- `references.tex`: bibliography entries for the section.
- `code/verify_complete_cayley.py`: new standalone replay and independent
  small convention checks.
- `code/depth_projector.py`: byte-for-byte pinned projector source.
- `code/bounded_relations.py`: byte-for-byte pinned independent bounded-row
  verifier, renamed locally for import; its complete-family enumerator is
  used here.
- `data/separator.json`: the inherited integer functional expressed in the
  adapted basis. The basis is specified by a finite lexicographic rule,
  so a redundant coordinate list is omitted.
- `data/provenance.json`: pinned URLs and SHA-256/Git-blob hashes.
- `verification.json`: successful exact replay receipt.
- `SHA256SUMS`: package checksums.

All repository sources are pinned at commit
`5a790187c8e186e41e2b990b4941cb7a1a3c7b6b`. The two reused modules have
their exact source bytes preserved. The functional integers in JSON must
be parsed exactly; the supplied Python parser does so. Conversion to
IEEE-754 floating-point numbers would alter them.

The inherited functional, finite row family, and depth-preserving projector
are attributed to their respective source contributions. They are not
claimed as new here. No files in the inspected repository snapshot were
modified. Exploratory search matrices and modular computations are excluded
from this contribution because none is needed for its proof.

## Integration note

The section can follow the canonical S6 conjecture and discussion of the
restricted formal obstruction. Retain the conjectural status of S6 and the
revised S8. Replace the proposed step “complete the Cayley ideal and retry
the inherited depth-four rows” by the proved exclusion in this contribution.
The theorem allows arbitrary higher-depth Cayley intermediates, but it
does not show that every conceivable proof must pass through depth five:
another additional relation family may contain information absent from
the frozen 5,131-row span.


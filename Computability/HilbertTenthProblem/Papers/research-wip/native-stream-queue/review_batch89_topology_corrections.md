# Root follow-up to the batch-89 manuscript review

The [frozen scoped review](review_batch89_remaining_writes_e3e58a882.md)
is retained unchanged, including its revision-specific findings. Root read
that full review and independently checked all six resulting file hashes,
the three original ZIP manuscripts and their source-label mappings, all
old/new destination labels, and the unchanged Presburger article/README.
The archives are under repository-root `docs/incoming/` at8311efdd4.
Only inert bytes were read; no archived program was executed.

The independently reproduced counts are1799→1876 for surreal-well-orders
and156→296 for birthday-cutoffs. All original destination labels survive
once. The original47/42/52 manuscript labels all occur once with the new
`swo:gcz:`, `hset:zr:` and `hset:kw:` prefixes, respectively. The new prefix
totals are77/65/74. The PDFs were authenticated by hash only.

Root additionally read the actual uniform-presentation theorem and the
three finding locations. This follow-up corrects the two delivered-label
counts in the birthday-cutoffs LaTeX source:926 lines has42 labels, and911
lines has52 labels. It also makes the surreal-well-orders README summary
explicit about the fixed well-orders on D and C_D and Separation in the
expanded language; ordinary Choice supplies the code order in ZC. These
changes agree with the actual theorem and archived manuscript counts.
They change no theorem statement, label, fixed compiler or proof artifact.

The corrected text files have these SHA-256 values:

| File | SHA-256 |
|---|---|
| `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md` | `39479f7f2e45227d492c2745b9b0796dc9cf4aab899a8a73396bea27221a0fc1` |
| `Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.tex` | `3a7b220ecf749eef8a486455962b12e0ff7a43904dc8acb4752e5777c5b058f3` |

The exact patch contains only those presentation changes. All LaTeX labels
remain identical after the count correction. No PDF or Lean/LaTeX build was
regenerated; the birthday-cutoffs PDF still reflects the previously supplied
edition's provenance wording. Source-level correction and PDF certification
are therefore separate. No theorem or formalization certification follows.

At the reviewed horizon2efca7042, actual Part XV and Parts VI–VII resolve
three of the four earlier missing integrations. Presburger Part X remains
absent. This result supersedes only those three placement findings; the
full proofs, external Glazer interface and choiceless surreal interface
remain subject to the frozen review's stated limits. There is no paid
finite Diophantine compiler or arithmetic-bound improvement here.

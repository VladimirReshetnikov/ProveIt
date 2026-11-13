TWO SMALLER CHECKING PRESENTATIONS OF iPRA
13 November 2026

Start with ipra_conditional_image.pdf. Its self-contained LaTeX source is
ipra_conditional_image.tex.

RESULT
  code/checker_tokens239.py     239 tokens / 261 AST nodes / 553 bytes
  code/checker_ast257.py        246 tokens / 257 AST nodes / 593 bytes

The pinned corpus's prior compact coordinate envelope is 240 / 259 / 462,
attained by different programs. The two candidates improve token and AST
records separately. Neither beats the 462-byte record; no single candidate
beats all three coordinates. No mathematical axiom deletion or global
minimality is claimed. This is a verified implementation refinement of the
existing guarded presentation of a theory bi-interpretable with full iPRA.

SOURCE SNAPSHOT
  VladimirReshetnikov/ProveIt
  commit 95d3dd192e97a19bd4f8783c764331ec41126264
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

COMPACT INPUT CONTRACT
  First JSON line: canonical closed guarded Eq/D public formula in the
  inherited unshifted sorted-arity codec.
  Following consumed lines: packets [source, target, template].
  Raw trees: exact integers and lists.
  Acceptance: normal termination and exactly ACCEPT plus one newline.
  Exceptions reject; unused trailing input is allowed.

These modules do not independently validate the full public grammar or
whole-input JSON alphabet. They are not arbitrary-JSON validators. Their
contract is the same as the frozen compact token control. The report states
the full mathematical theory and separates the inherited bridge from the
new operational argument. The readable expansion explains the code without
being an uncounted dependency of either compact module.

REPRODUCTION (OFFLINE)
  python3 reproduce.py

Exact sizes were measured with CPython 3.12.14. Other versions may normalize
source differently. The regression suite runs both ordinary and optimized
Python and includes a proof using its induction hypothesis and a capture
attack rejected before its neutral-major packet is read.

SINGLE EXAMPLE
  python3 code/checker_tokens239.py < fixtures/global_computation_zero.jsonl
  python3 code/checker_ast257.py < fixtures/global_computation_zero.jsonl

PDF BUILD
  pdflatex -interaction=nonstopmode -halt-on-error ipra_conditional_image.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_conditional_image.tex

CONTENTS
  code/        Two compact candidates and a readable standalone expansion.
  reference/   Frozen 240-token, 259-AST and 462-byte controls; inherited
               return-reservation proof; original article Chapter 1 source.
  fixtures/    Eight source fixtures, including serious induction and scope.
  proofs/      Operational proof and independent model-agent review.
  evidence/    Measured results, regression and structural-check receipts.
  audit/       Reproducible read-only whole-corpus census and compressed
               exact source snapshot; no upstream code is run by the census.
  measure.py   Exact complete-module size checks.
  verify.py    Focused regression and source-transformation checks.
  reproduce.py Runs all checks and writes evidence/reproduction.json.
  PROVENANCE.json  Paths, snapshot, claims and source attribution.
  SHA256SUMS.txt   File checksums for this delivered package.

The inherited_ch01_base.tex reference is an unmodified fragment of the
upstream article and depends on that article's preamble. It is supplied as
evidence, not as a standalone compilation target. The report's own .tex file
is standalone and embeds its code listing.

The census strips leading docstrings in addition to normalizing source,
which helps avoid missing earlier records hidden by documentation. The five
compact comparison modules have no docstrings, so the reported record
counts are identical with or without that extra census step. Unsound
negative controls, packed launchers, generators and test runners are
explicitly excluded from the complete-checker comparison. Quoted generated
program templates are not exhaustively enumerated.

The arithmetic and logical basis, public guarded translation, interpretation
maps and their round-trip theorems belong to the existing ProveIt work.
Return reservation, match capture and initialization factoring were also
already present. The new contribution is conditional-image factoring and
its measured compositions. Independent review here means a separate model
agent's review, not external human peer review. No new Lean/Rocq verification
of the Python implementation is claimed.

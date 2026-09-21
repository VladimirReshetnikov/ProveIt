# Monotone Blocks and Reverse Replies

**Proposed solution of Conjecture 2.9 in Henning Ulfarsson,
“A Permutation Avoidance Game with Reverse Replies and Monotone Traps”,
arXiv:2603.16004v1.**

For every k >= 3 and

    n >= R(k) = k + (k+1)^2 (k-2)^2 + 1,

Player II wins the normal-play permutation-avoidance game on S_n by always
replying to a length-k pattern with its reversal.

The article contains a complete elementary proof. Its key minimal-core lemma
isolates one member of an arbitrary set of nonmonotone patterns of a common
length inside a one-monotone-block family. A same-cell Erdős–Szekeres argument
extracts such a family from a sufficiently long witness. Symmetry orients the
isolated target, and inflation restores the exact original length.

This is an AI-assisted research draft, not an independently refereed or
proof-assistant-verified result. The tests are supplemental. No finite
computation is an assumption in the universal proof. The least eventual
threshold is not determined.

## Contents

- `article.pdf`: the 14-page article, including all proofs and a proof audit.
- `article.tex`: complete, standalone LaTeX source; bibliography is embedded.
- `code/reverse_reply.py`: exact, integer-only constructive implementation.
- `code/verify.py`: independent direct-subsequence checks, exhaustive small
  templates, sampled larger templates, 100 constructed replies, ES tests,
  and a full worked certificate at k=5, n=330.
- `code/explore_supports.py`: optional reproducible discovery exploration.
- `data/verification.json` and `data/verification.log`: executed test results.
- `data/worked_certificate.json`: all data for the worked length-330 witness.
- `data/exploration_summary.json`: the original discovery counts for k=5,6.
- `data/exploration_k5.json`, `data/exploration_k6.json`: independently rerun
  summaries from the packaged exploration script.
- `area_selection.json`, `select_area.py`: the recorded single random draw
  from 96 areas and the script that performed it.
- `STATUS.md`, `SOURCES.md`, `notes/selection_and_exclusions.md`: claim scope,
  source audit, and manifest-exclusion record.
- `build.sh`: PDF build command.

## Reproduce

Python 3.10+ with only its standard library is sufficient:

    python code/verify.py
    python code/explore_supports.py --k 5
    python code/explore_supports.py --k 6

The exploration is optional. `--witnesses` also writes all distinct-shadow
certificates, making a larger JSON. The recorded k=5 and k=6 counts are 8,640
and 70,560 marked signed templates respectively, with no failed supports.
These counts are not a general game-tree search.

The production API uses **one-based permutation values** and **zero-based
position indices**. The independent exploratory script uses zero-based
permutation values internally; it labels any serialized witnesses accordingly.

To build the PDF with a standard TeX Live installation:

    ./build.sh

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times to resolve all cross-references. No external bibliography processor
or network access is needed.

`select_area.py` intentionally refuses to draw again while the recorded JSON
exists. The selection was one OS-random draw, index 9 (zero based), selecting
“Permutation patterns”. The deterministic seed in the verifier is unrelated.

## API example

Add the package's `code/` directory to `sys.path`, or run a script from that
directory, and import `reverse_reply`. For example, from the package root:

    import sys
    sys.path.insert(0, "code")
    from reverse_reply import Template, construct_reply
    T = Template((1, 2, 4, 6, 3, 5), 4, -1)
    pi = T.inflate(325)
    rho, certificate = construct_reply(
        pi, (1, 2, 3, 5, 4), (0, 1, 2, 3, 329)
    )
    assert len(rho) == 330

A supplied marked occurrence avoids the potentially expensive search for an
occurrence in an arbitrary long permutation. The constructor checks the finite
extracted template against any supplied forbidden set and validates the final
compressed certificate. It does not pretend to enumerate every k-subsequence
of the large input or output.

## License and provenance

Original text and code in this package are released under MIT-0; see LICENSE.
No third-party articles or font files are bundled. The user-supplied manifest
is not redistributed: its hash and the exclusion analysis are recorded instead.

# openai-math preprints (vendored, unmodified)

This directory holds unmodified copies of selected manuscript directories
from the `preprints/` tree of [openai/math](https://github.com/openai/math).
It holds no Lean code and is not part of the `OAI` Lake library described in
[`../README.md`](../README.md).

## The Exponential Time Hypothesis is False (25 October 2026)

- Upstream URL:
  <https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026>
- Pinned commit: `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, then the head of
  `main`, committed 2026-10-26T21:18:03Z ("Merge pull request #3 from
  openai/codex/update-10-26"). Pinned tree:
  <https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026>
- Fetched: 2026-10-26, with a shallow, blobless, sparse `git clone` of
  `https://github.com/openai/math.git`. Each file was written from
  `git cat-file blob`, so no line-ending or other filter was applied.
- Copied byte for byte, with no file renamed, changed or added. These Git blob
  IDs equal both the upstream tree entries and this repository's index
  entries:

| Path in `The-Exponential-Time-Hypothesis-is-False-October-25-2026/` | Bytes | Git blob |
|---|---:|---|
| [`README.md`](The-Exponential-Time-Hypothesis-is-False-October-25-2026/README.md) | 551 | `4fed045323c329be85bc53cf46dfaa6efbf3759f` |
| [`paper.pdf`](The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf) | 887,884 | `0503566e95bc587a4076573a45132d97531b8ba6` |
| [`build/main_full_version.tex`](The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex) | 214,857 | `f7af85e623b58e0ca9f4b9416916d442defa963a` |
| [`build/quantitative-reduction.tex`](The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex) | 17,832 | `80389ac39d987133b71b2ddc2593e6fcdd99871a` |
| [`build/quantitative-contraction.tex`](The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex) | 27,544 | `51ba54efc29f51bbc0426f848003030da484f354` |
| [`build/quantitative-circuits.tex`](The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-circuits.tex) | 4,152 | `e25def5eb03ee53feefd3fe480dd5a1293761fae` |

The four `.tex` files and `README.md` use LF line endings upstream. The root
`.gitattributes` treats `*.pdf` as binary. The repository index therefore
holds exactly the upstream bytes. The root `.gitignore` ignores every
`build/` directory, so the four upstream `build/*.tex` sources were added with
`git add -f` to keep the upstream layout. Once tracked, they are versioned
like any other file.

The same directory is blob-for-blob identical at the earlier upstream commit
`42907c9e999cc00d6abe7a50bfc1023250edd1b9`, which two of the ProveIt
analysis packets pin.

## License

Upstream licenses the repository under the Apache License, Version 2.0, and
its `preprints/` tree has no separate license file. [`LICENSE`](LICENSE) is
the upstream root `LICENSE` at the pinned commit, unchanged (blob
`261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`). It is byte-identical to
[`../LICENSE`](../LICENSE), which accompanies the Lean port. That license,
not the repository's MIT-0 license, governs these files. Copyright remains
with the upstream copyright holders. The upstream repository supplies no
individualized copyright notice and no `NOTICE` file. This record adds no
copyright notice.

## Use in ProveIt

The manuscript is the primary source of
[`Computability/SubexponentialSAT/`](../../../Computability/SubexponentialSAT/README.md),
whose analysis packets cite it by path and Git blob. Nothing in ProveIt
compiles, builds or modifies these files. The upstream Lean development for
this paper (`lean/OAI/Algorithms/SubexponentialSAT/`) is not vendored.

# Independent review of the AQ22 display wording refresh

This audit covers the earlier author-only disclosure. The current PDF has a
later paired-replay wording refresh; its formula, constants and circuit are
unchanged, and a [separate refresh review](../equation10-22-paired-wording-independent-audit/README.md)
has passed.

This review compares the refreshed generator and TeX with their exact
previously audited versions in commit `7158586014`: in each, the only change
is the same replacement of the three-line unproved-status paragraph with the
four-line historical author-only status paragraph. The pinned graph is
unchanged. Therefore the 22 variable names, equation, four fixed ports,
base-10 decoder and 114 circuit lines retain the scope of the earlier
[presentation audit](../equation10-22-independent-audit/README.md), whose
PDF and status wording are now historical.

The [historical author run](../ipra-aq22-guarded-author/README.md) and its
[independent recorded-artifact audit](../ipra-aq22-guarded-author-independent-audit/README.md)
support the wording's qualified claims about witness transport and the
internal iPRA equivalence to a translated consistency sentence. They do not
constitute a matched peer replay or formally identify the displayed PDF and
its fixed ports with the Lean endpoint. The fixed-integer decoder and rank
recipe retains the manual-transcription boundary recorded in the earlier
presentation audit; the source wording does not close it.

Run the checker with ordinary Python and the existing TeX installation:

```sh
python3 Computability/DiophantineConsistency/reviews/equation10-22-wording-independent-audit/audit.py
```

It refuses to overwrite its receipt. To rerun, use a copy of the repository
and remove only that copy's receipt. It checks both original files against
the previous audit's recorded hashes, requires exactly the stated paragraph
replacement, and invokes the current generator in two independent temporary
trees. Each invocation itself compiles twice and rejects TeX layout or font
warnings; all four compilations yield the recorded PDF hash. The normal run
exited zero; optimized Python is deliberately rejected. The first attempted
version used mutable `HEAD` for the baseline and failed once the display was
committed concurrently; the final checker instead pins the prior commit.

The refreshed PDF has two letter pages. Visual inspection of 120 dpi
`pdftoppm` renderings found no apparent clipping or overlap. `page-1.png`
records the changed first page; the second page's render is byte-identical to
the earlier audit's `page-2.png`. This visual assessment is not a formal
layout proof. The [terminal observation](terminal-observation.json) records
the process exit, render hashes, and new PDF digest.

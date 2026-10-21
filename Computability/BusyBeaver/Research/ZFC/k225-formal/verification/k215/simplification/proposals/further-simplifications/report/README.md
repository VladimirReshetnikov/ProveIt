# Follow-up report

`report.pdf` is the seven-page reviewed report. `report.tex` is its editable LaTeX source. The production review cutoff is 0359ebda60aaf52758358e1450a04988136db67e; historical finite experiments retain their original beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc pins.

Run `sh build.sh` with a conventional TeX Live installation providing pdfLaTeX, Latin Modern, AMS, microtype, fancyhdr, enumitem, booktabs, xurl and hyperref. The optional `K215_TEXFORMATS` environment variable supports a separately installed format tree; it is not required on a normal TeX installation.

`qa/QA.json` records the final refreshed document hashes, rendering and seven-page visual inspection. This confirms PDF preparation only. No new Lean or Rocq formal draft in the follow-up was compiled.

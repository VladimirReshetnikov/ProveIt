Optional isolated TeX runner

A normal TeX Live or MiKTeX installation can compile report/report.tex with
ordinary pdflatex passes. No custom format is needed on such an installation.

The preparation environment contained installed TeX sources and fonts but
had dangling TeX cache/configuration symlinks. compile_report_isolated.py
provides an optional Linux fallback for that specific class of installation:

  python3 build_support/compile_report_isolated.py report/report.tex

The helper builds a private pdfLaTeX format from installed latex.ltx, creates
a private Latin Modern/AMS font map, and runs three actual pdfLaTeX passes.
It uses standard-library Python, pdftex, pdflatex, and the existing installed
TeX files. It uses no network and writes no system configuration or cache.
The default private work area is /tmp/pa194_tex; use --workarea to select
another writable directory. --passes changes the number of TeX passes.

The supplied report PDF was compiled from the supplied TeX sources.

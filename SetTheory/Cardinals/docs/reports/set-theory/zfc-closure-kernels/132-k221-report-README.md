# K221 report

The report gives the exact 221-state construction, the recent-commit comparison, three closed source rotations, the inductive whole-tape fold, unchanged logical calibration, certificate scope, and all 442 canonical transition rows.

From this directory, regenerate the appendix using:

    python3 generate_table.py ../machine/k221.tm
    sh build.sh

A conventional TeX Live installation with Latin Modern and the packages listed in report.tex is sufficient. The build script includes optional fallbacks for the research container's separated font and format trees; they are not additional mathematical inputs. An existing format directory may be selected using K221_TEXFORMATS.

Release files: report.pdf, report.tex, metadata.tex, transition_table.tex, generate_table.py, build.sh, README.md, validation.json. Build logs, auxiliary TeX files, rendered PNGs, and temporary text extraction are inspection aids, not required release inputs.

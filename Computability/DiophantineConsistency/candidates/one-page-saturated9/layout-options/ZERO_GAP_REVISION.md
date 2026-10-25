# Minimal v5 zero paragraph gap: preparation only

Root selected exactly `\\setlength{\\parskip}{.8pt}` to
`\\setlength{\\parskip}{0pt}` after the reviewed v4 scratch render
showed a one-for-one0.2point outer-height reduction and still rejected
0.26492points of vertical overflow on onepage/163647bytes. There was no
horizontal overflow. Closed history/v4 preserves its full original
checkpoint and failure transcript; every earlier history remains exact.

No other TeX parameter, font, formula, numeral, seed character or executable
byte changes. equation.tex is the exact nine-point-zero-gap.tex option.
This revision is unexecuted and needs both delta reviews and root release
before any command. The strict overflow guard is not weakened. No silent
fallback, source/parent program, Lean or canonical change is authorized.

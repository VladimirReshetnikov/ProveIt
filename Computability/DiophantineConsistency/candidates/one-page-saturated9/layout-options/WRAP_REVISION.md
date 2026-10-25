# Minimal v3 wrap: preparation only

Root selected one further line break in the reviewed tighter9-point TeX:

    -2p(105,398,611,858,1452,1542)+2p(299,326,1326,1521)

is displayed on two lines, with the second beginning +2p. No mathematical
symbol, coefficient, exponent, seed character, font or other layout
parameter changes. The two actual programs remain byte-identical to v2.
Current equation.tex is the exact nine-point-wrap.tex copy.

The actual v2 first render reached onepage/163624bytes with no vertical
overflow, but failed its10.7589-point kernel hbox guard. Its full original
closure/transcript are preserved in closed history/v2; history/v1 remains
unchanged. Neither attempt materialized a PDF/success artifact or ran the
actual auditor/rebuild. The new one-line-wrap fit is untested.

Both delta reviews and a separate explicit root rerun release must precede
any new command. There is no automatic font fallback or canonical change.

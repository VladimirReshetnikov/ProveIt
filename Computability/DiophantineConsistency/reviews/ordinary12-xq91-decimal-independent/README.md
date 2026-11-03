# Independent review of the 91-operation decimal display

The 91-operation [TeX](../../research/ordinary12-xq91-decimal-display/equation.tex)
and [PDF](../../research/ordinary12-xq91-decimal-display/equation.pdf) display
passed the external checks below. The first PDF page was visually inspected:
the two columns are legible and fit on the page. It names twelve distinct
positive unknowns `a,b,c,d,e,f,g,h,i,j,k,ℓ`, marks `r01`–`r91` as
abbreviations, and explicitly specifies integer subtraction and possibly
negative intermediate values.

The checker independently reconstructs every TeX row and every PDF-extracted
row from the pinned 91-operation JSON graph, including all coordinate and port
mappings. Both complete 91-row sequences and `r91=0` agree. It extracts and
checks all 41 ordered slots and all 943 decimal selector blocks, preserving
leading zeroes. PDF-extracted text on the three constant/table pages is
identical to the separately checked 92-operation display; this is text
comparison, not pixel-level identity or a formal PDF semantics theorem.

The checker recomputes all four fixed integers from the displayed recipes,
PDF-extracted slots and selector blocks, using shifts to construct the powers
of two. Each complete little-endian integer matches the corresponding
hash-checked, decompressed supplement payload. It also reruns the separate
independent graph and degree audit, which checks the exact total degree 172
stated on the PDF's first page. These are external finite calculations; they
are not Lean proofs about JSON, compressed files, TeX or PDF.

Both recorded display builds are byte-identical to each other and the
canonical files, with no overfull LaTeX boxes. The four-page PDF has 1,754
extracted word boxes and a minimum reported margin of 28.028 points; no word
box extends past a page edge. Poppler emits an XML-invalid control character
for one math delimiter, removed before the bounding-box XML is parsed. The
separate author display checkers both reran with empty stderr and reproduced
their captured outputs. The separately maintained root 14-variable TeX and
PDF still match their pinned hashes.

Run `python3 -I -S -B check.py` from this directory, or pass its path from
another directory. The read-only check pins the graph, TeX, PDF, reference
PDF, table sources, coefficient manifest, relevant author artifacts and root
equation, and rehashes its inputs after evaluation. Its captured run exited
zero with empty stderr; see `observations/stdout`. No Lean process was started.

The displayed fixed coefficients and PDF are connected to the Lean
expressions by these external checks. The checked fixed-port model theorem is
not an internal iPRA proof. Full file/PDF semantics and the coherent internal
iPRA endpoint remain separate obligations.

# Twelve-variable, 89-operation decimal display

`equation.tex` and `equation.pdf` display the absorbed-witness graph using
twelve distinct positive integer unknowns `a,b,c,d,e,f,g,h,i,j,k,ℓ`.
Registers `r01` through `r89` are abbreviations, not additional unknowns;
subtraction is ordinary integer subtraction. All printed numerals and the 943
fixed selectors use base-10 notation. The four fixed integers are specified
by formulas and the decimal selector table, making the display self-contained.
The maintained root equation and the separate 90-operation display are not
modified.

The pinned graph has 89 live arithmetic operations: 50 multiplications,
22 additions, and 17 subtractions. `check-degree.py` checks exact degree 172:
it proves a degree upper bound and computes a nonzero leading coefficient
`960910299` modulo `1000000007` under a one-variable specialization of the
fixed-coefficient graph. These are external finite checks.

The 89/90 positive-zero existence equivalence has been checked in the stated
IΣ₁ models under the port bounds and independently reviewed in
`../../reviews/ordinary12-absorb89-equivalence-independent/`. An author
fixed-port model halt bridge is recorded in `../ordinary12-absorb89-probe/HALT.md`.
The shifted Lean byte-port graph has a guarded [iPRA endpoint](../ordinary12-absorb89-ipra-join/README.md),
whose receipt passed independent audit without another Lean replay. There is
no Lean parser or file theorem binding this TeX or PDF to the Lean expression;
the display checks below are external transcription checks. Package-transitive,
dynamic and full historical source-to-object ancestry remain inherited.

Run `python3 -I -S -B generate.py --output build01` and similarly for a new
`build02`. The retained fresh builds have byte-identical TeX and PDF. The
captured `check_display.py` checks every printed graph row, all 943 decimal
selectors and 41 slots, the formula tokens, and all four complete coefficient
payloads. `independent_check.py` separately checks extracted PDF rows,
coefficient pages, selector and slot data, full payloads, and page bounds.
`capture_checks.py` retains both checks plus the degree check and before/after
hashes of the draft, root equation, 90-operation display, and inputs under
`observations/checks01/`. The first two PDF pages were visually inspected.

The TeX SHA-256 is
`06651ac929dd8f06ea1ef9cf4745bd29ba31d53fe2fc576241a2b8d15ed3ee0e`;
the PDF SHA-256 is
`24416713afb5f79f33c24486255520fec6cc286c65bc37ee53ecfc6260299248`.

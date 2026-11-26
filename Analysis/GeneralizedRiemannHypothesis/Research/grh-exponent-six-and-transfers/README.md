# The 432 imaginary quadratic fields of class-group exponent six

Open `report.pdf` for the 16-page research note. Section 2 proves that the 432 known fundamental discriminants form the complete exponent-six census and derives the complete list of 1,236 order discriminants. Section 3 treats Toroczkai’s prime-gap graph conjectures and simultaneous extensions. Sections 4 and 5 determine local quintic discriminants and derive a joint prime-splitting criterion. Section 6 identifies the questions that remain open.

## Reproduce the classification

Run these commands from the directory containing this README. The quadratic and graph checkers use the Python standard library. The tested runtime was Python 3.12.14. Leave assertions enabled. The second divisor search uses a C++17 compiler with unsigned 128-bit integers, such as GCC. The two programs implement the search independently.

```sh
python3 checks/zero_test.py
python3 checks/paired_norms.py 4
g++ -O3 -std=c++17 checks/paired_norms.cpp -o /tmp/grh-paired-norms
/tmp/grh-paired-norms 5500 151
python3 checks/check_order_table.py data/orders-six.txt data/exponent-six.csv
python3 checks/verify_order_classes.py data/orders-six.txt checks/earlier_census
python3 checks/earlier_census/check_exponent_six_fields.py > /tmp/grh-fields-six.csv
cmp /tmp/grh-fields-six.csv data/exponent-six.csv
```

The Python divisor search accepts the number of worker processes (one by default). The Python and C++ runs must each report 414 eligible primes, 85,491 pairs, 9,393,302 candidates above the lower bound, and zero survivors. Their intermediate divisor counts differ by 85,491 because the C++ search includes the zero-valued left endpoint once per prime pair. The two log files show the expected output.

The reduced-form census recomputes the 432 fields through absolute discriminant 5,761,140. The exhaustive enumeration up to 3.1 × 10²⁰ is an input from Elsenhans, Klüners and Nicolae. Section 2 proves exhaustiveness above that threshold. The order verification checks the sixth power of each of 103,830 primitive reduced classes. The order table is reproduced byte for byte from the authors’ accompanying data. The checker verifies its Git blob identity.

## Reproduce the other finite checks

```sh
python3 checks/prime_gap_graphs.py
python3 checks/reflection.py
python3 checks/maximal_orders.py
python3 checks/splitting.py
```

The last two commands require SymPy (tested with 1.14.0). The reflection program regenerates `data/reflected_fields.csv` from `data/quadratic_inputs.csv`. Each row specifies the polynomial by the parameters in Section 4. The independent maximal-order calculation checks all 37 reflected quintics and the cyclotomic quintic. The splitting calculation prints JSON for the two families of six fields. The graph calculation prints the example in `data/graph-example.json`. All inputs to these four checks are included.

## Sources and proof boundary

- [Sernau’s Lean development](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207) at commit `72fead102f663d5c7a407964a13dc0cf9d977207`. With a local checkout at that revision, run `python3 checks/source_audit.py /path/to/grh-lean`. This checks the statement files, theorem names, dependency pins and revision. The manuscript uses [Rubinstein’s independent compact-edition kernel replay](https://mrubinst.github.io/grh-lean-compact-check/) for build verification. The deductions in this report are mathematical proofs with executable finite checks. They have not been formalized end to end in Lean.
- [Previous ProveIt reports](https://github.com/VladimirReshetnikov/ProveIt/tree/1e1728ad221d69e48fea09bf754b73422af44943/docs/incoming) at commit `1e1728ad221d69e48fea09bf754b73422af44943`. The reduced-form routines in `checks/earlier_census/` and the small quadratic lists derive from the prior work. Section 1 identifies what each prior report had established.
- [Elsenhans, Klüners and Nicolae](https://arxiv.org/abs/1803.02056), Theorems 1–3 and Tables 1–2. [Carneiro, Milinovich, Quesada-Herrera and Ramos](https://arxiv.org/abs/2404.08380), Lemma 9.
- [Aiken, Ross, Shvydkoy and Xue](https://arxiv.org/abs/2605.26020), Theorem 1.3(5), and the [authors’ Table 6](https://github.com/erick-ross/research-data/blob/119301b8bcae42a891062d4877b77b6dbc8e820f/class-groups-small-exp/Table-6.txt).
- [Erdős, Harcos, Kharel, Maga, Mezei and Toroczkai](https://doi.org/10.1007/s00208-023-02574-1), Theorems 1.6 and 1.8. Further references for graph extensions and the quintic reflection results are linked at the relevant steps in the manuscript.

## Rebuild the manuscript

All TeX sections and typeset tables are included. Use pdfLaTeX in a standard TeX Live or MiKTeX installation with Latin Modern, microtype, AMS math, booktabs, enumitem, geometry, fancyhdr and hyperref.

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

To verify the extracted contents before rebuilding or regenerating any outputs, run `sha256sum -c SHA256SUMS` from this directory.

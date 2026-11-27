# Quadratic characters from finitely many zeros

The complete research note is in **quadratic_spectra.pdf**. Its editable source is **quadratic_spectra.tex**, with **interval_pairing.pdf** as the single illustration.

## Results

- Theorem 2.1 characterizes the least inert prime by the first possible positive pairing between spectral vectors of two separated logarithmic intervals.
- Theorem 3.1 reconstructs the character at all prime powers up to a chosen bound from one finite list of zero ordinates. Corollary 3.2 gives a common height identifying primitive quadratic characters with bounded conductor. Theorem 3.3 bounds below the total displacement of every matching when the two spectra have equal size.
- Theorems 4.1 and 4.3 classify optimal positive dilation averages at one ordinate and evaluate the first-order cost of shortening the support. Theorem 5.1 and its stability discussion extend the result to an entire consecutive block of harmonics with arbitrary real exponents and multiplicities.

## Reproduce the calculations

Run these commands from the extracted folder. Each check exits with an error if its assertions fail. The spectrum checks use numerical arithmetic; the zero-tail and rounding estimates in the paper have analytic proofs.

```sh
python3 check_filters.py
python3 check_spectrum.py --ordinates zeros_mod3.csv
python3 check_decoder.py --spot-check
python3 plot_pairing.py
```

- **check_filters.py** uses the Python standard library and exact rational arithmetic for the grid weights and moment equations. The output is recorded in **filters_example.txt**.
- **check_spectrum.py** uses mpmath to compute the conductor-three interval pairing through height 100. Its 46 positive ordinates are in **zeros_mod3.csv**. Its results are in **spectrum_example.txt**.
- **check_decoder.py** uses NumPy and SciPy for the higher-order test at height 1120. The optional spot check uses mpmath. The program recomputes the zeros and checks the count numerically by a separate argument calculation. The four estimates are recorded in **decoder_example.txt**.
- **plot_pairing.py** uses NumPy, Matplotlib and the supplied CSV to regenerate the vector figure. Building the paper uses the included figure and does not require Python.

A conventional TeX Live installation can build the PDF with two runs of:

```sh
pdflatex -halt-on-error quadratic_spectra.tex
```

The source analysis uses commit `72fead102f663d5c7a407964a13dc0cf9d977207` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207). The report links to the Lean statements, the reduction, independent verification reports, and the mathematical literature. The new results have written proofs. The zero-enumeration examples are numerical diagnostics rather than interval-certified enumerations.

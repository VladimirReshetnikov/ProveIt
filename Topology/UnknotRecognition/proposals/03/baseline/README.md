Unmodified source from the uploaded Knots.zip/fast/fastunknot/.

The benchmark worker selects this package by sys.path. Tests may import it as
baseline.fastunknot. reference_markowitz.py changes only the pivot scheduler
for validation and is NOT the unchanged baseline used for speedup denominators.
See ../results/provenance.json for exact source hashes.

To run the unchanged 19-test suite, change to this baseline/ directory and run
python -m unittest discover -s tests -v. The original example inputs are included.

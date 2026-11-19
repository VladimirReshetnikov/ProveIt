A convex cover for every unit space curve
19 November 2026

space_worm.pdf is the six-page report. Its main inequality is
0.0187328 < V_3 < 0.0542671. The exact minimum is open.

To compile the report, change to this directory and run the two commands
    pdflatex space_worm.tex
    pdflatex space_worm.tex
The vector figure cover_figure.pdf is included, so compilation requires
only a standard LaTeX distribution with Latin Modern and the AMS packages.

To reproduce the rational calculations, run
    python3 check_bounds.py
    python3 check_width.py
These scripts use the Python standard library. The first reconstructs the
planar quadrilateral from four half-planes, computes its shoelace area and
the spatial volume, and checks the rounded bounds. The second verifies
the width of the elementary four-link test curve.

To regenerate cover_figure.pdf, run
    python3 draw_cover.py
This optional step uses NumPy and Matplotlib. It renders the body given
by equation (1), with the mean of the quadrilateral vertices as origin.

The three-dimensional deductions are proved in the text. The cited
planar-cover and width theorems are inputs to those deductions.

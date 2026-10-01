# Optional numerical diagnostics

From the package directory run:

    python3 checks/theta_diagnostics.py

Requires NumPy, SciPy and mpmath. It writes theta_diagnostics.json beside
itself. The saved environment versions are included in that file.

The script performs 20 comparisons between the direct Gaussian sum and its
Fourier/theta representation at 75-digit working precision, 6 comparisons
of the neighboring-cap tilted laws' L1 distance with twice their removed
endpoint mass, and 36 finite squared-envelope recurrence evaluations.
The latter retain the exact numerically computed scalar-cluster parameters.
No assertion of a finite relative-approximation error is made for those rows.
They are diagnostics, not certified enclosures or evidence replacing the
uniform proof. The large-m theorem does not infer its limit from this sample.

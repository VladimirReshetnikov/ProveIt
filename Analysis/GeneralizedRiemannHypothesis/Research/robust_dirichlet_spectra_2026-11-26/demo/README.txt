Numerical illustration: oriented complex Dirichlet spectra
=========================================================

This directory accompanies a mathematical proof. It illustrates the proposed
observation model with three primitive characters of conductor 5. It does not
prove GRH or certify the completeness or multiplicities of a zero list.

Characters and data
-------------------
The quartic character has values chi(0),...,chi(4) = 0,1,i,-i,-1.
Its conjugate has values 0,1,-i,i,-1. Its square is the quadratic
character with values 0,1,-1,-1,1. All three have conductor 5.

The program searches the critical line from -40 to 40. It detects 31 roots
for chi (16 negative, 15 positive), 31 for its conjugate (the reflected list),
and 32 for chi squared (16 of each sign). The asymmetric quartic list shows
why signed ordinates retain information about complex conjugation.

Evaluation and numerical scope
------------------------------
The finite Hurwitz-zeta identity is used to evaluate

  L(s,chi) = 5^(-s) sum_{a=1}^4 chi(a) zeta(s,a/5).

Let a be the parity and epsilon = tau(chi)/(i^a sqrt(5)), where tau is
the Gauss sum. The completed L-function is

  Lambda(s,chi) = (5/pi)^((s+a)/2) Gamma((s+a)/2) L(s,chi).

On s=1/2+it the functional equation makes epsilon^(-1/2) Lambda real.
We divide by the positive modulus of the gamma/conductor factors before
evaluating this Hardy function, so its exponential decay does not damage
conditioning. The square-root branch is fixed by arg(epsilon).

Scanning uses a mesh of 0.125 and 28 decimal digits. Each sign-change
bracket is refined at 60 digits; its zero must remain inside the bracket
and direct |L(1/2+it,chi)| must be below 10^(-40). The largest such residual
is less than 9.62e-60. The saved ordinate strings carry 52 significant
digits. verification_summary.json records their reevaluation at 80 digits.

This procedure can miss an even-multiplicity zero or multiple crossings in
one mesh interval. Neither a sign-change scan nor a small residual proves
zero completeness, simplicity, or GRH. Every occurrence here is a detected
numerical root. No claim is made that height 40 exceeds the explicit theoretical
uniform cutoff in the accompanying report.

Distance and corruption
-----------------------
For finite lists X and Y, the distance is the minimum, over all partial
matchings, of

  (# unmatched entries of X) + (# unmatched entries of Y)
  + sum over matched pairs min(1, abs(x-y)).

The program solves a square assignment problem with dummy vertices.
Two hundred small rational examples compare this solver against an
independent exhaustive dynamic program using exact fractions.

The observed list starts from chi's 31 detected roots. It deletes the entries
with zero-based indices 10 and 20, adds -37.75, 3.125, 38.75, and moves each
remaining original ordinate j by 0.012 sin(1.7j+0.3). It has 32 entries.
The largest jitter is below 0.011902; total absolute jitter is 0.224153.

Candidate                  Clean distance from chi     From damaged list
chi(2)=i                    0.0000000000                 3.2241524043
conjugate chi(2)=-i         22.5615823472                23.7982264315
chi squared(2)=-1          18.7862949068                20.1386606425

The generating character remains the unique nearest candidate, with a
distance gap of 16.9145082382 to the next closest candidate. These numbers
refer only to the detected lists. The direct edit script costs at most
5.2241524043; the optimum is smaller because the metric may pair a deleted
original with a spurious observation at capped cost 1 instead of paying
two separate unmatched penalties.

Files and reproducibility
-------------------------
complex_spectra_demo.py     Root search, exact solver checks, corruption, plot.
verify_saved_data.py        Reevaluate the saved ordinates at 80 digits.
zero_lists.json            High-precision root strings, brackets, diagnostics.
zero_ordinates.csv         Same detected roots in a simple tabular form.
corrupted_observation.csv  Jitter/deletion/insertion provenance.
demo_results.json          Distances, construction budget, solver checks.
verification_summary.json  Verification of rounded saved ordinate strings.
complex_zero_lists.pdf     Vector figure.
complex_zero_lists.png     Raster preview.
requirements.txt           Versions used for this illustration.

Run from this directory:

  python3 complex_spectra_demo.py --height 40 --output .
  python3 verify_saved_data.py

The first run used about 22 seconds in the preparation environment.
To regenerate only the metric calculations and figure from saved roots:

  python3 complex_spectra_demo.py --height 40 --output . --reuse-roots

The script is deterministic. Wall times and final floating-point digits of
assignment costs may vary slightly with the execution environment.

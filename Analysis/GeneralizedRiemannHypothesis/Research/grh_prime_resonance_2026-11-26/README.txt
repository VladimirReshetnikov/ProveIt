PRIME-POWER RESONANCE AND CHARACTER-INDEPENDENT DETERMINANT LAWS
Research package prepared for Vladimir Reshetnikov, 26 November 2026

START HERE

Read grh_prime_resonance.pdf. The editable LaTeX source is main.tex.

MAIN RESULTS

1. For the positive zero-spectrum covariance of each primitive real Dirichlet
   L-function, microscopic increments at fixed distinct basepoints converge
   jointly to independent Brownian motions. The first covariance correction
   is explicit and occurs precisely at logarithms of unramified prime powers.

2. At basepoints log(1),...,log(N), the first correction is a finite matrix
   whose edge at j/i=p^k has weight chi(p)^k log(p)/p^(k/2).

3. The log determinant of the increment correlation matrix has a convergent
   trace expansion, up to an O(h/log(1/h)) remainder. This gives its asymptotic
   expansion to every inverse-logarithmic order.

4. A diagonal sign change removes the real character from that matrix.
   After the conductor shift, all coefficients depend only on the primes
   p <= N dividing the conductor. This is not a converse recovery claim.

5. Additional results give a triangular resonance profile and a two-term
   asymptotic for coalescing Gram determinants.

STATUS

The PDF contains complete human-readable proofs. Its external zero-location
input is the RH/Dirichlet GRH theorem in the pinned grh-lean source, supplemented
by classical explicit-formula, Hadamard-product and functional-equation facts.
The upstream Lean development was inspected, not rebuilt in this session.
The new results have not been formalized in Lean.

The 61 supplied ProveIt packets, including all 408 TeX files, were screened.
The proposed new contribution is the combined microscopic covariance,
prime-power matrix, all-orders determinant and character-universality result.
Derivative jumps and positive spectral kernels have acknowledged antecedents.
Targeted searches and corpus comparison do not certify worldwide priority.

The Gaussian process is constructed from the zero spectrum; no claim is made
that ordinary prime errors are Gaussian. All asymptotics fix the character,
the finite number of points, their distinct locations, and the time window.

CONTENTS

  main.tex                         Complete mathematical source
  grh_prime_resonance.pdf           Compiled report
  code/verify_resonance.py          90-digit zeta checks and exact graph checks
  code/verify_characters.py         Real-character transfer and rescaling checks
  code/make_figures.py              Regenerate the static scientific figure
  code/build.py                     Rebuild calculations, figures, and PDF
  figures/                         PDF/PNG figure
  results/                         Recorded numerical and exact-check outputs
  provenance/source_audit.txt       Source scope, novelty, and verification audit
  provenance/sources.json           Pinned source paths and local-content hashes
  provenance/inspected_tex_inventory.tsv  Git blob IDs of the screened corpus
  formalization-plan.txt           Honest plan, not a completed Lean proof
  requirements.txt                 Python dependencies
  SHA256SUMS                       Archive member digests (excluding this file)

REPRODUCE

Python 3.10+ and mpmath, NumPy, Matplotlib are required. Install dependencies
with your preferred Python environment, for example:

  python3 -m pip install -r requirements.txt

Then run from the extracted directory:

  python3 code/verify_resonance.py
  python3 code/verify_characters.py
  python3 code/make_figures.py

The calculations use no zero table. The main checks use 90-digit mpmath
arithmetic; they are not interval certificates. Exact character-gauge and
trace-polynomial checks use integer signs and rational coefficients.

For a standard TeX installation, either:

  tectonic main.tex --outdir build

or two runs of:

  pdflatex -interaction=nonstopmode -halt-on-error -output-directory build main.tex

Create build/ first. Alternatively, python3 code/build.py runs the full
sequence, preferring a working pdflatex installation. It copies the generated
PDF to grh_prime_resonance.pdf. Rebuilding may change PDF metadata and hashes.

No upstream source tree is redistributed. Source URLs and content hashes are
recorded for reproducibility. All files in this package were created for this
research result, apart from bibliographic metadata and source inventories.

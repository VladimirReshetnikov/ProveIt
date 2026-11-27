# Sharp Euler-factor agreement for prime-exponent Dirichlet packets

Contents:
- `prime_packet.tex`: full LaTeX research note with all new proofs and references.
- `prime_packet.pdf`: compiled 11-page note.
- `verify.py`: independent exact finite-field examples and normalized planar enumeration, including the impossible case p=7, b=5. This is a finite check, not a proof of the general theorem.
- `verification.txt`: output from running the script.
- `sources.md`: repository provenance and scope.

Build: run `pdflatex -halt-on-error prime_packet.tex` twice. Verify examples with `python3 verify.py` (standard library only).

The density bound, equality classification and planar obstruction are unconditional mathematical results using the established minimum-weight theorem and characterization for projective Reed–Muller codes. The effective prime-window statements use Dirichlet GRH as exported by the vendored Lean repository; neither the source proof nor this new note was kernel-checked in this session. The full density spectrum and priority over all published literature remain open verification tasks. No changes were made to the GitHub repository.

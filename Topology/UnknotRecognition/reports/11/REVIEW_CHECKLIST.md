# Review and acceptance gates

## Mathematics

- Check the precise local positive/negative twist conventions against Thompson's
  normal form and the marked reduced Frobenius functor.
- Review the first-use circle lemma independently, especially the untouched
  strand cut and its compatibility with braid closure.
- Check that the exact trace counts **chain dimensions**, not homology, and that
  local indices with equal support still contribute separate degree copies.
- Include bit lengths in all transfer and rank cost accounting.
- Keep expanded crossing length separate from binary exponent encoding.
- Keep the restricted `O(log n)`-run theorem separate from arbitrary diagrams.
- Treat the hierarchy progress theorem as conditional on globally preserved
  constraints, including all reset operations.

## Implementation (completed here)

- [x] Unit suite: 62 tests.
- [x] Independent crossing-cube comparison: 900 cases, degree-wise.
- [x] Both differentials checked for square zero in that comparison.
- [x] Independent exact-size and degree-profile certificates.
- [x] Controlled same-code block-grouping ablation, including A/A controls.
- [x] Invalid/link/UNKNOWN CLI behavior checked in final smoke tests.

## Upstream integration (not completed here)

- [ ] Run `integration/crosscheck_fastunknot.py` against the intended checkout.
- [ ] Run the upstream Python and Rust unit suites.
- [ ] Check paired timings against the current scanner on filter-undecided inputs.
- [ ] Verify an adapter's retained braid provenance across every transformation.
- [ ] Keep production defaults unchanged until all acceptance gates pass.

The mathematical argument is an ordinary written proof. No Lean certification,
independent peer review, or unrestricted quasi-polynomial theorem is claimed.

# Exact computational companion to Report149

This fresh, standard-library-only Python implementation checks the corrected
ascent-first alternating Baxter involution enumeration. It does not import or
reuse the earlier scouting scripts. The corrected factor is the Catalan number
C_j; the old recurrence uses its own odd coefficient o_j instead.

## Run

Python 3.10 or newer on Linux/POSIX is sufficient. No third-party package or
network access is needed. From the release directory:

```sh
python companion/verify.py --check companion/evidence.json
python -m unittest discover -s companion/tests -v
python -O -m unittest discover -s companion/tests -v
```

To create new evidence, choose a file that does not already exist, in an existing
real directory:

```sh
python companion/verify.py --output /tmp/report149-new-evidence.json
python -O companion/verify.py --output /tmp/report149-new-evidence-optimized.json
cmp /tmp/report149-new-evidence.json /tmp/report149-new-evidence-optimized.json
```

The CLI deliberately refuses an existing destination, including a previous
successful run. Choose another filename. It neither creates parent directories
nor follows symlinks in the target or any parent directory. `--check` also refuses
input symlinks, directory inputs, oversized inputs, duplicate JSON keys, and
non-finite JSON values. A failure exits nonzero. The success message is not a
substitute for the evidence file.

`evidence.json` is deterministic: there are no timestamps, elapsed times, machine
paths, random samples, or platform-version strings. Normal and `-O` runs produce
identical bytes. All mathematical checks use explicit exceptions, so optimization
cannot disable them. The suite includes subprocess checks in both modes.

## What is checked

1. **Exact coefficients through half-length m=60.** `exact.py` computes e_m and
   o_m from the two corrected recurrences. A separate implementation expands
   u=sqrt(1-4x^2), M=(1+u)/2, D=M(1-2x-4x^2),
   O=(M-x-sqrt(D))/(2x^2), and E=(1+xO)/M with rational formal series. It never
   consults the enumeration recurrence. The radical branch starts at one, and
   the numerator's first two zero coefficients are checked before division by
   x^2. Both coefficient vectors, integrality, the two functional equations,
   discriminant factorization, and the quartic polynomial relation are checked.

2. **The old recurrence and its first discrepancy.** Old and corrected vectors
   agree for n<20. The first mismatch is a_20=2168 versus 2166. The corrected
   prefix continues 5080, 6014, 14594, 17252 at n=21,22,23,24. The computation
   compares the mathematical old recurrence, not an unrelated rounding-based
   implementation of it.

3. **Two explicit omitted objects of length 20.** `permutations.py` checks
   ascent-first alternation, involutionhood, and both Baxter definitions on each
   object. The literal Min 2021 definition considers every quadruple i<j<k<l:
   ai+1=al and al<aj imply ak>al; al+1=ai and ai<ak imply aj>ai. It does not add
   positional adjacency. The other predicate independently checks adjacent
   central positions in 2-41-3 and 3-14-2. Each accepted object passes all 4845
   quadruples. Their outer blocks are inverse partners; each outer block is
   individually non-involutive. Their length-eight interior blocks are the two
   non-involutive members of RB_8. Classical separability is an additional check,
   never a replacement for either Baxter definition. A unit test includes a
   Baxter permutation that is not classically separable to guard that distinction.

4. **Finite exhaustive checks with explicit dependence boundaries.**
   - Every permutation through n=8 is tested for equality of the two Baxter
     predicates, with factorial totals checked
   - Every involution through n=12 is generated without pruning by alternation,
     Baxter avoidance, or any structural lemma. The generator pairs the least
     unassigned position with itself or one larger unassigned partner. Telephone
     number totals are checked, then ascent-first alternating objects are filtered
     by both predicates and compared with the corrected coefficients
   - Separately, unrestricted even doubly alternating and doubly reverse-alternating
     classes are generated through m=10 from the published Min-Park structural
     lemmas. Uniqueness, Catalan totals, alternation, inverse alternation, and
     involution-filtered counts are checked. Both literal Baxter predicates are
     evaluated on every accepted involution, not every unrestricted object. At
     length 20 this gives 16796 unrestricted B_20 objects and 2168 involutions;
     the reverse class gives the odd coefficient a_21=5080. Both omitted objects
     occur in the unrestricted generated class

   The n<=12 direct check is independent of the structural lemmas. The larger
   grammar check assumes those lemmas and does not independently prove their
   completeness. No finite bound is silently promoted to an all-n theorem.

5. **All four displayed formal inverse coefficients.** A small exact Laurent
   polynomial ring in beta,p,d1,d2,d3,d4 substitutes v1 through v4 into

   0 = beta*u - p*log(1+epsilon*u)
       + sum_(j>=1) d_j*epsilon^j*(1+epsilon*u)^(-j).

   Every coefficient through epsilon^4 is identically zero for symbolic beta
   nonzero and arbitrary p (the application uses p=3/2). Independent sequential
   coefficient cancellation reproduces the displayed formulas. Adding one to
   each v_k separately is detected. This is a formal algebra test; it does not
   estimate or certify finite analytic remainder constants or threshold onsets.

6. **Tampering and filesystem safety.** The evidence checker recomputes the
   expected mathematics and compares the exact canonical structure and values;
   it does not trust an embedded hash or claimed success flag. Tests mutate
   coefficients (including coordinated recurrence/radical changes), a permutation,
   a property flag, an inverse coefficient, the schema, bounds, and JSON types.
   Missing and extra keys are also rejected. Boolean `true` cannot substitute for
   integer 1. `safeio.py` walks existing directories using descriptors and
   O_NOFOLLOW, creates output with O_EXCL, and never overwrites an existing file.
   Descriptor-relative opens prevent a symlink check/use race. Tests cover live
   and dangling target symlinks, parent symlinks, input symlinks, parent traversal,
   and existing-file preservation.

## Files

- `exact.py`: recurrence, rational formal radicals, exact identities, symbolic inverse
- `permutations.py`: literal predicates, direct generator, unrestricted grammar
- `safeio.py`: exclusive descriptor-relative regular-file operations
- `verify.py`: deterministic evidence generation and full semantic recomputation
- `evidence.json`: frozen generated results, coefficients, finite counts and limits
- `tests/test_companion.py`: correctness, mutation, I/O safety and optimization tests

The full evidence run takes several seconds on a typical machine. The test suite
is longer because it deliberately starts additional normal and optimized runs.

## Scope and sources

The written report, not these finite computations, supplies the all-n proof and
analytic transfer argument. These files do not certify finite inverse error
constants, asymptotic onset, universally exact ceiling rounding, novelty, or the
current content of a live OEIS entry. The intended permutation class and the old
recurrence-defined sequence remain distinct throughout.

- Min and Park (2006), Theorem 4.1 and Corollaries 4.5, 4.7:
  https://doi.org/10.4134/JKMS.2006.43.3.553
- Min (2021), literal definition on p.253 and old recurrence comparison:
  https://doi.org/10.14403/jcms.2021.34.3.253

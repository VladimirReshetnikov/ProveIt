# Source provenance and scope

## Mathematical construction

The article supplies a self-contained proof of effective Presburger timed evolution for the stated single-unit-label, positive-weight, one-dimensional, finite-radius model at total mass at most three. The main proof and the executable implementation were reviewed separately. No novelty claim is made.

The proof requires one zero-weight vacuum, not uniqueness of the quiescent symbol. Constant nonzero configurations may also be fixed. Radius zero and absence of a weight-one label are explicitly included. The unit-label hypothesis is essential to the no-split diameter lemma.

## Arithmetic dependency

The quartic corollary uses the canonical quantifier-free Presburger compiler already established in Section 9 of *Sparse Diophantine certificates for finite mass lattice dynamics*, companion research report dated 2 October 2026. This package neither modifies that report nor imports its polynomial-constructor implementation. The verified six-witness congruence bound is retained.

Effective quantifier elimination is attributed to D. C. Cooper, “Theorem Proving in Arithmetic without Multiplication,” Machine Intelligence 7 (1972), 91–99:
https://www.cs.cmu.edu/~emc/spring06/home1_files/Cooper.pdf

Effective equivalence with semilinear sets is attributed to S. Ginsburg and E. H. Spanier, “Semigroups, Presburger formulas, and languages,” Pacific Journal of Mathematics 16 (1966), 285–296:
https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf

## Numerical-particle literature

A. Alhazov and K. Imai, “Particle Complexity of Universal Finite Number-Conserving Cellular Automata,” CANDAR 2016, 209–214:
https://doi.org/10.1109/CANDAR.2016.0045
https://ieeexplore.ieee.org/document/7818615

The publisher abstract was verified. It states nonnegative integer states and finite total sum, and reports a five-particle universal construction at sufficiently large finite radius. It does not claim minimality. The full paper was inaccessible, so its discussion of lower bounds could not be checked.

The Kyoto RIMS 2020-year research report, printed p. 93, records Gil-Tak Kong and Katsunobu Imai, “On particle complexity of number conserving cellular automata,” on 2 February 2021:
https://www.kurims.kyoto-u.ac.jp/kyoten/ja/files/kyodo_report_2020.pdf

The same title appears under academic year 2020 in KAKEN project 17K00015:
https://kaken.nii.ac.jp/grant/KAKENHI-PROJECT-17K00015/

### Direct 2021 precursors verified for this revision

Gil-Tak Kong, *A hierarchical structural interpretation of 1-dimensional 2-state number conserving cellular automata*, Hiroshima University doctoral thesis, June 2021:
https://hiroshima.repo.nii.ac.jp/record/2002360/files/k8621_3.pdf

Definition 1, printed p. 8 (PDF p. 9), fixes the binary model. Theorem 2, printed p. 14 (PDF p. 15), gives three-particle non-strong-universality using whole-orbit or independent-component periodicity. The conclusion on printed p. 15 (PDF p. 16) calls four particles open as of 2021, not necessarily today.

Katsunobu Imai, final report for KAKEN project 17K00015, dated 25 June 2021:
https://kaken.nii.ac.jp/file/KAKENHI-PROJECT-17K00015/17K00015seika.pdf

PDF p. 4, Section 4, item (2), reports a motion-representation proof of decidability with at most three particles. The decision problem is implicit. PDF p. 3 discusses the five-particle result and the numerical-NCCA/pebble distinction. This does not resolve the relationship to our fully specified weighted, uniform timed, or quartic statements.

The primary pages were inspected visually as well as through extracted text. No primary PDF or screenshot is redistributed. These findings require explicit precursor attribution; they do not establish novelty of the stated strengthenings or the current status of mass four.

## Reproducibility boundary

The portable replay exercises actual sample CA rules, finite-state mass-two profiles, signed affine first-entry arithmetic, complete encounter cycles, and intermediate output configurations. The main rule families have independent mathematical conservation arguments; exhaustive finite-window or random dense checks are supplementary. Test success is not a machine-checked universal theorem.

No third-party paper PDFs, screenshots, machine-specific paths, credentials, package-manager environments, or unrelated reports are redistributed.

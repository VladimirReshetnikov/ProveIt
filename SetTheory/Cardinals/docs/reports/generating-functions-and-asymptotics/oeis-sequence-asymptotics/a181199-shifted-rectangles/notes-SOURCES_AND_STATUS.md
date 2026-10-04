# Sources and status audit

Audit date: October 3, 2026. Preparation date refers to the user's local date; PDF file metadata may show the following UTC date.

## Primary OEIS target

**A181199**, https://oeis.org/A181199, defines the five-row array sequence. The inspected entry labels

    a(n) ~ 9 * 5^(5*n + 1/2) / (2^17 * pi^2 * n^12)

as a conjecture of Vaclav Kotesovec dated February 27, 2023, based on Christoph Koutschan's conjectured recurrence. The present article proves that asymptotic from the combinatorial definition without assuming the recurrence. Its five correction coefficients follow from the article's finite exact moment formula.

The conjecture label is a statement about the inspected OEIS entry, not proof that no prior proof exists anywhere.

**A181198**, https://oeis.org/A181198, defines the four-row sequence and displays a conjectured order-two, degree-nine recurrence and a conjectured finite-sum solution. The manuscript proves asymptotic results for this sequence but does not prove either displayed conjecture.

**A181197**, https://oeis.org/A181197, already records the height-three leading asymptotic and a shifted-hook explanation attributed to Greta Panova, in comments contributed by Joel B. Lewis. Its leading term is a control, not a new discovery here.

**A181196**, https://oeis.org/A181196, organizes the two-parameter family. Keeping the number of rows fixed is different from keeping the number of columns fixed.

## Reference integers

https://oeis.org/A181198/b181198.txt

https://oeis.org/A181199/b181199.txt

The entry pages credit Christoph Koutschan's tables, with earlier terms from Alois P. Heinz (through n=27 and n=26, respectively). Selected values were transcribed into `data/oeis_selected.json`; no claim is made that the complete b-files were downloaded or regenerated. Independent row-state enumeration matches the selected values through n=40. Values at n=80 are used only as reference inputs for diagnostics.

## Related research inspected

**Manuel Kauers and Christoph Koutschan**, *Some D-finite and Some Possibly D-finite Sequences in the OEIS*, Journal of Integer Sequences 26 (2023), article 23.4.5. https://arxiv.org/abs/2303.02793

Section 6.4 of the inspected arXiv PDF treats shifted rectangles and the conjectured height-four and height-five recurrences. The relevant pages were inspected as both text and rendered images. The arXiv pagination differs from the page numbers quoted on the OEIS entries. No long conjectured recurrence is copied into this archive because none is needed in the proof.

**Ping Sun**, *Enumeration of standard Young tableaux of shifted strips with constant width*, Electronic Journal of Combinatorics 24(2) (2017), P2.41; preprint https://arxiv.org/abs/1506.07256

Supplies the established shifted-hook product, integral/order-statistics viewpoint, and results in small parameter regimes. The article's Appendix A re-proves the shifted hook product, and the exact threshold identity is established independently. Sun's two parameter orientations must not be confused.

**Brian T. Chan**, *Periodic P-Partitions*, revised preprint https://arxiv.org/abs/1803.05594 (2020), subsequently European Journal of Combinatorics (2023).

Its periodic-strip framework and constant-coefficient recurrence/asymptotic results concern repetition with a fixed number of cells in each row. For the rectangles in this manuscript, that is fixed n and growing m, not the fixed-m asymptotic established here. No claim is made that the present theorem invalidates or supersedes those results.

**Philippe Flajolet and Robert Sedgewick**, *Analytic Combinatorics* (2009), author companion site https://ac.cs.princeton.edu/

Used as background for classical algebraic-function/Puiseux properties. The full book was not fetched during this run; no exact page or sequence-specific result is attributed to it. The nonalgebraicity argument itself is given in full, using coefficient subtraction, Puiseux structure, and the classical transcendence of pi.

**NIST DLMF**: https://dlmf.nist.gov/5.11 (Stirling expansion), https://dlmf.nist.gov/18.19 (orthogonal polynomial background), https://dlmf.nist.gov/4.13 (Lambert W branches). The binomial norms and coefficient conversion are derived explicitly in the manuscript. The inverse method is standard, not claimed as a new invention.

## ProveIt relationship

Repository: https://github.com/VladimirReshetnikov/ProveIt

Revision: `6bf7f30d0352f7596e70928b3d4f304914075907`.

Identifier searches for A181198 and A181199 returned no matching report. This does not exclude unnamed discussion, unindexed files, or archived incoming material. The README of the existing `a189281-path-forest-expansions` report was inspected as an editorial precedent for distinguishing proved all-order expansions, conjectured recurrences, standard inversion machinery, and finite numerical checks. None of its theorems is used as a premise here.

## Proven statements and priority limitations

The article proves an exact threshold identity with an exponential boundary bound; an effective all-order fixed-height asymptotic; universal first and second correction coefficients; the A181199 specialization; a limiting ratio to ordinary rectangular tableaux; an algebraicity dichotomy; and Gaussian intermediate-shape laws. These proofs are the basis of the claims, not the numerical tests.

The reviewed sources did not supply these full statements in the form established here. That review is not an exhaustive priority certificate. In particular, the report does not claim that standard hook formulas, Gaussian Vandermonde integrals, orthogonal-polynomial methods, or Lambert-W inversion are new.

Unresolved here: the specified conjectured recurrences, D-finiteness at arbitrary fixed height, polynomial dependence of every correction on height, uniform growing-height asymptotics, actual exponentially small sectors, process limits, and efficient certified integer-index inversion.

No OEIS submission, GitHub commit, peer review, or proof-assistant verification was performed.

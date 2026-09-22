# Infinitesimal Spectral Thickening and Closed-Range Defects in Hahn–Hilbert Spaces

Research manuscript prepared for Vladimir Reshetnikov, September 22, 2026.

## Files

- `article.pdf`: typeset article, with complete proofs relative to explicitly named classical inputs.
- `article.tex`: self-contained LaTeX source, including the bibliography.
- `code/verify.py`: exact finite symbolic checks, with scope limitations in the source.
- `data/verification.txt`: output of an actual successful run (218 assertions, six groups).
- `build.sh`: compile the article and rerun the checks.
- `requirements.txt`: the SymPy version used for the recorded checks.

## Mathematical setting

The scalar field is K_Gamma = C((t^Gamma)), with Gamma a nonzero set-sized
divisible ordered abelian group. The vector space is H((t^Gamma)), with H an
ordinary complex Hilbert space. Its inner product uses ordinary Hilbert
inner products on coefficients followed by finite Hahn convolution. This is
not an unspecified l2(K), not the algebraic tensor product, and not a claim
about every possible surcomplex Hilbert-space model.

When Gamma is an ordered subgroup of the surreal additive group, t^gamma maps
to omega^(-gamma). In particular, Gamma = Q, t = omega^(-1) realizes the explicit
counterexamples inside a set-sized surcomplex scalar workspace.

## Principal results

1. Every everywhere-defined adjointable operator is automatically a Hahn series
   of bounded ordinary operators, with a single well-ordered support. No prior
   strong-summability assumption is required.
2. For an ordinary bounded normal T, the full algebraic and adjointable-algebra
   spectra agree and equal sigma_C(T) union (sigma_C(T)' + m_Gamma), where the
   prime denotes accumulation points and m_Gamma the infinitesimals. There are
   no new eigenvalues. Isolated points do not thicken.
3. An injective ordinary leading operator S retains its whole algebraic range
   defect after every globally supported positive-order Hahn perturbation E:
   coker(S+E) is noncanonically W((t^Gamma)), where V = Ran(S) direct-sum W.
4. For D e_n = e_n/n, C = D^2 + t^(2 eta) I is bounded, self-adjoint, positive,
   coercive and injective, but not onto. Its cokernel dimension over K_Gamma is
   at least the continuum. In rank one its range is closed and proper with
   zero orthogonal complement, despite completeness of the ambient space.
5. Constant data admit the monomial-shift resolvent of an injective S exactly
   when they lie in every Ran(S^k).
6. The Hahn extension of an ordinary bounded operator has a least field-valued
   norm bound exactly when the ordinary operator attains its Hilbert norm.

## Status and attribution

These are candidate original results in the specified construction, with
proofs in the manuscript. No named published open problem is claimed solved.
The repository audit and literature comparison did not identify the exact
package in the inspected sources, but priority has not been certified.
The proofs have not been independently refereed or verified by a proof
assistant. Standard Hilbert spectral theory, Baire category, the closed graph
theorem, Hahn–Neumann support lemmas and Conway normal forms are imported and
attributed. The general failure of non-Archimedean orthogonal decomposition is
not claimed as new.

The 218 exact checks concern finite identities only. They do not verify the
infinite-dimensional spectrum formula, the Baire argument, arbitrary support
well-ordering, completeness or continuum-dimensional cokernels. The
rectangular splitting test is explicitly a finite analogue, not a finite
injective nonsurjective endomorphism.

## Repository snapshot

VladimirReshetnikov/Surreal, commit:
608dd23c0539fce73723843949ee627641c27b30

Inspected: repository tree, main README, full documentation catalogue, the
opening 250 lines of the spectral article, and the opening 230 lines of the
differential-equations article. This is a targeted coverage audit, not an
inspection or verification of every repository file. No repository files were
modified.

## Rebuilding

A TeX Live installation providing pdflatex and the packages listed in the
source is sufficient. No external figures, bibliography database or bundled
fonts are needed.

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

For the checks, use Python 3.10+ with SymPy. The recorded run used Python 3.13.5
and SymPy 1.14.0.

    python code/verify.py

Alternatively run `bash build.sh`. The checks are exact rather than numerical;
finite symbolic simplification can take a few minutes on a modest machine.

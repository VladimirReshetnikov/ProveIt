# Research scope and provenance

## Requested basis

The supplied `surcomplex_analysis(3).tex` defines Hahn-coherent data as
well-ordered Hahn sums of ordinary holomorphic functions on one common ordinary
domain. Its final research directions explicitly propose multivariable coherent
division and analytic-set/finite-mapping results with globally stated support
control. The new article addresses the isolated complete-intersection part of
that proposal and retains the source's distinction between strong summation and
fine-topological convergence.

## Literature checked

Research was checked on September 21, 2026. Relevant primary-author and publisher
sources were used for the following works (full references and links are in the
article):

1. Alling, *Foundations of Analysis over Surreal Number Fields* (1987): existing
   surreal and surcomplex analytic foundations; publisher description checked.
2. Neumann, *On ordered division rings* (1949), and Poonen, *Maximally complete
   fields* (1993): Hahn support algebra and algebraic closedness. Poonen's
   Corollary 4 was inspected directly.
3. Cluckers–Lipshitz, *Fields with analytic structure* (2011): broad neighboring
   valued-field analytic theory; publication and scope checked. No claim is made
   that the present statements cannot be derived from their general framework
   after additional comparison work.
4. Crainic, *On the perturbation lemma, and deformations* (2004): the standard
   perturbation identities, inspected directly. The article gives its own
   specialized verification with the sign convention `dh + hd = 1 - ip`.
5. Demailly, *Complex Analytic and Differential Geometry* (2012 online version):
   ordinary coherent analytic algebra, finite mappings, and Stein vanishing.
6. Kunz, *Residues and Duality for Projective Algebraic Varieties* (2008), and
   Cattani–Dickenstein, *Introduction to residues and resultants* (2005): ordinary
   local residue and finite-algebra foundations. Publisher/author bibliographic
   records and scope were checked; these books were not read exhaustively.
7. Cattani–Dickenstein–Sturmfels, *Residues and resultants* (1998): neighboring
   multivariate residue literature.
8. Costin–Ehrlich, *Integration on the surreals* (2024): existing substantial
   extension and integration results, distinct from the coefficientwise local
   contour construction developed here.

Search formulations included combinations of “surcomplex”, “Hahn”,
“holomorphic”, “division”, “Koszul”, “multiplicity”, and “residue”. Searches did
not locate the exact combined theorem package of this article. This does not
prove bibliographic uniqueness, and the article explicitly avoids treating a
negative search result as a priority certificate.

## What is established in the article

The proof constructs a support-controlled perturbation of one ordinary global
Koszul contraction; obtains finite free quotients; identifies all algebraic
characters with actual coherent evaluation points; compares primary local
factors with formal germs at the moved points; and proves the residue and
valuation estimates in that setting. These extension steps are written out in
the paper rather than inferred merely from the terminology of existing sources.

## Important nonclaims

No new abstract homological perturbation lemma is claimed. No general fine
contour integral is claimed. The work does not settle positive-dimensional
surcomplex analytic geometry, compatibility of sectorial summation atlases, or
global transcendental extension problems. The finite checks accompanying the
paper do not replace the proofs and are not Lean or other proof-assistant
verification.

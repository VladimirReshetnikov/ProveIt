# Source and attribution ledger

Inspection date: September 29, 2026.
ProveIt snapshot: `1085b506d65e207a05b7e9c861bb1fe88432fe38`.

## Repository sources actually read

### Formal polynomial map

`Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean`

https://github.com/VladimirReshetnikov/ProveIt/blob/1085b506d65e207a05b7e9c861bb1fe88432fe38/Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean

The file defines the original three-coordinate polynomial map and states
its formal Jacobian determinant, collisions, and noninjectivity. The present
article uses this exact map without rescaling. Its determinant and the
inverse identities needed here were rederived algebraically and independently
checked with exact symbolic arithmetic. The Lean file was read, not built.

### Prior arithmetic report: the central source

`SetTheory/Cardinals/docs/reports/jacobian-conjecture/arithmetic-local-global-fibers/article.tex`

https://github.com/VladimirReshetnikov/ProveIt/blob/1085b506d65e207a05b7e9c861bb1fe88432fe38/SetTheory/Cardinals/docs/reports/jacobian-conjecture/arithmetic-local-global-fibers/article.tex

Its accompanying README was also read. The report is an AI-assisted,
unrefereed research document, not a formal proof development.

Directly inspected sections include the scope and attribution discussion,
the complete inverse cubic, sparse images, verification boundaries, and
the full further-research section. The relevant inherited facts are:

- the inverse cubic `c T^3 - 2 T^2 + B T - 2 A`;
- the derivative reconstruction `g'(t)=2/x`;
- the previously constructed integral-root family on `C=2`;
- its root-parameter density `27/(4 pi^2)`;
- the distinction between rational and integral local-global questions.

The exact open targets are:

- Section 12.2: classification beyond the existing split integral-root family;
- Section 12.3: target-height asymptotics on `C=2`;
- Section 12.4: Zariski density in the full three-dimensional target space.

This article resolves the full-dimensional question, gives a complete
classification for the distinct completely split sector, and proves a
sharp counting theorem in that sector for every fixed nonzero integer
slice. It does not claim to settle the rational-plus-quadratic sector.

### Neighboring research inspected to avoid overlap

`Algebra/JacobianConjecture/Research/README.md`

https://github.com/VladimirReshetnikov/ProveIt/blob/1085b506d65e207a05b7e9c861bb1fe88432fe38/Algebra/JacobianConjecture/Research/README.md

`SetTheory/Cardinals/docs/reports/jacobian-conjecture/weighted-keller-rigidity/README.md`

https://github.com/VladimirReshetnikov/ProveIt/blob/1085b506d65e207a05b7e9c861bb1fe88432fe38/SetTheory/Cardinals/docs/reports/jacobian-conjecture/weighted-keller-rigidity/README.md

These discuss stable degree reductions, weighted classifications, and
related results. None is a theorem dependency for the new arithmetic proofs.
The repository README and recursive file tree were also inspected.

## External primary sources

Shuhong Gao, *Counterexamples to the Jacobian conjecture in dimensions
greater than two*, arXiv:2608.00222 (2026).

https://arxiv.org/abs/2608.00222

The retrieved abstract/metadata were used to verify attribution and the
pre-existing geometric context. This was not a full independent review of
the paper. No result from that paper is an unproved hypothesis in the
present arithmetic arguments: the complete inverse needed here is proved
in the article.

NIST Digital Library of Mathematical Functions, Section 5.12, *Beta Function*.

https://dlmf.nist.gov/5.12

Equations 5.12.1 and 5.12.3 supply the standard beta-gamma identity and
Euler integral used to display the counting constant. The article also
gives the constant as a convergent elementary integral.

## Novelty and proof boundary

The inspection identifies a concrete question stated as unresolved in the
pinned repository report and provides a self-contained proof answering it.
The accompanying classification and counting theorem extend the inspected
material. The searches do not amount to an exhaustive priority audit across
all literature or all repository history. The manuscript therefore claims
contributions relative to these sources, not certified worldwide novelty.

A current repository description, a Lean theorem name, an exact computer
calculation, and an English proof manuscript have different trust boundaries.
They are kept separate throughout the article and in `STATUS.md`.

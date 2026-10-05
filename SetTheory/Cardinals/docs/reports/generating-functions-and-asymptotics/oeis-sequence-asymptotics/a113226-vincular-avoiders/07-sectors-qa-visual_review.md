# Final verification record

Verified 2 October 2026.

## Mathematical checks

- Independent global branch, Hankel orientation, radius-independence, convergence, and exact-decomposition review: pass
- Independent complex saddle, all-orders integrated remainder, Gaussian prefactor, parity, and c2 review: pass
- Exact symbolic circle and separate chord parameterizations through c2: pass
- Exact odd-shift exponent and odd Gaussian moments: pass
- High-precision loop-plus-bank regressions for k=0,1,2 at n=512 and4096: pass
- Analytic omitted-bank tail bounds in all numerical tests: below 1e-70

## Clean replay

The source scripts were copied to a fresh temporary directory. Both Python checks were run with -O and passed. The TeX format was generated in a local writable build/cache directory, and the article compiled twice. Both generated JSON check files reproduced the included outputs byte-for-byte. The final PDF was taken from this clean replay.

## Rendering

The final PDF contains 11 Letter-sized pages. All pages were rendered at 100 dpi and individually inspected. Mathematical symbols, theorem statements, formulas, table columns, references, line breaks, and page numbers are legible and unclipped. No overfull boxes or undefined-reference warnings remain. The final clean-replay PDF was rendered again; every PNG matched the inspected corresponding page byte-for-byte.

Page observations:

1. Title, abstract, scope, main formulas: pass
2. Global branch and exact local formula: pass
3. Bank formulas, Hankel definition, endpoint-loop qualification: pass
4. Global decomposition and rectangle proof: pass
5. Exact normalization and angular saddle: pass
6. Bank bound, prefactor, coefficient algorithm: pass
7. All-orders theorem and detailed integrated-remainder proof: pass
8. Second correction, quantified first pair, constants: pass
9. Replay checks, numerical table, bounded source comparison: pass
10. Further questions and dependency appendix: pass
11. References and verified primary links: pass

These checks are mathematical review and reproducibility evidence; they do not imply external peer review, formal verification, or interval certification of the numerical quadrature.

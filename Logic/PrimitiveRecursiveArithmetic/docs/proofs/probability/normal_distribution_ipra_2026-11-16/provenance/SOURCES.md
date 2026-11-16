# Source inventory and trust boundary

Inspected on 16 November 2026.

## Requested formula collections

1. Wikipedia, **Normal distribution**  
   <https://en.wikipedia.org/wiki/Normal_distribution>
2. Eric W. Weisstein, **Normal Distribution**, MathWorld  
   <https://mathworld.wolfram.com/NormalDistribution.html>

The manuscript inventories mathematical formula families from these pages, corrects missing hypotheses where necessary, and does not attempt to prove historical or empirical prose.

## ProveIt baseline

Repository: <https://github.com/VladimirReshetnikov/ProveIt>  
Commit: `8f028dcb4be7a7397d0c11d7c467aa1170cbf2f3`

Inspected interfaces and reusable packets include:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/central_limit_ipra_2026-11-15/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/calculus_ipra/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/taylor_cauchy_ipra/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/zeta_ipra/`

## Reuse boundary

The packet reuses the written finite quantitative contracts of the analysis and CLT packets. It does not upgrade an uncompiled blueprint into a kernel theorem by citation. In particular:

- `PR`, `PTm`, `PRAAx`, `Prf`, `PRA.qfInd`, and `pra_iff_native` are checked repository interfaces.
- The existing central-limit and analysis packets are human mathematical dependencies unless a particular result is already present in `IPRADerivations` as a literal `Prf PRAAx` theorem.
- This packet's own Lean files are uncompiled blueprints.

## External mathematical references

The bibliography also cites standard probability texts for terminology and cross-checking. No external numerical library is trusted for proof-relevant inequalities.

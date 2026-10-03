# Source status and version receipts

Checked 2 October 2026. These receipts distinguish established results from the present proof and record the scope of the literature check. They are not a guarantee of universal novelty or an assertion about unpublished work.

## Enumeration model and sequence identification

- OEIS A213863: https://oeis.org/A213863
- Official OEIS data export: https://github.com/oeis/oeisdata/blob/main/seq/A213/A213863.seq
- Inspected export blob: 273e138f4f18892a46381c70f8d3b0e9e32550e5; entry revision dated 16 May 2026
- The defining triangle and boundary conditions occur in Lin et al. (2026), equations (1) and (2), https://arxiv.org/html/2601.09551v3
- That version is explicitly dated 6 September 2026. Its Theorem1.1 proves 2^(n−k)A[n,k]=(n−k+1)!b[n,k], supplying the previously conjectural identity needed for total counts

## Existing asymptotic scale

- Fuchs, Yu and Zhang, On the Asymptotic Growth of the Number of Tree-Child Networks, European Journal of Combinatorics 93 (2021), 103278; author PDF dated 16 September 2020
- https://web.math.nccu.edu.tw/mfuchs/Number-of-TCNs-final.pdf
- Proposition2 gives TC_(n,n−1)=n!a_(n−1); equation(4), PDF p5, gives the factorial deficit domination. The one-step insertion inequality is Lemma2, PDF p4
- Banderier and Wallner, Young tableaux with periodic walls: counting with the density method, SLC85B (2021), Article47, Theorem4.1, printed/PDF p8, explicitly gives a_n=Θ(n!12^n exp(z(3n)^(1/3))n^(−2/3))
- Publisher page: https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2021/47.html
- Inspected author PDF: https://lipn.univ-paris13.fr/~banderier/Papers/jenga2021.pdf

## Total counts and distributional baseline

- Chang, Fuchs, Liu, Wallner and Yu, Enumerative and Distributional Results for d-combining Tree-Child Networks, Advances in Applied Mathematics 157 (2024), 102704; author PDF dated 25 March 2024
- https://web.math.nccu.edu.tw/mfuchs/d-comb-journal-rev.pdf
- Theorem3.4 connects network counts to the word array; combined with Lin et al. Theorem1.1 this proves the exact A-table identity used here
- Corollary1.11 and Proposition3.21/equation(26) give the leading total/maximal factor sqrt(e) in the binary case
- Theorem1.9 gives the Poisson(1/2) deficit limit; Remark3.23 discusses moment convergence
- Remark1.12 expressly distinguishes the available Θ result from a first-order asymptotic equivalent

## Amplitude status in the dissertation

- Yu-Sheng Chang, An Enumerative and Probabilistic Study of Various Phylogenetic Network Classes
- https://web.math.nccu.edu.tw/mfuchs/Yu-Sheng-Thesis.pdf
- The title page gives compile date 31 December 2025. The author's publication page lists the dissertation under 2026: https://web.math.nccu.edu.tw/mfuchs/
- The missing multiplicative constant is discussed on printed p100 (PDF page101). Remark35 on printed p137 (PDF page138) repeats the first-order-asymptotic limitation
- The inspected PDF bytes and their SHA256 are recorded in source-status.json. The PDF was successfully retrieved during screening; a later web-index opening failed, so this receipt rests on the inspected local copy rather than a claim about uninterrupted URL availability

## Later primary sources checked for scope

The following 2026 items were inspected during screening. They concern exact enumeration, fixed reticulation numbers, or sparse growing-reticulation regimes; no maximal-reticulation amplitude proof was located in them:

- https://arxiv.org/html/2601.09551v3 (latest inspected version September6)
- https://arxiv.org/abs/2605.07587 (bounded-parameter formulas and limit laws)
- https://arxiv.org/html/2609.04979v1 (a combinatorial proof of the recurrence)
- https://arxiv.org/abs/2605.23126 and https://arxiv.org/abs/2608.20860 (growing sparse-reticulation regimes)
- https://arxiv.org/html/2606.24325v2 (fixed-reticulation asymptotic comparisons)

Fixed-k or k=o(sqrt(n)) results do not cover the maximal regime k=n−1. These scoped observations support the stated research gap but do not certify that every relevant unpublished manuscript has been excluded.

## Mathematical claim boundaries

The report's positive amplitude definition is exact. Numerical amplitude diagnostics are floating-point finite-index values, never certified digits. Every finite algebraic order is proved; convergence of the infinite series and beyond-all-orders terms are not claimed. The inverse result supplies smooth-model asymptotics and eventual integer brackets, not a universally exact ceiling prescription. No external publication, repository change, or submission was made.

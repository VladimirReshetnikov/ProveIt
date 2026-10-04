# Scoped BCH import and computational-interface review

The imported BCH material supplies exact finite word-coefficient algorithms, not an unbounded computation encoding or a paid universal Diophantine compiler. The selected formal coefficient argument is sound. One analytic-domain shorthand needed correction: convergence of the exponential and logarithm at their separate arguments does not make them inverse globally. The combined article now states explicit sufficient local hypotheses and retains the false global reading with its counterexample in a numbered remark.

## Immutable scope and the corrected assertion

The review concerns import `abb123637` and adaptation `ad52ef11e`. Its receipt records eight exact read spans at the adaptation commit, totaling752 lines: the project guide, full combined scope/formal/computation sections, the universal-enveloping interface, the Mercator proposition, the small-logarithm proposition and the final formalization-limit paragraph. All six adaptation text diffs were read and hashed. The import statistic of129 paths is intake only, not a full audit of those files. Lean source/builds, the three original papers, general Hopf/PBW proofs, analytic convergence and applications, external attribution and historical verifier logs remain outside certification.

The old `02_formal.tex` paragraph said that the analytic statements corresponding to the formal exp/log inverse lemma hold "on those domains", just after specifying exponential convergence for every A and Mercator convergence for norm(U)<1. The global inverse reading is false even when both series converge: in the scalar complex algebra, A=2πi has exp(A)=1 and U=0, but log(exp(A))=0≠A. Absolute convergence at the composed argument does not justify the unrestricted nested-series rearrangement.

The replacement makes the two domains explicit:

* exp(log(1+U))=1+U for norm(U)<1;
* log(exp(A))=A under the sufficient hypothesis norm(A)<log2;
* for commuting A,B with norm(A)+norm(B)<log2, the product law follows by applying the local inverse to A, B and A+B;
* applying it separately to A and −A gives the local inverse-log law.

These are the report's own later Mercator and small-logarithm propositions. Their selected proofs were read: the derivatives are uniformly dominated on a disk strictly larger than the unit disk, and the differentiated expressions are constant as required. No broader analytic theorem is inferred from this review. The formal degree-completion lemma has no such analytic branch issue.

The original wording and a concrete proof of failure of its global reading remain in `rem:analytic-inverse-domain`, following the repository's retention rule. All16 existing labels in the edited file are retained and exactly that new label is added. Independent reviewers Aristotle and Tesla were asked to challenge this boundary; their individual scopes are recorded separately, rather than represented as a complete article audit.

## Finite coefficients and a useful integer scale

For a word w of length n, the coefficient of w in U^k, where U=exp(X)exp(Y)−1, is the sum over its contiguous cuts into k nonempty pieces. Every piece must have the shape X^rY^s and contributes 1/(r!s!). Since k<=n, this is a finite rational computation; there are2^(n−1) possible cuts. The full Section2 proof correctly obtains the formula from concatenation and the positive-degree filtration. Characteristic zero is retained.

A direct useful consequence is that

`D_n = n! * lcm(1,...,n)`

clears the denominator of every associative degree-n coefficient. Indeed each cut term has denominator k times a product of factorials of nonnegative run lengths summing to n. That factorial product divides n! by the integer multinomial coefficient, and k divides the displayed least common multiple. Each cut term, and hence their signed sum, has integral product with D_n. This proof does not assume an optimal denominator and gives no unit-cost factorial/lcm operation in the target circuit model.

For a supplied finite cutoff N and finitely represented rational input polynomials or rational matrices, the truncated BCH expression and its equality to another finite rational object are decidable by exact finite arithmetic. Thus a total computable reduction of arbitrary halting to this **fully supplied finite evaluation/equality predicate** would decide halting, an impossibility. This does not preclude an existential unbounded history parameter or integer unknowns inside polynomial equations; those are different predicates and still need a sound, complete, costed representation. The source's universal substitution property is algebraic universality and does not itself give such a computational representation. The source explicitly separates finite verifications, all-order proofs and analytic convergence.

## Fresh independent finite evidence

The new checker does not execute or import any supplied verifier. It extracts each word coefficient using a separate finite matrix representation. For w=a1...an take two strictly upper-triangular (n+1)-square matrices: the (i,i+1) entry of X or Y is1 exactly when ai has that letter. A product corresponding to a length-n word has (0,n) entry1 exactly for w and0 for every other word; products of other lengths have zero there. Therefore the (0,n) entry of the finite nilpotent matrix logarithm of exp(X)exp(Y) is exactly the desired coefficient. Unlike a fixed small matrix sample, this word-dependent path construction isolates every tested word.

Using exact rational matrix products, the checker independently reconstructs all126 words of lengths1 through6, including coefficients missing from the sparse table (which must be zero). All agree with `bch_associative.csv`. All5,190 supplied nonzero rows through degree12 also have valid reduced rational schema and denominators dividing D_n. This latter check is not a recomputation of their degree7–12 numerators and does not certify Lie-basis tables, Zassenhaus tables, or all-order identities.

Fresh normal and optimized exact receipt checks both passed from `/` before freezing. Helper SHA256: `396513caa931ea35297e3d2f8bc7c33cc4480ff201aa29105411b07447ae372b`. Receipt SHA256: `b44a6287e6ab3a69e3611c173c251fa3e6e05a0e1d9888a21ff19f5bb4fdf3b6`. The current corrected TeX source is pinned in the receipt. A direct installed `pdflatex -no-shell-escape` build succeeded in three passes; the final log has no warnings or undefined references, and the rebuilt79-page PDF is saved alongside the source. No old builder or supplied scientific helper ran. An initial build attempt only failed because the new output directory did not yet exist; creating it resolved that setup error.

No source circuit, witness count, arithmetic ledger or established universal bound changes. The report offers exact coefficient machinery for future constructions; an unbounded accepting-history interface and its paid integer compiler remain absent from the reviewed material.

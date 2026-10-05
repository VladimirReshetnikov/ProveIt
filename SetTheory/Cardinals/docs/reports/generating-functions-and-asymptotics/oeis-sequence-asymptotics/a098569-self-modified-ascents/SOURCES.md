# Sources and attribution for Report242

Checked 5 October 2026. This is a bounded literature and model review, not a
certificate of worldwide novelty. The package distributes only original
article/code material and finite source-linked numeric fixtures, not copies
of third-party papers or private review material.

## Model and current indexing

The object is a nonnegative upper-triangular integer table with positive
diagonal, counted by total entry sum N. Dimension is m. Subtracting mandatory
diagonal ones gives binomial(M+N-m-1,N-m), M=m(m+1)/2. Binary tables have
unit diagonal and binomial(m(m-1)/2,N-m) choices.

- [A098569](https://oeis.org/A098569): current official data record revision
  140, 30 May 2026, includes the 29 October 2023 offset change. Matrix size N
  is current OEIS index N-1. All 26 displayed terms were checked
- [A121690](https://oeis.org/A121690): official data record revision 29,
  5 November 2025. Matrix size N is current OEIS index N-1. All 25 displayed
  terms were checked. A cached internal webpage returned revision 28;
  the official data record supplies the later revision
- [A098568](https://oeis.org/A098568): current official record revision 64,
  offset zero. Its formula gives exactly A098568(n,k)=T(n+1,k+1). The
  dimension is k+1, and the row sum is b_(n+1)

The empty object is separately counted by b_0=c_0=1. The older ordinary
formal generating functions and word lengths must not silently be identified
with the current zero-based sequence indices. A098568 explicitly asks about
the distribution of row terms; the article's full-span local Gaussian law
addresses that question with these shifts.

Vaclav Kotesovec's finer logarithmic expressions in the OEIS records are
prior postings. A121690's posting is dated 1 July 2025. The inspected record
does not provide a cited proof or a relative count error for it. A displayed
asymptotic equivalence for a logarithm does not by itself establish every
term of that displayed expression with additive error o(N). The article
credits these expressions without attributing a stronger historical theorem
than the inspected source supports.

## Historical exact enumeration

B. I. Bayoumi, M. H. El-Zahar and S. M. Khamis, *Asymptotic enumeration of
N-free partial orders*, Order 6 (1989), 219-225.
[DOI](https://doi.org/10.1007/BF00563522)

The author-uploaded full text was inspected. Page 222, Lemmas 2-3, gives
uniqueness/rigidity and the interval characterization by positive
superdiagonal. Page 223, Lemma 4, gives the binary finite sum using a block
matrix with one more row than the present table. The same page gives the
multiplicity substitution I(x)=J(x/(1-x)). Table I, page 224, contains the
ordinary prefix 1,2,5,14,43,143,510,1936,7775.

Theorems 5-6 are logarithmic-scale estimates for the larger class of all
covering-graph N-free posets, with the interval subclass used as a lower
bound. They do not provide a relative equivalent or dimension limit theorem
for the selected interval subclass. The correct article page range is
219-225; the later 2004 bibliography's 219-232 is erroneous.

S. M. Khamis, *Height counting of unlabeled interval and N-free posets*,
Discrete Mathematics 275 (2004), 165-175.
[DOI](https://doi.org/10.1016/S0012-365X(03)00106-7)
[Institutional record](https://research.asu.edu.eg/handle/123456789/1124)

Page 166 defines N-freeness in the directed covering graph. Pages 167 and
170 identify the unique strictly upper-triangular block matrix with positive
superdiagonal. Deleting its forced zero first column and last row yields the
present positive-diagonal table; height m is table dimension m, while the
original block matrix has m+1 rows. Lemma 4.1, page 171, gives the
height-refined binary binomial formula. Theorem 4.2 gives the multiplicity
substitution. Table 2, page 173, gives nonrigid refined counts through size 14.

These historical results already supply the binary/rigid subclass and the
exact formulas. Neither exact enumeration nor rigidity is presented as a
new theorem in Report242.

## Word and matrix bridges

M. Bousquet-Melou, A. Claesson, M. Dukes and S. Kitaev, *(2+2)-free posets,
ascent sequences and pattern avoiding permutations*, JCTA 117 (2010),
884-909. [Preprint](https://arxiv.org/abs/0806.0666)

Section 4.4, Propositions 10-11, preprint pages 15-17, supplies the
self-modified factorization, exact generating function, dimension-refined
sum and barred-pattern correspondence. Maximum and ordinary ascent count
are both m-1. Its Section 6 cites Zagier for unrestricted Fishburn numbers,
which does not furnish the present subclass's asymptotics.

M. Dukes and P. R. W. McNamara, *Refining the bijections among ascent sequences,
(2+2)-free posets, integer matrices and pattern-avoiding permutations*,
JCTA 167 (2019), 403-430. [Preprint](https://arxiv.org/abs/1807.11505)

Definition 3.3, Lemma 3.4, Propositions 3.6-3.7 and Corollary 3.8, preprint
pages 11-13, give the positive-diagonal class and its chain meeting all
strict-downset levels. Lemma 3.4 provides the explicit word/matrix map.
The article re-explains that prior map for self-containment.

Terminology guard: the historical N-freeness above concerns the directed
COVERING GRAPH. The 2019 induced-subposet N-free class is the smaller
series-parallel/Catalan class related to 101-avoidance and SE-free matrices
(Proposition 5.4 and Definitions 5.5-5.6). These two conventions must not be
conflated. Report242 uses table/word language for its main claims.

## Difference ascent specialization

G. Cerbai, A. Claesson and B. E. Sagan, *Self-modified difference ascent
sequences*, Advances in Applied Mathematics 170 (2025), 102929.
[DOI](https://doi.org/10.1016/j.aam.2025.102929)
[Published PDF](https://users.math.msu.edu/users/bsagan/Papers/Old/smd-pub.pdf)

The final published paper was inspected as complete web-extracted text.
Lemma 4.3, page 17, describes the decreasing-pace blocks; Theorem 4.4, page 18,
gives the generating function. Page 19 gives d=0 and d=1 and the unshifted
size-N table. For d=1 the strict blocks force diagonal multiplicity one and
at most one occurrence of each lower letter, exactly the binary subclass.
The terminal sections concern patterns; no asymptotic theorem for these
specializations was located in the inspected paper. Its stabilized d-to-
infinity sequence is a different model and is not part of this article.

## Other inspected antecedents and methodological context

- N. Kube and F. Ruskey, *Sequences That Satisfy a(n-a(n))=0*, JIS 8 (2005),
  Article 05.5.5. [Article](https://cs.uwaterloo.ca/journals/JIS/VOL8/Ruskey/ruskey99.html)
  Theorem 1.3, pages 3-4, gives the same table through another sequence and
  set-partition model; no asymptotic section
- C. Bean, A. Claesson and H. Ulfarsson, *Enumerations of Permutations
  Simultaneously Avoiding a Vincular and a Covincular Pattern of Length 3*,
  JIS 20 (2017), Article 17.7.6.
  [Article](https://cs.uwaterloo.ca/journals/JIS/VOL20/Bean/bean2.html)
  Section 5 Proposition 13 and Section 6 Proposition 14 give the binary and
  ordinary permutation enumerations. Permutation indexing is not silently
  transferred to the current shifted matrix size
- W. Y. C. Chen, N. J. Y. Fan and A. F. Y. Zhao, *Partitions and Partial
  Matchings Avoiding Neighbor Patterns*, 2010.
  [Preprint](https://arxiv.org/abs/1009.4535)
  Theorems 1.3-1.4 and Section 4 give the triangular generating function and
  cite self-modified ascents; no relevant asymptotic theorem was located
- H.-K. Hwang and E. Y. Jin, *Asymptotics and statistics on Fishburn matrices
  and their generalizations*, JCTA 180 (2021), 105413.
  [Preprint](https://arxiv.org/abs/1911.06690)
  Theorem 18 concerns a different sum/product family, with different dimension
  scaling. It is methodological context, not an automatic application to the
  present positive-diagonal geometric-cell generating function
- [DLMF 5.11](https://dlmf.nist.gov/5.11) and
  [DLMF 5.15](https://dlmf.nist.gov/5.15) supply the standard gamma,
  digamma and polygamma estimates. The manuscript derives the needed
  uniformity, mixed-size derivatives and Gaussian lattice transfer explicitly

## What was and was not inspected

The historical 1989 author-uploaded full text, the 2004 institutional full
text and the final 2025 published paper were available as complete
web-extracted text. Direct downloads of those versions did not yield local
PDFs, and page screenshots were unavailable. Therefore their complete text
was inspected, but local PDF page images were not. An expired-certificate
failure and site challenges were not bypassed. Available local preprints and
other downloaded papers were distinguished from these published-text reads.

Searches covered exact sequence IDs, model descriptions, binary/rigid
variants, positive superdiagonal, and actual source bibliographies. A bounded
current-main repository comparison read 1,024 TeX sources across the inspected
categories, and a separate seven-file comparison checked nearby existing
articles. No exact duplicate of the selected relative all-orders, dimension,
rare-event and inverse package was located in those checks. The scan did not
cover every file format, archive, PDF, branch, revision history, inaccessible
generated subtree, unpublished work or unnamed equivalent formulation.
Search silence is not a proof of absence. These checks are not external peer
review and do not establish worldwide priority.

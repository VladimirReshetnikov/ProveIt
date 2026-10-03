# A Lorentzian polynomial for oriented supports of a bipartite physical graph

Research note, October 1, 2026. This extends the earlier exterior-only construction to physical core vertices used in either role. It does not resolve arbitrary internal-core 2+3 covers. No priority claim or proof-assistant formalization is made.

## Theorem

Let D be a finite loopless directed relation, and let V=C disjoint-union I be a bipartition of its underlying undirected graph. Thus every directed arc crosses between C and I; an underlying edge may have either or both directions. Assign independent nonnegative activities u_v and v_v for using physical vertex v as a tail or a head.

A feasible support is an ordered pair (S,T) of disjoint, equally sized vertex sets admitting a directed perfect matching from S to T. Each support is counted once, regardless of its number of witnessing matchings.

Define

    F_C(z_C,x_I)
      = sum_(S,T feasible) u^S v^T
          product_(c in C \ (S union T)) z_c
          product_(i in I intersect (S union T)) x_i.

Then F_C is a nonzero, multiaffine Lorentzian polynomial, homogeneous of degree |C|.

Consequently, if Gamma_D(t)=sum gamma_k t^k, then

    H_C(s,t)=sum_k gamma_k s^(|C|-k) t^k

is Lorentzian. The sequence gamma_k / binom(|C|,k) is log-concave. Interchanging the two physical parts gives the analogous statement at order |I|, and hence at order min(|C|,|I|).

The conclusion is actual-degree rank-ULC whenever the positive-weight relation has a matching saturating the smaller physical part. If its surviving degree is smaller than both part sizes, this theorem alone does not give actual-degree normalization. In particular, dividing out a power of s is not asserted to preserve Lorentzianity.

For disconnected physical graphs, reverse each connected component's bipartition independently and put its smaller shore in C; place isolated vertices in I. This gives order equal to the sum, over nontrivial connected components, of the smaller shore size. It gives actual-degree normalization if the positive-weight relation saturates each chosen smaller shore.

## Proof

### Two transversal matroids

For every c in C, temporarily distinguish its tail role c+ from its head role c−. Construct a rank-|C| transversal matroid M+ with matching positions C+ and ground set consisting of one exterior head copy i− for every i in I together with a private dummy a_c for every c in C. The neighbors of i− are exactly those positions c+ for which c→i is an arc. The dummy a_c is adjacent only to c+. The private dummies form a basis, so the rank is exactly |C|, including when some exterior elements are loops.

For U subset C and R subset I, the set of exterior copies R together with the dummies indexed by C\U is a basis exactly when |R|=|U| and a directed matching from U to R exists. Each basis is counted once, so this records the corresponding endpoint support once and does not count matching witnesses.

Similarly construct M− with positions C−, exterior tail copies i+, and private dummies b_c, using arcs i→c. A basis specifies L subset I, W subset C, with a matching from L to W, and the unused-head-role dummies C\W.

Let B+ and B− be their squarefree basis-generating polynomials. They are Lorentzian by the matroid-basis theorem [BH, Theorem 3.10].

### Activities and exterior disjointness

First suppose all role activities are positive. In B+, replace its dummy a_c by a_c/u_c, replace exterior variable x_i by v_i x_i, and multiply the polynomial by product_(c in C) u_c. The resulting coefficient for a basis (U,R) is exactly u^U v^R. Perform the analogous substitutions b_c→b_c/v_c and y_i→u_i y_i in B−, with prefactor product_(c in C) v_c. These operations preserve Lorentzianity.

Multiply these weighted basis polynomials and identify x_i=y_i for every i in I. Take the multiaffine part in the resulting physical exterior variables. A term has x_i squared exactly when i has been selected both as a tail and as a head. Removing these terms therefore enforces exterior physical disjointness, and leaves all other coefficients unchanged.

Products, nonnegative linear substitutions, and multiaffine-part extraction preserve Lorentzianity [BH, Corollary 2.32, Theorem 2.10, Corollary 3.5]. At this stage the polynomial is homogeneous of degree 2|C| and is affine in each private dummy variable.

### Merging the two core roles

For each c apply the coefficientwise operator

    a_c b_c -> z_c,
    a_c     -> 1,
    b_c     -> 1,
    1       -> 0.

The term a_c b_c represents a physical core vertex unused in both roles, and becomes its one unused-vertex variable. Exactly one unused dummy means exactly one used role; its dummy is removed. Neither dummy means both roles are used, so the term is prohibited. Thus this operator enforces exactly the physical disjointness at c.

This is exactly the Lorentzian-preserving merge of [BH, Lemma 3.3], with its surviving variable renamed z_c. The lemma applies because all variables are multiaffine after exterior extraction. For completeness, the symbol verification is as follows. This is a homogeneous linear operator of degree −1: every surviving monomial loses exactly one degree. It preserves coefficient nonnegativity. On the space of polynomials affine in a_c and b_c, its algebraic symbol is

    T[(a_c+r)(b_c+s)] = z_c+r+s.

This is real stable with nonnegative coefficients. The full symbol, if untouched variables are included, is this factor times the factors (w_j+v_j)^(kappa_j). It is therefore homogeneous and Lorentzian. The Lorentzian symbol theorem [BH, Theorem 3.2] applies directly. Equivalently, the stable-symbol theorem and [BH, Theorem 3.4] show that this homogeneous, coefficient-positive stability preserver also preserves Lorentzian polynomials.

Apply this merge at every c in C. Each merge lowers homogeneous degree by one; the final degree is therefore |C|. The all-dummy term survives as product_(c in C) z_c, with coefficient one, so the result is not zero.

### Identifying the resulting supports

A surviving pair of bases gives outgoing data U subset C, R subset I and incoming data L subset I, W subset C, with U intersect W empty and R intersect L empty. It determines exactly the ordered support

    S = U union L,       T = R union W.

Conversely, any feasible directed support of D uniquely determines these four sets by intersection with the bipartition. Its witnessing matching splits into the C→I arcs and the I→C arcs. These give the two bases, independently of the choice of witnessing matching. Therefore the surviving pair is unique for that support. Different role choices can produce the same physical-variable monomial, and their weights correctly add because they are different ordered supports.

The support monomial has x-degree k and z-degree |C|−k: a matching of size k uses exactly k vertices in each physical part. This proves both the displayed formula for F_C and its homogeneity.

For arbitrary nonnegative activities, approach the given activities by strictly positive ones. The coefficients converge to the required weighted support coefficients; the Lorentzian cone is closed, and the coefficient-one all-unused term prevents a zero limit. Finally use the nonnegative substitution z_c=s, x_i=t and the binary Lorentzian characterization [BH, Example 2.26].

## Overlapping role-cover consequence

Suppose the bipartite role graph has a cover P+ union Q−, where the physical sets P and Q may overlap, and suppose the physical core C=P union Q is independent in the underlying graph. The role-cover condition forbids any exterior-to-exterior arc; core independence forbids any core-to-core arc. Thus C and V\C form the physical bipartition required above.

The theorem gives order |P union Q| rather than order |P|+|Q|. A positive-weight matching saturating C gives actual-degree rank-ULC with independent activities. For a 2+3 role cover this means order 5, 4, or 3 according as the selected physical sets have intersection size 0, 1, or 2. It does not treat internal physical core arcs.

Equivalently, one can begin with only the |P|+|Q| necessary role dummies. Merging each of the |P intersect Q| duplicated core vertices lowers the degree by one, giving exactly |P union Q|.

## Primary source

[BH] Petter Brändén and June Huh, *Lorentzian polynomials*, Annals of Mathematics 192 (2020), 821–891, DOI 10.4007/annals.2020.192.3.4.

- Journal page: https://annals.math.princeton.edu/2020/192-3/p04
- Author revision, arXiv v8, July 17, 2024: https://arxiv.org/pdf/1902.03719
- Checked numbering: Theorem 2.10 (nonnegative linear substitutions); Example 2.26 (binary coefficient characterization); Corollary 2.32 (products); Theorem 3.2 (Lorentzian algebraic symbols); Lemma 3.3 (the precise multiaffine merge used here); Theorem 3.4 (homogeneous positive stability preservers); Corollary 3.5 (multiaffine part); Theorem 3.10 (matroid-basis polynomials). Lemma 3.3 is on printed page 851 of the journal version.

The proof uses only the Lorentzian symbol theorem for the merge, not an unverified assertion that every rank-three transversal matroid is stable. Such an assertion is false.

# PD0L phase batching: an 11-operation transport and an alignment obstruction

Batching one complete phase cycle removes the single phase multiplication
from the sequential FIFO PD0L component. The resulting content and length
transports cost **11=5M+6A**. Selecting their row coefficients is still a
joint, weighted lookup problem: the direct batch table has |Sigma|^p entries,
and factoring that table introduces offsets depending on earlier selected
image lengths. This is not a complete certificate below the ternary 90.

There is also a structural obstruction to one tempting simplification.
If the image of every p-letter block has length divisible by p, letter
occurrence in any prolongable PD0L limit is decidable. This holds for
variable-length images, including erasing images. The corresponding
ordinary block substitution must start from the whole aligned prefix
containing the seed; its first block alone need not generate the limit.

The checker is `../verification/explore_pd0l_phase_batching.py`, with an
adjacent JSON receipt. This note complements the sequential evaluator in
`EXPLORATION_FIFO_PD0L.md` and the separate locally uniform analysis in
`EXPLORATION_LOCALLY_UNIFORM_PD0L.md`. PD0L notation is that of
[Endrullis--Hendriks, Definition 1.1](https://arxiv.org/pdf/1207.2336).
The batching and general alignment arguments below are proved here; they
are not attributed to that paper's universality theorem.

## 1. Exact batches of the non-erasing FIFO evaluator

Let h_0,...,h_(p-1) be fixed non-erasing morphisms over a finite alphabet
Sigma, with p>=1. The FIFO evaluator deletes its front letter a and appends
h_phi(a), then increments its phase phi modulo p. The sequential note
proves that, for a productive prolongable seed s with H(s)=s t, the queue
initialized to t enumerates the letters of H^omega(s) after s.

Suppose the current queue has at least p letters, and write it as x w with
x=a_0...a_(p-1). During the next p reads, the evaluator consumes exactly x:
the appended letters are placed after all of x and w. Consequently the batch
is exactly

    x w -> w F_phi(x),
    F_phi(x)=h_phi(a_0) h_(phi+1)(a_1) ... h_(phi+p-1)(a_(p-1)),       (1)

where subscripts are modulo p. The phase returns to phi. Non-erasure gives
|F_phi(x)|>=p, so the queue length never decreases. Once a batch is possible,
every subsequent batch is possible. Rotate the fixed tuple so that this
batch phase is zero; no phase variable is then needed in a batch history.

For a shorter nonempty queue, simulate until its length reaches p or the
exact pair (phase,queue) repeats. While its length is below p there are at
most p sum_(ell=1)^(p-1) |Sigma|^ell such pairs. Thus this preprocessing always
terminates. In the repeated case, all future consumed letters are determined
by the already observed prefix and cycle, so target occurrence is decidable
there. This is effective finite preprocessing, not a free arithmetic loader
for a variable raw numerical input.

A target already in s or consumed during preprocessing is a separate
positive case. Otherwise occurrence is equivalent to a finite positive
number of batches in which some source block x contains the target.
Completing the final batch is legitimate because the queue never empties.
This equivalence does not impose a target condition on the terminal queue.

## 2. Scalar and packed transport, with every endpoint product paid

Give letters distinct digits in {1,...,b-1}, and encode the queue front at
the least significant end. Write n for its code and L=b^(queue length).
For the selected source block x, put

    B=b^p,  d_x=code(x),  u_x=code(F_0(x)),
    k_x=|F_0(x)|,  lambda_x=b^(k_x-p).

B and all three table entries are fixed numerals. Equation (1) gives

    B n_next = n-d_x+u_x L,
    L_next = lambda_x L.                                            (2)

Conversely, assume a valid initial queue of length at least p and a selected
entry x in Sigma^p on every row. Reducing the first equation modulo B forces
d_x to equal the actual p-digit front block: both lie in [0,B), and L is
divisible by B. The quotient is exactly deletion of that block and appending
F_0(x). The second equation gives its actual new length power. Induction
therefore recovers precisely the batched FIFO run. The hypothesis that each
row selects one joint table entry, including its weights, is essential.

Conditionally supply common geometry Q=R^h, h>=1, and five words

    N=sum n_i R^i,           A=sum d_(x_i) R^i,
    U=sum u_(x_i) L_i R^i,   Z=sum L_i R^i,
    W=sum lambda_(x_i) L_i R^i,                         0<=i<h.

Let n0,L0 and nh,Lh be the initial and terminal queue codes and length powers.
Summing (2) gives

    R(N-A+U)=B(N-n0+nh Q),
    RW=Z-L0+Lh Q.                                                   (3)

| Transport | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Content | 3 | 4 | 7 |
| Length | 2 | 2 | 4 |
| Total | 5 | 6 | 11 |

The schedule charges multiplication by B, both terminal products, and both
row shifts. Numerals and comparisons are free. The checker compares all
11 primitives with the two independently written source polynomials.

A complete source must derive common row supports and sufficiently strong
pre-decoding bounds. For example, if every scalar residual in the expanded
equations has absolute value less than R, a vanishing sum of residuals times
R^i has every residual zero, by reduction modulo R and induction. Merely
writing (3) does not establish those bounds. Genuine finite histories can
choose R sufficiently large, which supplies component completeness but not
the missing soundness bounds for arbitrary positive solutions.

## 3. What is still paid after removing the phase

The sequential component costs 12=6M+6A. Batching saves its one phase
multiplication, at the price of changing the selection problem. A direct
batch table has one rule for each of the |Sigma|^p input blocks, rather than
the p|Sigma| phase/letter rules of the sequential formulation.

For a direct specification, introduce Boolean row selectors D_x and their
length-weighted counterparts T_x:

    D_x=sum [x_i=x] R^i,       T_x=sum [x_i=x] L_i R^i.

They must refer to the same selections and partition the common rows. With
J=sum_(i<h) R^i, the required forms include

    sum_x D_x=J,     A=sum_x d_x D_x,
    Z=sum_x T_x,     U=sum_x u_x T_x,     W=sum_x lambda_x T_x.       (4)

Target occurrence additionally needs a positive selected sum over the rules
whose source block contains the target. These identities and their typing
are not part of the 11-operation subtotal. In particular, D_x Z is an
ordinary convolution of different rows, not the required T_x.

Factoring the table into p position tracks avoids explicitly listing all
input blocks, but the append code has selected offsets. For one batch let

    z_0=1,   z_(r+1)=b^(|h_r(a_r)|) z_r,
    u_x=sum_(r=0)^(p-1) code(h_r(a_r)) z_r.                         (5)

The arithmetic then needs weighted row values L_i z_(r,i), coupled to the
selected letter on track r, as well as the final length factor. Independent
track masks do not establish these couplings. Products of their packed
integers again mix different rows. Fixed numerical coefficients in (5)
are available when each phase has a length independent of its input letter;
this is precisely the locally uniform restriction, whose compatible
universality interface has not been supplied here.

The complete ternary 90 has a 43-operation kernel and 47 outer operations.
An 11-operation transport would leave **36 outer operations** to pay for
geometry, input and acceptance, all five fields, rule and weighted selection,
packing, bounds and positive-variable adaptation. Neither 11 nor 43+11=54
is a complete universal count. The direct table sizes are implementation
cost indicators, not a lower bound against every compressed lookup scheme.

## 4. Decidability when every full phase block has aligned output

Here images may erase and need not have locally uniform lengths. Assume

    p divides |H(v)| for every v in Sigma^p.                         (6)

Condition (6) is effectively checkable. Equivalently, for every phase r
the residues |h_r(a)| modulo p are independent of a, say c_r, and
sum_r c_r=0 modulo p. Sufficiency follows by summing these residues;
necessity follows by varying one letter of a p-block at a time.

Let s be any finite prolongable seed, s prefix H(s), and let x be its
finite or infinite prefix limit. Letter occurrence in x is decidable.

First, the empty seed stays empty. Otherwise put m=p ceil(|s|/p).
Iterate s until an iterate has length at least m or an iterate stabilizes
below m. Prefix preservation makes the iterates nested, so each
non-stationary step increases length by at least one. Hence at most p-1
strict steps are needed to reach m, and an earlier stabilized case gives
the finite limit directly.

In the remaining case choose k with |H^k(s)|>=m and let V be its prefix of
length m. Then

    s prefix V prefix H^k(s).                                     (7)

By (6), |H(V)| is a multiple of p, and H(s) prefix H(V) gives
|H(V)|>=|s|. Therefore |H(V)|>=m=|V|, even when some images erase.
Both V and H(V) are prefixes of H^(k+1)(s), so V prefix H(V).

Let Delta=Sigma^p. Define the ordinary morphism g on Delta by splitting
H(v) into its consecutive p-letter blocks. Its image may be empty.
For any word of Delta, unblocking g is exactly applying H to the unblocked
word: each input block starts at phase zero and (6) aligns all output
boundaries. Thus the blocked V is a prolongable seed for g.

Applying H^n to (7) gives the sandwich

    H^n(s) prefix H^n(V) prefix H^(n+k)(s).                         (8)

Their prefix limits coincide, finite or infinite. The ordinary substitution
therefore generates x from the **whole block word V**. Form the finite graph
with edges v->w when the block w appears in g(v). The blocks occurring in
x are exactly those reachable from any block in V: descendants occur in
some iterate, and the iterates of V are nested prefixes, so no occurrence
is lost from their limit. A target letter occurs precisely when it occurs
in a reachable block. Finite graph reachability decides this predicate.

Using only the first block is incorrect. Already for p=1, g(1)=1,
g(2)=22 and seed12, the first block generates only1, while the actual limit
also contains2. The whole-prefix construction in (7) avoids this issue.

Consequently, the all-block-output-aligned subclass cannot serve as an
undecidable marker-occurrence interface, even with variable lengths or
erasing images. This does not rule out nonaligned locally uniform PD0L,
general PD0L batching, other acceptance predicates, or a more economical
joint-selector encoding. It rules out making this particular alignment
restriction as a universality-preserving arithmetic shortcut.

## 5. Fresh finite evidence and scope

The author checker verifies all 11 primitives and both source comparisons,
1,904 local batches for periods1,2,3, and 24 packed histories containing
120 macro rows. Its short-queue checks give 32 exact cycles and32 escapes
to a batchable queue. Every local batch is compared with p sequential reads
and both scalar identities.

For the alignment lemma it checks 881 two-phase tables over a two-letter
alphabet and all prolongable seeds of lengths1,2,3: 2,480 valid cases,
including912 with an erasing image, 1,440 without locally uniform lengths,
and208 that stabilize before reaching an aligned length. It checks the
block substitution, prolongability, commuting iterations, graph closure
and agreement with direct seed iteration. It also includes the first-block
counterexample above. These finite checks support the general proofs;
they do not establish an unprovided universal arithmetic compiler.

Review status: author and two independent complete scoped proof/source
reviews and fresh receipt checks PASS.

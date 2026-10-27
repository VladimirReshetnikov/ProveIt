# Polynomial-space contraction by streaming balanced separators

## Scope

This second new local algorithm uses the exact pair-weight arrays and the
full crossing Cauchy modes of the previous joint-Cauchy packet. It replaces
global tuple enumeration by a hierarchy of finite distributive factorizations.
It needs no exponential cache and treats each leaf group evaluation as an
expensive recursive child contraction. Its polynomial-space guarantee is the
same resource regime as the previous 76.90899 and composed66.19272 bounds.

## Exact mode-graph identity

Fix an active call, interpolation data and an exact weight allocation b_gh.
Each directed pair e=(g,h) has a finite domain of d_e exponent tuples. For
an empty domain the array contributes zero. Otherwise its contribution is

    Z = sum_{x in product_e [d_e]} product_{g=1}^r Z_g(x_incident(g)).

Because all exact pair weights are fixed, there is no remaining coupled
budget constraint within this Cartesian product. Every Z_g depends only on
its incident pair indices. Evaluating Z_g means contracting a child network
of at most (2/r+o(1))M wires, with the unchanged precision convention.

Let S be a subset of groups and fix all indices between S and its complement.
Partition S into two parts A,B. Its conditional contraction is exactly

    Z_S = sum_{x on directed pairs A<->B} Z_A * Z_B.

Use a fixed balanced binary tree of group subsets. Compute this identity
depth first, retaining only the current pair indices and ring accumulators.
A singleton leaf calls Z_g on its incident assigned indices. Only the cuts
on the path to that leaf are enumerated together; internal choices in disjoint
subtrees are summed independently. This is the saving over global tuple
enumeration. No lookup table or cheap group-factor oracle is assumed.

The implementation `streaming_contract` in adaptive_blocks.py carries out
this identity for any fixed number of groups. It is tested against literal
global sums in integers and modulo powers of two, including16-group cases.

## Cost from the cut pairs on a path

Let h_e=log2 d_e and let I_pi be the union of directed cut pairs on a root-to-leaf
path pi. These cut sets are pairwise disjoint. That leaf is called exactly
product_{e in I_pi}d_e times. The total number of leaf and internal operations
is bounded by a fixed polynomial times

    sum_pi 2^(sum_{e in I_pi} h_e).

There are r leaves, and the tree has fixed size. The subset entropy bound
for nearly lossless packing and slope-four modes is

    sum_{e in I} h_e <= (sqrt(|I|)/r + o(1)) K,
    K = (pi sqrt2/ln2) M/sqrt(u).

For a balanced binary tree define

    v(1)=0,
    v(r)=2 floor(r/2) ceil(r/2)
          +max(v(floor(r/2)),v(ceil(r/2))).

Then |I_pi|<=v(r). If r is a power of two, direct induction gives

    v(r)=2(r^2-1)/3.

For r=16, v(r)=170, whereas global mode enumeration uses all240 directed
pairs. The local coefficient is therefore sqrt170/16 instead of sqrt240/16,
a ratio sqrt(17/24). This is an upper-bound coefficient comparison. It does
not claim that every actual input or timing gains that factor.

The local recurrence is

    T_d <= poly(s) 2^((sqrt170/16+o(1))K_d) * 16 T_{d+1}
           + poly(s+description_length) 2^((sqrt170/16+o(1))K_d).

The root description is shared; its polynomial cost is not multiplied into
the branching count at every depth. The remaining polynomial-in-s factors
over O(log log s) recursion levels are lower order in the exponent.

## A simple schedule and its exact leading constant

Let lambda=ceil(log2 s), b_buf=ceil(6log2 lambda), and choose the integer

    B=floor(lambda/80)-ceil(sqrt(lambda)).

For sufficiently large sizes B>0. Set

    r=16, H=ceil(s/lambda),
    u_0=B,
    u_d=floor(3B/4^d) for d>=1,
    a_d=sum_{j<=d}u_j+(d+1)b_buf.

The root range is (1+o(1))lambda/80, while the total of the tail ranges
is at most B. Consequently a_0<=lambda/80-Omega(sqrt(lambda)) and
a_d<=lambda/40-Omega(sqrt(lambda)) uniformly through the active depths.
The inward square-root guard absorbs the O((log lambda)^2) additive buffers.

At the root, Q^2 Delta with Q=16^a0 and Delta=ceil(s^0.9) has logarithm
at most8a0+0.9lambda=lambda-Omega(sqrt(lambda)). Below the root, orient
the bipartition as retained/fresh. The retained-side row term Q Delta has
logarithm at most4ad+0.9lambda=lambda-Omega(sqrt(lambda)). Fresh-side
and rounding terms have exponent at most9/40+o(1)<1. Thus the inherited
asymmetric nearly lossless packing lemma applies uniformly, giving child
ratio1/8+o(1), in particular at most1/6 eventually.

To avoid a circular depth assumption, first verify these estimates through
hypothetical depths ceil(log_6 lambda)+1 with M>H. In that range

    u_d >= lambda^(1-ln4/ln6+o(1)) -> infinity.

The verified1/6 contraction then proves that no active path is deeper.
All packet degrees are below the normalized s^0.9 premise. The same
additive-buffer argument as in the asymmetric packet gives
p_t<=(6+o(1))MD/u with polynomial precision and entry-description sizes.

Let K0_scale=(pi sqrt160/ln2)s/sqrt(lambda). The root contributes
K0_scale. At the first tail level the K contribution is
(1/(4sqrt3)+o(1))K0_scale; later contributions have ratio1/4+o(1).
Hence the sum over the entire path is

    (1+1/(3sqrt3)+o(1)) K0_scale.

Multiplying by sqrt170/16 yields the exact coefficient

    C_stream = [5pi sqrt17/(2ln2)] [1+1/(3sqrt3)]
             =55.70947831890997....

The total deterministic time is

    poly(s+description_length)
    * 2^((C_stream+o(1))s/sqrt(log2 s)),

and space is polynomial. A safe eventual time coefficient is56.
For a rational certificate, use pi<22/7, ln2>6931/10000, sqrt17<33/8,
and sqrt3>12/7. These give C_stream<16259375/291102<56; the checker
verifies the square-root brackets and the final rational inequality.
The group count and binary separator depth are constants. Exponent tuple
rank/unrank, pair weights, current assignments, ring accumulators, packet
data, interpolation data and immutable descriptions all have polynomial
size. Entry evaluation and direct leaves are lower-order costs exactly as
under the inherited normalized interface.

## Parameter search used only to choose the simple certificate

A floating-point exploratory search examined fixed alphabets4 through128
and every root/tail alphabet pair4 through64, using the displayed cut-pair
recurrence and the exact continuous tail-budget minimization. The simplest
fixedr16 was best in those finite search ranges:55.7094783. The next
root/tail pairs were20->16 at55.7177317 and24->16 at55.7607397.
These exploratory rankings are not an optimality theorem. The proof above
depends only on the explicitr16 schedule and its exact constants.

## Prior work and novelty boundary

The pair-weight split, the slope-four mode factorization and the nearly
lossless asymmetric packing are inherited. Distributivity and balanced
recursive summation are classical. The additional contribution relative
to the inspected packets is their use to stream the mode graph in polynomial
space, paying for all child contractions and charging entropy only to the
cut-pair sets along a separator path. The previous packet's optional mode
graph theorem explicitly stored group and block tables; this construction
requires neither. No smaller logarithmic order for general SAT is claimed.

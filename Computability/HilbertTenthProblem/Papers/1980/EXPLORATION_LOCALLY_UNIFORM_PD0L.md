# Locally uniform PD0L: exact resampling and an aligned decidable subclass

Phase-dependent output lengths admit an exact formula, but it requires the
same indicator sequence at two different bases. A periodic mask alone does
not enforce that relation. Moreover, when the total output length of one
phase cycle is divisible by the period, finite letter occurrence is
decidable. This rules out that aligned subclass as a replacement universal
marker-occurrence machine. It is not a nonuniversality result for all locally
uniform PD0L systems and supplies no improved certificate count.

The companion `../verification/explore_locally_uniform_pd0l.py` checks the
word identities, position phases, productivity criterion, block construction
and finite reachability on bounded examples. Its adjacent JSON is the receipt.

## 1. Source definitions and the exact universality boundary

Use Endrullis and Hendriks, [On Periodically Iterated Morphisms](https://arxiv.org/pdf/1207.2336),
Definition 1.1. A tuple H=(h_0,...,h_(p-1)) acts simultaneously on a word by
replacing its letter at position j with h_(j mod p) of that letter, then
concatenating the images. The seed s satisfies s prefix H(s), so its iterates
form a prefix-increasing sequence. Definition 1.7 calls the system *locally
uniform* when |h_r(a)|=k_r is independent of a. Globally uniform further
requires all k_r equal; Proposition 1.10 makes the productive globally
uniform case automatic. These notions cannot be interchanged: Examples
1.11--1.12 give locally uniform words that are not morphic.

Theorem 4.15(i) establishes undecidable finite letter occurrence in productive,
non-erasing PD0L systems. It is an existential occurrence statement, independent
of the additional infinite-occurrence result. Its Definition 4.3 construction
is not locally uniform: at the same phase, the spacer and Q have image length
one while a has image length d. Furthermore |h_i(e)|=d-i+1 gives d different
lengths across the phases. That construction does not establish a small fixed
set of lengths across the varying program family. Nothing here transfers its
undecidability to locally uniform systems.

The remaining sections are direct lemmas. They allow k_r=0, so individual
morphisms may erase every letter. No non-erasing premise is hidden.

## 2. The exact simultaneous word and phase formulas

Let p>=1, k_r>=0, K=sum_(r<p) k_r, and

    kappa_0=0,  kappa_r=sum_(j<r) k_j.

Assign distinct digit codes c(a) in {1,...,b-1}, for a fixed integer base b.
Write code_b(x)=sum_j c(x_j)b^j, including code_b(empty)=0. For a finite input
x, define its phase/letter indicator polynomials

    E_(r,a)(z)=sum_{t>=0: pt+r<|x| and x_(pt+r)=a} z^t.

The exact identities are

    code_b(x) = sum_(r,a) c(a)b^r E_(r,a)(b^p),
    code_b(H(x)) = sum_(r,a) code_b(h_r(a)) b^kappa_r E_(r,a)(b^K).  (1)

The source cell at position pt+r contributes its output at positions

    Kt+kappa_r+u,  0<=u<k_r.                         (2)

Indeed, the t preceding full phase cycles contribute Kt symbols and the
preceding phases of the current cycle contribute kappa_r. Summing these
disjoint output blocks proves (1), including erased images and an incomplete
last phase cycle. If |x|=pt+r, its output length is Kt+kappa_r.

The next generation applies morphism index

    (Kt+kappa_r+u) mod p                            (3)

to that child. When p does not divide K, the input phase r alone generally
does not determine this phase: the quotient t matters as well. For K>0 its
contribution depends on t modulo p/gcd(p,K).

All coefficients and the two bases in (1) are fixed numerals. The unbounded
indicator polynomials are not numerals. Supplying their two evaluations as
independent coordinates loses the requirement that they encode the same
sequence. Neither ordinary multiplication nor an equality between those
two coordinates enforces that requirement. No arithmetic cost for this
resampling constraint, or for a complete PD0L history, is claimed here.

A concrete nonaligned example uses p=2, (k_0,k_1)=(1,2), b=3,
h_0(a)=a, h_1(a)=aa, and input x=1212, with digit codes 1,2.
Both nonzero indicator polynomials equal 1+z. Their evaluations are 10 at
b^p=9 and 28 at b^K=27. The true output 122122 has code700; substituting the
input evaluations into the output linear form incorrectly gives250. The
phase-zero source positions0 and2 have children starting at0 and3, with
different next phases. This is a resampling counterexample, not a claim
about the computational power of this example or of nonaligned systems.

## 3. Productivity and arbitrary seed lengths

Let f(n)=K floor(n/p)+kappa_(n mod p). This is the length of H applied to
any n-letter word. Since k_r>=0, f is nondecreasing. For a valid nonempty
seed of length ell, productivity is equivalent to

    f(n)>n for every integer n>=ell.                 (4)

If some n>=ell satisfies f(n)<=n, monotonicity bounds every iterated length
by n. Conversely, (4) makes the successive lengths strictly increase. Prefix
monotonicity turns unbounded lengths into an infinite limit. The empty seed
is not productive. This also proves the criterion in Proposition 1.8 directly.

If K<p, f(n)-n is eventually negative. If K=p, f(n)=n at every multiple of p.
Neither case is productive. If K>p, (4) is a finite test: for each residue
r, check its least representative n>=ell, because adding p increases
f(n)-n by the positive constant K-p.

For a productive system K>p, H is continuous on infinite words in the prefix
metric: an input prefix of length n determines an output prefix of length
f(n), and f(n) tends to infinity. Thus the prefix limit x satisfies H(x)=x,
even when some k_r vanish.

## 4. The aligned subclass p divides K

Assume p|K and productivity. Put m=K/p>=2. Use the finite block alphabet
Delta=Sigma^p. For a block B=a_0...a_(p-1), concatenate

    h_0(a_0)...h_(p-1)(a_(p-1))

and split its K letters into m consecutive p-letter blocks. This defines an
m-uniform morphism g:Delta* -> Delta*. Every full input block starts at a
multiple of p, and every full output block group has length K divisible by p,
so concatenation gives the exact commutation

    flatten(g(V)) = H(flatten(V))                    (5)

for every block word V. Empty phase images cause no difficulty because the
whole block image still has length K.

The original seed need not have length divisible by p. Compute its iterates
until at least p letters are available, and let B be the first p-letter block
of the resulting prefix. Productivity guarantees termination. Since H(x)=x,
g(B) starts with B. Its iterates are nested prefixes of x of lengths p*m^t,
so

    x = flatten(g^omega(B)).                        (6)

In particular this procedure has not discarded any initial seed symbols.
Every finite prefix of x, including the entire seed even when |s|>p, occurs
inside a sufficiently long iterate of B.

Construct the finite directed graph on Delta with an edge U->V whenever V
is one of the blocks of g(U). A letter a occurs in x exactly when some block
reachable from B contains a. Both directions follow from (6): descendants
appear in successive iterates, and every finite position is eventually in
one of those iterates. Breadth-first search decides occurrence. At most
|Sigma|^p block vertices need be explored; no efficiency claim is needed.

For a nonproductive valid system, direct iteration eventually stabilizes at
its finite prefix limit, so occurrence is decidable there as well. The
productivity test above decides which procedure to use. Consequently finite
letter occurrence is decidable on the entire aligned locally uniform class.

The proof does not cover p not dividing K. Refining phases enough to determine
(3) for one step is not a proof that a fixed refinement closes under all
iterations. The status of general locally uniform marker occurrence is left
unresolved here. Neither productivity nor a high subword complexity supplies
the missing existential universality reduction.

## 5. Finite evidence and certificate scope

The checker compares (1)--(3) against direct concatenation, includes erased
images and partial phase cycles, and records the explicit10-versus28
resampling example. Its aligned systems include zero image lengths,
nonconstant phase lengths and initial seeds not divisible by p. It checks
prolongability of B, commutation (5), seed-prefix preservation, and equality
between graph-reachable marker sets and direct iterates long enough to cover
the finite block graph. Finite productivity tests are checked against the
exact scalar length recurrence.

These are checks of the stated lemmas. No transition-table lookup, shared
digit-sequence conversion, positive-variable adaptation, kernel, raw-input
loader or universal certificate has been implemented or priced.

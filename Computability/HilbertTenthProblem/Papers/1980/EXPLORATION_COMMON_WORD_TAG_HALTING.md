# Common-word appendants make tag halting decidable

This is an elementary obstruction to simplifying the tag-system
word-substitution interface. It is not an operation lower bound for
general tag systems and does not change the established universal
certificate of 90 operations.

## 1. The restricted family

Fix a finite alphabet, deletion number beta>=1, a nonempty word v of
length m, and a nonnegative integer k_a for each symbol a. Let

    h(a)=v^(k_a).

The powers here mean ordinary word concatenation, with exponent zero
giving the empty word. The initial word w is arbitrary. As usual, a
queue shorter than beta halts; otherwise delete its first beta symbols
and append the production determined by its first symbol.

**Theorem.** Halting from w is decidable. More precisely, the exact
halting time, or the fact of nonhalting, can be computed using a finite
prefix and one period of an explicitly known integer walk.

This covers a binary system with one empty appendant and one arbitrary
fixed appendant. If both appendants are empty, the queue simply loses
beta symbols per step and halts after floor(|w|/beta) steps. Thus a
universal binary tag-halting construction cannot replace one appendant
by the empty word while keeping only the other production.

## 2. The stream is known before the computation

Consider the infinite ultimately periodic word

    P=w v v v ... .

For every actual finite sequence of transitions, all symbols produced
so far form a prefix w v^K of P: each production only appends more
copies of the same word. Before a legal transition j, its first symbol
is therefore

    p_j=P[beta*j].

It is already inside the produced prefix because the queue contains
at least beta symbols. The cumulative number of deleted symbols is
exactly beta*j.

Set j0=ceil(|w|/beta) and p=m/gcd(m,beta). For j>=j0,

    p_j=v[(beta*j-|w|) mod m],

so the symbol sequence p_j has period p (possibly a smaller one as
well). Define an ordinary integer walk from L_0=|w| by

    L_(j+1)=L_j+m*k_(p_j)-beta.                    (1)

Until its first value below beta, L_j is exactly the actual queue
length. This follows by induction: a current length at least beta
makes the stated read legal and selects exactly the stated appendant.
At the first crossing the new length is nonnegative, since a legal
step starts with at least beta symbols and appends a nonnegative
number. Therefore halting is exactly the first j with L_j<beta.

## 3. Finite decision and exact time

First inspect the j0 prefix steps, stopping if a length below beta is
encountered. Let L=L_(j0). For the periodic part define

    d_r=m*k_(p_(j0+r))-beta,       0<=r<p,
    s_0=0, s_r=sum_(i<r) d_i,     1<=r<=p,
    Delta=s_p.

The length before phase r of period k is exactly

    L+k*Delta+s_r,               0<=r<p, k>=0.      (2)

If Delta>=0, all such lengths are at least the corresponding lengths
in the first period. Thus a short value occurs precisely when
L+s_r<beta for some phase r. The first such phase gives the exact
halting time j0+r; otherwise the computation never halts.

If Delta<0, put a=-Delta. For each phase r, the first period having
a short value at that phase is

    k_r=max(0, floor((L+s_r-beta)/a)+1).

The exact halting time is

    j0+min_(0<=r<p) (p*k_r+r).                    (3)

This is finite arithmetic on known integers. The intermediate walk
after its first short value need not describe legal queue steps;
formula (3) selects the earliest short value, for which the induction
in Section 2 applies.

## 4. Relevance and scope

Removing intermediate prefix guards from an existential halting
certificate, as proved in
`EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md`, leaves the
variable-length morphism as an important encoding cost. Making all
appendants powers of one word does simplify that morphism, but it
also makes every initial-word halting question decidable by this
theorem. Such a restricted family cannot supply the required universal
halting language under an effective input encoding.

The theorem uses the common-word hypothesis, not merely a small
alphabet, a small number of productions, or unequal production lengths.
It makes no claim about arbitrary binary tag systems or their other
reachability and output predicates. The proof is an original deduction
in this investigation, rather than a universality statement attributed
to an external source.

`../verification/explore_common_word_tag_halting.py/.json` compares
the algorithm with direct queue execution on bounded binary families.
Every predicted finite halting time is checked exactly. For predicted
nonhalting, the finite run is a regression only; the proof of absence
of a later halt is the nonnegative-drift argument above.

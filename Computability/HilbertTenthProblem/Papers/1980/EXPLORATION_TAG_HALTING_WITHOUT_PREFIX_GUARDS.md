# Tag-system halting needs no causal-prefix guards

This note removes a proof obligation from the finite-stream tag-system
proposal. It does not supply a counted Diophantine encoding or improve
the established universal bound of 90. The result is a general elementary
equivalence, valid also for erasing productions and arbitrary finite
alphabets. It concerns eventual halting; a proposed stream need not
describe exactly the stated number of legal transitions.

## 1. A finite-stream criterion

Fix a finite alphabet, a deletion number beta>=1, and one finite
appendant h(a) for each symbol a. A queue of length at least beta takes
one step by deleting its first beta symbols and appending h(a), where
a was its first symbol. A shorter queue halts.

For an initial word w, choose a finite selector word

    s=s_0 ... s_(t-1)

and form the ordinary concatenation

    U=w h(s_0) ... h(s_(t-1)).

Require only the following two conditions, with zero-based positions:

    U[beta*i]=s_i for every 0<=i<t,                 (1)
    beta*t <= |U| < beta*(t+1).                    (2)

Condition (2) ensures every position in (1) exists. The empty selector
is permitted and satisfies the conditions exactly when |w|<beta.

**Theorem.** The actual tag system halts from w if and only if such a
finite selector exists. No intermediate queue-length inequalities are
required.

## 2. Proof by the first short prefix

For a proposed selector define the produced prefixes and formal lengths

    U_j=w h(s_0) ... h(s_(j-1)),
    ell_j=|U_j|-beta*j,                            (3)

for 0<=j<=t. The final condition gives 0<=ell_t<beta, so there is a
least j<=t such that ell_j<beta. If j=0, the initial queue already
halts. Otherwise ell_i>=beta for every i<j.

Inductively, immediately before transition i<j the actual queue is
the suffix of U_i beginning at position beta*i. This suffix has length
ell_i>=beta. Its first symbol is U_i[beta*i]; that position lies
inside U_i, which is a prefix of U. By (1) it equals s_i. Deleting
beta symbols and appending h(s_i) therefore produces exactly the suffix
of U_(i+1) beginning at beta*(i+1).

Thus the first j proposed steps are actual legal steps. Their resulting
queue has length ell_j. If j>0 then

    ell_j=ell_(j-1)-beta+|h(s_(j-1))|>=0,

so it has a genuine length between zero and beta-1 and halts. Symbols
or apparent steps after this first halt do not affect that conclusion.
The argument also proves that a proposed certificate of length t
implies actual halting in at most t transitions.

Conversely, let an actual run halt after t legal transitions and use
its first symbols as the selector. The produced stream is U. At each
transition the head occurs at position beta*i, proving (1). Exactly
beta*t symbols were consumed, leaving fewer than beta, proving (2).
This includes t=0 and allows empty appendants.

## 3. A deliberately noncausal certificate

Take beta=2, initial word w=00, and productions

    h(0)=0, h(1)=100.

The real computation is 00 -> 0 and halts after one transition. Yet
the selector s=001 gives

    U=00 | 0 | 0 | 100 = 0000100.

Its positions 0,2,4 read 0,0,1, and |U|-2*3=1. It therefore satisfies
(1)-(2). Its formal prefix lengths are 2,1,0,1: the third selected
symbol is supplied by its own later appendant. This is not a legal
three-step computation. The theorem correctly extracts the real halt
after the first step, rather than asserting causality of the whole
selector.

## 4. Consequence for the proposed arithmetic architecture

Section 6 of `EXPLORATION_FINITE_UNIVERSAL_HISTORY_VERIFIERS.md`
previously required all prefix inequalities to certify an exact
tag computation. For representing the eventual-halting language,
(1)-(2) already suffice. A future arithmetic encoding can omit those
prefix guards and avoid paying for a separate prefix-positivity or
ballot condition.

The remaining obligations are substantial: encode one common selector,
its variable-length morphism image, the sampled symbols in that image,
the final length window, and a faithful ordinary-input interface.
Their operation counts are not supplied here. Published tag-system
universality is not by itself a free input compiler. The distinction
between deletion number two and two productions also remains unchanged.

`../verification/explore_tag_halting_without_prefix_guards.py/.json`
exhaustively compares this stream criterion with direct queue execution
on bounded binary systems. It checks every accepted stream by extracting
the first short prefix, includes the noncausal example above, and checks
the converse for every direct run halting within the tested depth. The
general theorem is proved in Section 2; the finite regression supports it.

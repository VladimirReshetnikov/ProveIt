# Tag lowering gives zero protected debt

## Scope and statement

This is an ordinary all-natural mathematical proof for the new ZC215
command parser. It does not assume any particular AX stack contribution.
The parser uses DROP tag 0, NIP tag 1, MP tag 2, and AX tags at least 3.
DROP and NIP each consume one Cantor field. The new CB1 refill, started
from counter 1 and residual 0, enumerates every raw candidate 0,1,2,... .
Positive command continuations are decremented before their first field
is read. The assertion concerns that exact scheduler; a skipped-candidate
schedule or a positive initial cutoff requires a separate argument.

**Theorem.** Every command prefix of the infinite syntactic word

    W(0) W(1) W(2) ...

contains at least as many DROP occurrences as NIP occurrences. In
particular, the conservative balance assignment DROP=+1, NIP=-1,
MP=AX=0 has minimum prefix balance zero. No finite testing, asymptotic
estimate, initial truth head, or positive AX contribution is needed.

## Exact parsing and encoding

Put P(a,b)=(a+b)(a+b+1)/2+b. For a command k, its complete field list is

    DROP:       [0]
    NIP:        [1]
    MP(x):      [2,x]
    AX(c;x,y):  [c+3,y,x].

Let E([a1,...,ar],v)=P(a1,P(a2,...P(ar,v)...)). For a nonempty finite
command list L=[k1,...,ks], define its *raw* encoding rho(L) backwards by

    rho([k])   = E(fields(k),0),
    rho(k::L)  = E(fields(k),1+rho(L)) when L is nonempty.

This is exactly the existing first-command/positive-continuation
convention. In particular rho([DROP])=0 is a valid nonempty candidate.
It is not the encoding of an empty continuation: a final DROP inside a
longer word has positive residual 1 at its predecessor.

For every n, its syntactic parse W(n) is nonempty and finite. Every
nonempty continuation has raw index r-1<n, since the residual r is at
most n. The field counts determine the command boundaries uniquely.
Induction on the continuation index proves both identities

    rho(W(n))=n,                    W(rho(L))=L.

The second identity is for every finite nonempty list of commands with
natural fields; it includes all zero aliases. Thus this proof does not
need decoded formulas or theoremhood.

## The injection

An occurrence is a pair (n,j), meaning command j of W(n), numbered from
zero. Let (n,j) be a NIP occurrence. Form L' by replacing that occurrence
with DROP and leaving every other command and field unchanged. Put

    m = rho(L'),                   Phi(n,j)=(m,j).

The two commands have the same one-field arity. Hence W(m)=L', and
Phi(n,j) is indeed a DROP occurrence at the same command position.

Cantor pairing is strictly increasing in each coordinate. At the
modified command, replacing tag 1 by 0 strictly decreases its encoded
suffix: if its residual is r, the exact decrease is

    P(1,r)-P(0,r)=r+1>0.

Every enclosing successor and pairing in the preceding command
prefix preserves this strict decrease. Therefore

    m<n.

The map is injective. From an image occurrence (m,j), replace that DROP
back with NIP and apply rho; this recovers the unique original n and
position j. Distinct NIP occurrences therefore have distinct DROP
images, all lying in strictly earlier raw candidates.

Now stop the infinite schedule after any finite command prefix. Every
NIP occurrence in this prefix has its DROP image in an earlier completed
candidate, hence in the same prefix. The injective map proves the claimed
count inequality. The same argument applied to the prefix ending at a
particular NIP shows that, immediately before that NIP, at least one
unmatched earlier DROP exists.

Every actual execution before its first halt is a prefix of this
syntactic schedule. If an actual NIP is reached, all the earlier
candidates containing its image and the images of previous NIPs have
completed without halting. Thus the injection counts executed DROP
commands, not merely hypothetical commands in skipped or aborted words.

## Protected arbitrary tails

Represent the current numerical stack as an explicit list of theorem
heads above a fixed arbitrary natural tail J. Start with zero explicit
heads, so the initial stack is exactly J. Start top and cache at theorem
zero. DROP pushes one theorem head; NIP removes one; MP never reduces the
explicit length; AX adds ten theorem heads in the present source.

By the theorem, the explicit protected length is positive whenever a NIP
is about to pop. That NIP therefore reads an explicit theorem head,
never J. Its halt test is on the theorem-valued cache. Induction on the
actual commands proves theoremhood of top/cache and all protected heads,
and hence every halt supplies a native refutation.

This applies to the exact initialized stack J=5, without interpreting any
part of 5 as a theorem stack. It also applies to every other natural J.
Numerical zero aliases do not invalidate the logical list witness:
unpair(P(x,v))=(x,v) holds exactly, even when x=v=0.

The argument is stronger than the previously supplied diagonal credit
proof: **AX can contribute zero protected heads and the scheduler still
has zero protected debt.** This does not itself authorize deleting AX
outputs: such a source would still need its own numerical-calculus and
strong-completeness proof, as well as a binary implementation.

## General form

The same injection works for any exhaustive increasing enumeration by a
strictly coordinate-monotone, uniquely parsed nested code in which a
push command has a smaller tag than a pop command, the two have the same
field arity, and changing the tag preserves the rest of the command word.
The result concerns prefix safety, not just final balance. It explains
why the combination of DROP-first tags and exhaustive enumeration from
zero can replace an initialized reserve of theorem heads.

# Exact contextual interfaces for the filtered paired carry graph

The centered filtered controller has Boolean read bits d0,d1, append bits
a0,a1, and fixed integer weights g0,g1,g2:

    a0+a1+d0=1,
    3*k_next=k+g0*a0+g1*a1+g2*d1.                      (1)

Its terminal carry is zero. The optimized arithmetic component is
[filtered paired69](native_controller_paired_filter70.md), or72 with paid
fixed block alignment. This note supplies exact contextual code identities
and one nontrivial physical phase cycle. It supplies no universal compiler,
no typing of a selected block alphabet, and no new complete bound. The
established complete universal bound remains76.

## 1. Every recurrent block is an edge between disjoint Boolean words

Use Z=00, P=10 and S=01 for physical queue symbols. Every append belongs
to this alphabet by(1), so every queue symbol does after one sweep. Fix a
block length ell. For two Boolean ell-bit vectors u,v with disjoint
supports, define the physical word

    Code(u,v)_j=(v_j, 1-u_j-v_j).                      (2)

This is a bijection between disjoint pairs(u,v) and words over{Z,P,S}.
For a physical word with planes(p,s), the inverse is u=1-p-s, v=p.

The filter allows the read/append block pair

    Code(u,v) -> Code(u',v')

if and only if **u'=v**, coordinate by coordinate. Indeed the residual
in(1) at position j is

    v_j+v'_j+(1-u'_j-v'_j)-1=v_j-u'_j.

Thus the physical filter exactly advances an edge(u,v) to an edge(v,v').
It can preserve a current cell state as the previous state in the next
queue sweep. This is a contextual interface rather than a single fixed
binary alphabet. The vertex set could be restricted to finitely many
chosen vectors, for example one-hot vectors with disjoint phase classes,
but the restriction is an additional obligation: equation(1) by itself
allows every disjoint pair, not only the proposed codes.

Write B=3^ell, H=(B-1)/2 and let U,V,V' be the ordinary ternary values of
u,v,v'. For an aligned macro transition, the exact carry equation is

    B*k_next=k+(g1+g2)H-g2*U-(g1+g2)V+(g0-g1)V'.       (3)

This follows by summing(1) over the block, using append words V' and
H-V-V', and secondary read word H-U-V. Conversely, divisibility by B
recovers each integral microscopic carry by successive reductions modulo3.
Equation(3) is therefore an exact candidate-synthesis constraint for the
whole block, without a hidden intermediate-state assumption.

## 2. Why one repeated binary code fails, and a two-phase alternative

Suppose two fixed physical codewords C0,C1 are reused on both read and
append sides. If the three logical pairs 0->0,0->1,1->0 all satisfy the
filter, then C0=C1. Write Ci=(pi,si). The first and third pairs give
`2p0+s0=1` and `p1+p0+s0=1`, hence p1=p0. The second pair then gives
s1=s0. This argument holds at each micro position and for every block
length. In particular such an encoding cannot realize a binary scan
table containing all four logical input/output pairs. It does not apply
to context-dependent codes or to codes changing between phases.

There is a simple exact phase-dependent physical interface:

    ordinary phase: logical0=Z, logical1=S;
    temporary phase: logical0=P, logical1=S.

Every one of the four ordinary-to-temporary logical pairs satisfies(1).
The identity-return pairs P->Z and S->S also satisfy it. This gives a
potential two-sweep interface, but does not yet supply its finite carry
controller, phase boundaries or an ordinary-input loader.

If the identity-return sweep is required to keep one constant centered
carry kappa while handling either symbol, P->Z gives2*kappa=0 and S->S
gives2*kappa=g1+g2. Thus that particular constant-state recoder requires
kappa=0 and g1+g2=0. This is a scoped necessary condition, not an exclusion
of varying-state or context-annotated return sweeps.

## 3. An exact scalar projection of the coupled queue and carry

Let W=3^m and N0,N1 be the current two queue integers. Set

    T=g1+g2*W, F=g0-(W+1)T,
    Z=k-T*N0+g2*N1, V=2Z-T.                           (4)

Every physical step obeys the identities

    3*Z_next=Z+T+F*a0,
    3*V_next=V+2F*a0.                                 (5)

To prove them, substitute

    3*N0_next=N0-d0+W*a0,
    3*N1_next=N1-d1+W*a1

and(1) into(4). The coefficients of d1 cancel; those of d0 and a1 become
T, so their sum is T*(1-a0), giving(5). No injectivity of this projection
is asserted. Nor may an arbitrary path of(5) be lifted without recovering
both typed queues and the integral carry constraints.

For a run starting at(I0,I1,cs) and ending at(0,0,0), with q=3^t and
primary append word A0, telescoping gives the exact necessary identity

    F*A0+T*((q-1)/2-I0)+g2*I1+cs=0.                  (6)

It is also obtained by eliminating the secondary append word A1 from
`g0*A0+g1*A1+g2*(I1+W*A1)=-cs` and
`A1=(q-1)/2-I0-(W+1)*A0`. This reduction can be used to check proposed
finite graphs; the Boolean constraints on all words remain essential.
No general decidability or universality conclusion follows here.

## 4. A forced phase cycle whose length depends on the queue width

Take(g0,g1,g2)=(2,3,-3) and start at carry0. The whole reachable carry
graph, including the initial fourth physical symbol11, is

| Carry | Read | Append | Next carry |
|---:|---|---|---:|
| 0 | Z | S | 1 |
| 0 | P | Z | 0 |
| 0 | S | S | 0 |
| 0 | 11 | Z | -1 |
| 1 | Z | P | 1 |
| 1 | S | P | 0 |

There are no other outgoing integral edges from these states, and carry-1
has no outgoing edge at all. Hence the part that can return to carry0
has exactly states0,1 and the five recurrent edges shown.

Starting from the empty physical queue Z^m and carry0, the path is forced.
After i steps, for1<=i<=m, it is

    queue Z^(m-i) S P^(i-1), carry1.

The next step produces P^m with carry0. Then m repetitions of P->Z erase
the queue. All2m+1 configurations before the return are distinct, so the
period is exactly2m+1 for every m>=1. This is genuine variable-width phase
dynamics, even though a complete two-state Mealy embedding is excluded
by the earlier repeated-label argument.

It is not an ordinary positive-input accepting witness: its starting
queue is empty. Moreover x=1 in the raw split interface forces the first
read11 and therefore the dead carry-1. No universal simulation or repair
of that input problem is asserted.

## 5. Evidence

The [checker](pell_kernel_paired_contextual_codes.py) exhausts all recurrent
codeword pairs through block length4, checks the collapse of distinct
fixed two-code alphabets and the two-phase physical interface, independently
expands(3)–(6), and verifies every edge of the exact small carry graph.
It checks the proved2m+1 cycles at widths1 through100. These checks support
the displayed universal identities, not an exhaustive search over
controllers or a compiler theorem. The [receipt](pell_kernel_paired_contextual_codes.json)
is replayed by default. Independent full proof, source and fresh default
review passed, including the exact whole carry graph and the scoped
limitations of the code interfaces.

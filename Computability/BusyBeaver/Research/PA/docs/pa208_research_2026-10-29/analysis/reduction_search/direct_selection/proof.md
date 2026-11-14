# Direct selection: two exact unary tests for the cache value one

The final U208 counter source has three commands. Its transfer command S has
all-natural semantics

\[
S(t,[x;v],d,h)=\begin{cases}\mathrm{halt},&h=1,\\(h,v,d,x),&h\ne1.\end{cases}
\]

The original implementation has 35 primitive occurrences: clear T (2), copy
H into T and X while clearing H (4), restore H from X (3), set X=1 (1),
destructive equality test H=X with halting equality arm (11), and pop W into
H (14). We retain clear T and the exact original pop macro, and replace only
source interval [3876,3895). No other retained control edge enters that
interval except its first ordinal. The exact source CFG checker verifies
all retained effects and edges after ordinal translation; source row 136 and
its complete address are unchanged.

## A 25-primitive implementation

The following notation denotes a binary source tree. CI and CD increment and
decrement their indicated register; a zero CD exits its enclosing left arm.
CB and CC use the source's usual break/continue depths. Let

\[
Z_r=((\mathrm{CD}_r,\mathrm{CB}_1),\mathrm{CH}),\qquad
M_{5,1}=(\mathrm{CD}_5,(\mathrm{CI}_1,\mathrm{CC}_2)).
\]

Z_r halts if its input register is zero, and otherwise decrements it once
and exits normally. M_{5,1} transfers H into T and clears H; its all-natural
proof is induction on the initial H.

After clear T, execute the tree

\[
(\mathrm{CD}_5,
 [\mathrm{CI}_1;Z_5;\mathrm{CI}_1;M_{5,1}]),
\]

then pop W into H. Brackets mean closed sequencing. Five binary associations
of the four factors are supplied as direct25_0 through direct25_4.

There are three exhaustive cases:

* h=0: the outer CD5 skips the entire body. T=H=0 before pop.
* h=1: the outer CD5 leaves H=0, CI1 sets T=1, and Z5 halts.
* h>=2: the outer CD5 and Z5 consume two units of H, while the two CI1
  instructions supply two units of T. M_{5,1} adds the remaining h-2 units
  to T and clears H. Hence T=h and H=0 before pop.

X and Y remain zero, and no other register is touched before pop. Therefore
all nonhalting cases have exactly the required S result after the retained
pop. The new body has 9 primitives, so the full S has 2+9+14=25. Every loop
terminates by a decreasing natural counter. This is an argument for every
natural input, independently of the finite numerical checks.

## A 26-primitive implementation reusing the original copy

Keep the original four-primitive copy of H into T and X. From T=0,X=0 it
returns T=h,H=0,X=h. Next execute

\[
(\mathrm{CD}_6,[Z_6;(\mathrm{CD}_6,\mathrm{CC}_1)]).
\]

If h=0, the outer CD6 skips the body. If h=1, Z6 halts. If h>=2, the two
CD6 tests consume two units and the remaining clear-X loop consumes h-2.
Thus every normal exit has T=h,H=X=0. The original pop then establishes the
same S contract. This body has 4+6=10 primitives and the full S has 26.

## Source and machine scope

The source generator verifies the exact retained CFG and checks 256 small
pre-pop stores for each variant. Those examples validate the implementation;
the exhaustive arithmetic case split and loop induction above supply the
all-natural reasoning. The comparison uses the exact final three-command
S interface, so no compiler change, numerical-calculus change, theory change,
stack-credit change, or startup-suffix change is needed at source level.

Smaller primitive count does not imply fewer Turing-machine states. The
baseline source has 197 distinct DAG nodes, the 25-primitive S sources 201,
and the 26-primitive S source 199. A literal allocation and its complete
whole-tape runtime proof remain separate obligations. These are experimental
source variants, not accepted sub-208 Turing machines.

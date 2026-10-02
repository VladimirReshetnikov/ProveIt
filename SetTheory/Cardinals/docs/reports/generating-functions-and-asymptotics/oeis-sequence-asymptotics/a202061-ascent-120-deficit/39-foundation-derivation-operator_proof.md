# Classical 120 avoidance: an exact algebraic height-walk reduction

Research draft, 1 October 2026. This is a proposed new structural reduction, not yet independently audited. The n^(3/8) conjecture is not proved here.

## 1. Normalized states

For a classical 120-avoiding ascent prefix, remove every value smaller than the largest lower endpoint of an already occurring increasing pair, and translate the remaining alphabet so its least allowed value is 0. Let a be the translated ascent budget (the next letter is at most a+1), let S={0=s_0<s_1<...<s_k} be the values already seen in the remaining alphabet, and let l be the last letter. Write m=max(S), h=a+1-m, and d_i=s_i-s_{i-1}. We have h>=1. The last letter is either 0 or the least positive member of S. This follows because, after appending i>0, the largest old value p<i is retained as the new zero and there is no old value strictly between p and i. Appending 0 gives last letter 0.

Appending a legal i in [0,a+1] creates no forbidden pattern after this normalization. Put p=max({s in S:s<i} union {0}). The exact child is

(a',l',S')=(a+1_{l<i}-p, i-p, {s-p:s in S,s>=p} union {i-p}).

In particular the last union must include the new value; the typeset recurrence in Conway et al. omits this insertion if its r has only the stated renumbering meaning.

Let E_h(R) be the suffix ordinary generating function when l=0 and the list of positive gaps is R. Let G_h(d,R) be the suffix generating function when the gaps are (d,R) and the last letter is d. Empty suffixes have weight 1. Let

D_h(d,R)=sum_{q=1}^d G_h(q,(d-q,R)),

where a zero gap is omitted. Finally set e_h=E_h(empty) and

N_h=sum_{q=1}^h G_{h+1-q}(q,empty).

All series are in x, which marks appended letters. The shift operator T acts on height by (Tf)_h=f_{h+1}.

For R=(d_1,...,d_k), direct classification of the next letter gives

(1-x)E_h(R)=1+x N_h+x sum_{j=1}^k D_{h+1}(d_j,(d_{j+1},...,d_k)).       (1)

The i=0 transition is the xE_h(R) term; choosing inside an old gap is an ascent from last letter 0, hence h+1; choosing a new maximum gives N_h.

For G, selecting inside the first gap does not make an ascent; selecting inside a later gap does. Subtracting its recurrence from (1) for (d,R) yields

G_h(d,R)=E_h((d,R))+x(1-T)D_h(d,R).                                 (2)

Subtracting (1) for R from the same formula for (d,R) gives

E_h((d,R))=E_h(R)+c T D_h(d,R),  c=x/(1-x).                          (3)

Hence, with A=x+x^2 T/(1-x),

G_h(d,R)=E_h(R)+A D_h(d,R).                                         (4)

## 2. Commuting gap operators

There are scalar formal series in x whose coefficients are polynomials in T, denoted R_d(T), P_d(T), Q_d(T), such that for every tail R,

D_h(d,R)=R_d(T)E_h(R),
E_h((d,R))=P_d(T)E_h(R),
G_h(d,R)=Q_d(T)E_h(R).

They satisfy P_d=1+c T R_d and Q_d=1+A R_d. Induction on the positive integer d proves existence and uniqueness: the definition of D splits into q=d and q<d, and (4) gives

(1-A)R_d=1+sum_{q=1}^{d-1} Q_q P_{d-q}.                             (5)

The inverse (1-A)^(-1) is well-defined x-adically. This induction is valid for arbitrary tail R, so in the q<d terms both the smaller-gap operator identities can be applied. All operators commute because they are functions of the same height shift T. Thus

E_h(d_1,...,d_k)=P_{d_1}(T)...P_{d_k}(T)e_h,
G_h(d,d_1,...,d_k)=Q_d(T)P_{d_1}(T)...P_{d_k}(T)e_h.                 (6)

This proves a precise version of the gap permutation symmetry suggested by small-state comparisons.

## 3. Explicit algebraic jump series

Use an ordinary variable t in place of T and put

Q(x;z,t)=sum_{d>=1}Q_d(t) z^d,
P(x;z,t)=sum_{d>=1}P_d(t) z^d,
R(x;z,t)=sum_{d>=1}R_d(t) z^d.

Let b=1-x and c=x/b, A=x+x^2 t/b. From (5), equivalently R=Q(1+P), and Q=z/(1-z)+AR, P=z/(1-z)+ctR. Eliminating R and P gives

x t(1-z) Q^2 + [b(z-b)+x t(x-z)] Q + b z = 0,                      (7)

with Q(x;0,t)=0 and Q(0;z,t)=z/(1-z). In particular

Q_1(t)=1/(1-x-x^2 t/(1-x)).

Every coefficient [x^n t^r]Q_d(t) is a nonnegative integer, as is clear directly from the recurrence (5). The same holds for P_d,R_d.

The boundary equation (1) at empty R is

e_h = 1/(1-x) + x/(1-x) sum_{q=1}^h (Q_q(T)e)_{h+1-q}, h>=1.       (8)

This is an exact one-dimensional height-walk representation. A macro-step first drops by q-1 (requiring q<=h), then rises by r, has weight x/(1-x) times [t^r]Q_q(t), and ends at h+1-q+r. The terminating weight at every height is 1/(1-x). Starting from the original one-letter prefix 0 gives

A202061(x)=1+x e_1(x).                                             (9)

Equations (7)--(9) have unique x-adic solutions: every nonterminating step has at least one factor x, and for each x degree only finitely many upward shifts occur. They are not being asserted to reduce to a finite algebraic equation for A202061(x).

## 4. Exact diagonal kernel check

Let Delta(x,z,t) be the discriminant of (7) in Q:

Delta=[b(z-b)+xt(x-z)]^2-4xt(1-z)bz.

Its diagonal specialization has polynomial numerator

z^2 Delta(x,z,1/z)
=(z-1)[x^4 z-x^4+2x^3 z^2-2x^3 z+x^2 z^3-7x^2 z^2+2x^2 z-2x z^3+6x z^2+z^3-z^2].

The discriminant in z of this quartic factors exactly as

-256 x^7(x-1)^7(x^3+5x^2-8x+1).

Thus the same cubic governing the established A202062 exponential constant appears naturally in this representation. This algebraic consistency check alone proves no coefficient asymptotic for A202061.

## Sources and status

Conway, Conway, Elvey Price, Guttmann, Pattern-Avoiding Ascent Sequences of Length 3, EJC 29(4) (2022), P4.25: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/ . Their final pp.14--15 credit an O(n^3 log^2 n) enumeration to Shi Lecun, Liang Chengwei, Cai Zhongyu, but supply neither a recurrence nor a separate reference. The new gap-operator reduction above may overlap that unpublished computation; novelty is not established.

OEIS A202061: https://oeis.org/A202061 . The inspected entry still reports no known formula or generating function.

A202062 proof package used for the established exponential constant: ../oeis-a202062-report . It does not prove a stretched correction for A202061.

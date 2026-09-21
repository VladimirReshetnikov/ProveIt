# A289587: proof note (not submitted)

The conjectured generating function is correct.

Let R={(0,1),(0,2),(1,0),(1,2),(2,1)}, the shading denoted by 174. For a
321-avoiding permutation, call adjacent values pi(i),pi(i+1) an upper succession
when pi(i)>i and pi(i+1)=pi(i)+1. An upper run is a maximal consecutive run of
such excedances, including isolated excedances as length-one runs.

**Structural fact.** The occurrences of (12,R) are exactly pairs of fixed
points and pairs within a common upper run. Indeed, the shading forces the
interval between the selected positions to contain exactly the consecutive
value interval between the selected values. The first selected value is at
least its position. Equality gives two fixed points. Strict inequality leaves
a smaller value to the right, so any inversion within the selected interval
would give a 321; the interval must consequently be an increasing consecutive
upper run. The converses follow because excedances are left-to-right maxima
and fixed points split a 321-avoider as a direct sum.

Thus the desired permutations have no upper succession and at most one fixed
point. More generally, their mesh-occurrence statistic is

    choose(fix(pi),2) + sum_U choose(length(U),2).

Let C(x,u) count all 321-avoiders by length and excedances. Its Narayana equation
is C=1+x*C*(1-u+u*C), with C(0,u)=1. Contracting maximal upper runs gives a
unique succession-free core. Each core excedance can be inflated independently
into a nonempty increasing interval. Fixed points are preserved. Therefore,
if B(x,u) counts succession-free cores,

    C(x,u) = B(x,u/(1-x*u)),
    B(x,u) = C(x,u/(1+x*u)).

Write B=B(x,1), and let H count such cores with no fixed point. Fixed points
are precisely singleton direct-sum blocks, so B=H/(1-x*H), or H=B/(1+x*B).
At most one fixed point gives A=H+x*H^2.

Put D=x^4-2*x^3-5*x^2-2*x+1. The Narayana equation now yields

    B = (1+x-x^2-sqrt(D))/(2*x),
    H = (1+3*x+x^2-sqrt(D))/(4*x*(1+x)),
    A = (x^4+4*x^3+11*x^2+10*x+3
         -(x^2+5*x+3)*sqrt(D))/(8*x*(1+x)^2),

where the square root has constant term 1. This is the formula attributed in
the OEIS entry to Thomas Scheuerle, December 23, 2025.

A convenient nonnegative-integer recurrence uses I(0)=0 and

    I = x^2 + (x+x^2)*I + (1+x)*I^2,
    H = 1/(1-I),
    A = H+x*H^2.

This costs O(N^2) integer arithmetic operations for the first N terms. A
signed recurrence costs only O(N). Let T=sqrt(D)=sum t(n)*x^n and
(d0,...,d4)=(1,-2,-5,-2,1). Differentiating T^2=D gives 2*D*T'=D'*T, hence

    t(0) = 1,
    2*n*t(n) = sum_{k=1..min(4,n)} (3*k-2*n)*d(k)*t(n-k)   for n >= 1.

Then, comparing coefficients of x^(n+1) in 8*x*(1+x)^2*A = P-Q*T, and writing
(p0,...,p4)=(3,10,11,4,1) with p(j)=0 for j>4 and negative subscripts read as
zero,

    a(n) = (p(n+1)-3*t(n+1)-5*t(n)-t(n-1))/8 - 2*a(n-1) - a(n-2).

All divisions are exact. (These are arithmetic-operation counts, not bit
complexity; a(n) has Theta(n) bits.)

Also a(n) ~ K*gamma^n*n^(-3/2)*(1+c1/n+O(n^-2)), with

    gamma = (1+2*sqrt(2)+sqrt(5+4*sqrt(2)))/2
          = 3.546455444684995244456761...,
    K  = 0.413931068036970644808821...,
    c1 = -1.008253037811239547502410....

Inversion transposes the shading from 174 to 234, proving the equivalence of
the two versions in the sequence definition. The accompanying article gives
all details, refinements, and the exact expressions for K and c1. Two
independent programs were run: literal mesh tests through n=12 and exact
series checks through degree 200, and a second, separately written checker
with literal mesh tests through n=11 and exact series checks through degree
1000. All four coefficient algorithms agree at every index through 1000.
Nothing here has been submitted to OEIS.

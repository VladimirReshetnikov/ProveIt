# Last rank-four gap with a fifth head-only vertex

## Theorem

Let A consist of four vertices with positive tail activities, and let h be a fifth physical core vertex with zero tail activity. The directed relation on A union {h} is arbitrary and loopless. Adjoin any finite independent cloud W of universal sinks, with arbitrary nonnegative sink-head activities. All core-head activities are arbitrary and independent. Then

    gamma_3^2 >= (8/3) gamma_2 gamma_4.

The head role of h is retained. The proof works on the entire four-tail face, with no assumption that gamma_4 is positive. By continuity it includes further zero tails.

## Reciprocal-tail decomposition

Let p=product_{i in A} u_i and x_i=1/u_i. Write t=v_h and E_k=e_k(w), including E_0=1. If h has no incoming arc from A, its head activity contributes nothing; set t=0. Otherwise its active in-neighborhood N is nonempty, and put

    Z=E_4+t E_3.

For each i in A define Boolean indicators

    alpha_i = 1 if A\{i} can cover the head h,
    beta_i  = 1 if A\{i} can cover the head i,
    delta_i = 1 if A\{i} can cover the two heads {h,i}.

"Cover" means that a matching has distinct sources in the indicated tail set and one target at every indicated head. Put

    A_i=E_3+(t alpha_i+v_i beta_i)E_2+t v_i delta_i E_1.

For distinct i,j, use tail set S=A\{i,j} and define a,b,c,d,e,f as its Boolean abilities to cover respectively

    {h}, {i}, {j}, {h,i}, {h,j}, {i,j}.

Then put

    B_ij=E_2+(t a+v_i b+v_j c)E_1
         +t v_i d+t v_j e+v_i v_j f.

Partitioning supports by their omitted active tails gives exactly

    gamma_4=pZ,
    gamma_3=p sum_i x_i A_i,
    gamma_2=p sum_{i<j} x_i x_j B_ij.

Each endpoint support is counted once, regardless of matching witnesses. A matching covering the indicated core heads extends to any selected universal sink heads, which proves the formulas.

## Local pair inequality

For every i != j,

    A_i A_j >= Z B_ij.

Here is an ordinary proof. Assume t is an actual active extra-head variable, so N is nonempty. The basic Boolean implications are

    alpha_i+alpha_j >= 1+a,
    alpha_i alpha_j >= a,
    beta_i >= b, beta_j >= c,
    delta_i >= d, beta_i alpha_j >= d,
    delta_i+beta_i alpha_j >= b,
    delta_j >= e, beta_j alpha_i >= e,
    delta_j+beta_j alpha_i >= c,
    beta_i beta_j >= f,
    delta_i alpha_j >= d, delta_j alpha_i >= e,
    delta_i beta_j+delta_j beta_i >= f.

All but two assertions follow immediately by retaining a witness when enlarging its tail set. For delta_i+beta_i alpha_j >= b, take a source r in S for i. If alpha_j=1, the beta_i alpha_j term suffices. Otherwise N must be {j}, and j->h together with r->i proves delta_i=1. The symmetric assertion follows identically.

For the final assertion, suppose f=1 and take distinct r,s in S with r->i and s->j. Then beta_i=beta_j=1. Take any z in N. If z=i, the arcs i->h and s->j prove delta_j=1. If z=j, use j->h and r->i to prove delta_i=1. If z is in S, then z differs from at least one of r,s: use z->h together with that other's incoming arc to prove the corresponding delta. Thus at least one delta is one.

The coefficients of A_i A_j-ZB_ij as a polynomial in t,v_i,v_j are:

    1:       E_3^2-E_2 E_4
    t:       (alpha_i+alpha_j-1)E_2 E_3-a E_1 E_4
    v_i:     beta_i E_2 E_3-b E_1 E_4
    v_j:     beta_j E_2 E_3-c E_1 E_4
    t^2:     alpha_i alpha_j E_2^2-a E_1 E_3
    t v_i:   delta_i E_1 E_3+beta_i alpha_j E_2^2-b E_1 E_3-d E_4
    t v_j:   delta_j E_1 E_3+beta_j alpha_i E_2^2-c E_1 E_3-e E_4
    v_i v_j: beta_i beta_j E_2^2-f E_4
    t^2 v_i: delta_i alpha_j E_1 E_2-d E_3
    t^2 v_j: delta_j alpha_i E_1 E_2-e E_3
    t v_i v_j: (delta_i beta_j+delta_j beta_i)E_1 E_2-f E_3
    t^2 v_i v_j: delta_i delta_j E_1^2.

Every displayed coefficient is nonnegative. Use the implications above together with

    E_3^2>=E_2E_4, E_2E_3>=E_1E_4,
    E_2^2>=E_1E_3, E_2^2>=E_4, E_1E_2>=E_3.

These are the elementary-symmetric log-concavity comparisons (with weaker-than-Newton constants); the final two also follow by direct positive expansion. They hold for every finite nonnegative sink vector, including vanishing coefficients. For t v_i, if d=1 then both delta_i and beta_i alpha_j equal one, so the coefficient is at least E_2^2-E_4. If d=0 and b=1, their sum is at least one and E_2^2>=E_1E_3 suffices. If b=d=0 it is immediate. The t v_j case is symmetric. This completes the local proof.

## Four-variable completion

Let y_i=x_i A_i. The local pair inequality gives

    gamma_2 gamma_4 / p^2
      =sum_{i<j}x_i x_j B_ij Z
      <=sum_{i<j}y_i y_j.

Cauchy's inequality in four nonnegative variables gives

    (sum_i y_i)^2 >= (8/3) sum_{i<j}y_i y_j.

Combining with gamma_3/p=sum_i y_i proves the theorem. Explicitly, the complete nonnegative identity is

    3 gamma_3^2-8 gamma_2 gamma_4
      =p^2 sum_{i<j}(y_i-y_j)^2
       +8p^2 sum_{i<j}x_i x_j (A_i A_j-ZB_ij).

Multiplication by p^2 removes every reciprocal denominator; equivalently extend the already proved positive-tail inequality by continuity. No physical vertex is deleted from its head role.

## Exact audit

The script check_pair.py independently verifies all Boolean implications for the 960 arc patterns having nonempty N, among the 1024 patterns on the ten relevant arcs from A into {h,i,j}. The displayed proof does not depend on this finite audit. Arcs out of h have zero tail weight, and arcs into the other two active vertices cannot appear in the indicated ranks with fixed omitted tails, so there are no omitted relevant edges.

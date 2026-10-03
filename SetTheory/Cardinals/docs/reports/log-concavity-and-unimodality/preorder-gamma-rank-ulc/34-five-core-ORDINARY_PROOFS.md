# Five-core universal-sink structural reduction

## Scope and result

Let C have five vertices, H be any loopless directed relation on C, and W be a finite independent set of universal sinks: every arc C→W is present and no other exterior arcs occur. Tail activities u_i, core-head activities v_i, and sink-head activities w_x are independent and nonnegative. A feasible ordered pair of disjoint endpoint sets is counted once, irrespective of matching witnesses.

The following **ordinary, computer-independent theorem** is proved below:

> γ₃² ≥ 2 γ₂ γ₄ for every such H and every nonnegative activity assignment.

It supplies the second middle rank-ULC comparison when the actual degree is five. It is not by itself the comparison required when the actual degree drops to four.

The first middle comparison γ₂²≥2γ₁γ₃ is exactly equivalent, after closure over all finite sink counts, to a nonnegative polynomial in twelve nonnegative variables (ten core activities and two sink parameters). The reduction is explicit below. No claim that this reduced polynomial is always nonnegative is made by this note.

## 1. Boolean support formulas

For k,r≥0 let

F_{kr} = sum u_S v_J,

where the sum ranges over disjoint S,J⊆C with |S|=k, |J|=r and H[S,J] admitting an injection covering J. This is a Boolean feasibility test. Put

a=F₁₁, b=F₂₂, c=F₂₁, d=F₃₁, f=F₃₂, g=F₄₁,

e_j=e_j((u_i)_{i∈C}), E_j=e_j((w_x)_{x∈W}).

Then exactly

γ₀=1,
γ₁=a+e₁E₁,
γ₂=b+cE₁+e₂E₂,
γ₃=fE₁+dE₂+e₃E₃,
γ₄=gE₃+e₄E₄,
γ₅=e₅E₅.

Proof: a rank-k support has k core tails and r core heads, so k+r≤5; the remaining k−r heads are sinks. Any injection onto the selected core heads extends to the selected universal sink heads. This partitions supports without counting witnesses.

More explicitly, for core head j with nonempty in-neighborhood N_j,

g_j=u_{C\{j}},
d_j=sum_{S⊆C\{j}, |S|=3, S∩N_j≠∅}u_S,
c_j=sum_{S⊆C\{j}, |S|=2, S∩N_j≠∅}u_S,

and g=Σv_jg_j, d=Σv_jd_j, c=Σv_jc_j. These polynomials are zero if N_j is empty. For a core head pair J, write b_J for its Boolean feasible two-tail polynomial and f_J for its Boolean feasible three-tail polynomial. Then b=Σ_Jv_Jb_J and f=Σ_Jv_Jf_J. Since C\J has three vertices, f_J is either zero or u_{C\J}; it is nonzero exactly when b_J is nonzero.

## 2. Sharp two-parameter reduction for the first middle gap

Write p_j=Σ_x w_x^j and set A=√p₂, B=p₁−√p₂. Then A,B≥0 and

E₁=A+B,
E₂=AB+B²/2,
E₃≤AB²/2+B³/6.

Indeed, p₃≤p₂^(3/2), because each w_x≤√p₂; substitute in 6E₃=p₁³−3p₁p₂+2p₃. The first two identities are exact.

For any fixed λ≥0, γ₂²−λγ₁γ₃ is nonincreasing in E₃ with E₁,E₂ and core activities fixed. Thus it suffices to substitute the displayed upper boundary for E₃. This is sharp after closure: one sink of activity A and n sinks each of activity B/n tend to that boundary as n→∞.

Define integer polynomials

G₁=a+e₁(A+B),
G₂=2b+2c(A+B)+e₂(2AB+B²),
G₃=6f(A+B)+3d(2AB+B²)+e₃(3AB²+B³).

At the boundary, G₁=γ₁, G₂=2γ₂, G₃=6γ₃. Therefore

Q_H=3G₂²−4G₁G₃

is twelve times the boundary gap γ₂²−2γ₁γ₃. Its nonnegativity on the closed nonnegative orthant is necessary and sufficient for γ₂²≥2γ₁γ₃ for every finite sink cloud for the fixed core H.

## 3. Three ordinary core comparisons

We prove, coefficientwise in the core activities,

(I) 3fd≥bg,
(II) 4fe₃+3d²≥be₄+4cg,
(III) 2de₃≥2e₂g+ce₄.

The separate exhaustive exact audit actually finds the stronger fd≥bg, but that strengthening is not needed and is not a dependency of the ordinary proof.

### 3.1. Proof of (I)

Compare one head monomial at a time.

If it has the repeated-head form v_j²v_k, its coefficient on the right is b_{jk}g_j. For any feasible two-tail set B⊆C\{j,k}, the triple B∪{k} is feasible for head j. Hence f_{jk}d_j contains b_{jk}g_j coefficientwise.

For a three-distinct-head monomial v_jv_kv_l, every tail monomial in bg has coefficient at most three: for each choice of the single head l belonging to g, its four-tail factor is fixed and the two-tail factor is then uniquely determined. We show that every such monomial occurs in fd at least once. This proves domination after multiplying fd by three.

Fix a contributing b_{jk}g_l and a witnessing two-tail matching onto j,k. Write C={j,k,l,a,b}.

* If its two-tail set is {a,b}, choose any incoming arc r→l. If r∈{a,b}, pair l with the original head whose matching source is the other tail. If r∈{j,k}, pair l with the other original head. In either case this pair has a feasible three-tail complement, and the remaining head has a feasible three-tail set obtained by dividing the target monomial by that complement. The original matching supplies its incoming arc.
* Otherwise the two-tail set is {l,a}, after interchanging a,b if needed. Relabel j,k so the matching is l→j and a→k. If l has an in-neighbor in {j,k,a}, use f_{jk} and d_l. If not, its nonempty in-neighborhood must contain b; use f_{kl}, witnessed by a→k,b→l, and d_j, witnessed by l→j.

All constructed tail triples avoid their selected heads, and their products are exactly the original tail monomial. Thus (I) holds coefficientwise.

### 3.2. Elementary three-variable facts

For three variables z_a,z_b,z_c set t=e₁(z), s=e₂(z), p=e₃(z). For U⊆{a,b,c}, put

L_U=Σ_{i∈U}z_i,
B_U=Σ_{|S|=2, S∩U≠∅}z_S.

For nonempty U, coefficientwise

sB_U≥p(t+L_U).

If U is a singleton {a}, expansion gives equality on every p-multiple and extra square terms; if |U|≥2, B_U=s and s²≥2pt≥p(t+L_U).

For any U,V,

B_UB_V≥2pL_{U∩V}.

For every i∈U∩V, multiplying the two distinct pairs containing i in the two orders supplies 2pz_i; these monomials are different for different i.

Let b(U,V) be the sum of z_iz_j over unordered distinct pairs that can cover the two neighborhoods U,V. Then

B_UB_V≥b(U,V)s.

If both sets have size at least two, B_U=B_V=s and b(U,V)≤s. If one is a singleton, the claim is immediate when the other has size at least two. For two distinct singletons {a},{b}, it is
z_a(z_b+z_c)z_b(z_a+z_c)=z_az_b(s+z_c²)≥z_az_bs.
For equal singletons, b(U,V)=0.

### 3.3. Proof of (II): squared-head terms

The coefficient of v_j² is 3d_j²−4c_jg_j. In fact d_j²≥2c_jg_j coefficientwise.

If j has at least two in-neighbors among its four permitted tails, d_j=e₃(z), c_j≤e₂(z), g_j=e₄(z), and e₃(z)²≥2e₂(z)e₄(z) coefficientwise. If it has just one in-neighbor of activity a, write t,s,p for the elementary symmetric polynomials in the other three tail activities. Then c_j=at,d_j=as,g_j=ap, and s²≥2tp. The empty-neighborhood case is zero. This proves the squared-head comparison.

### 3.4. Proof of (II): two distinct heads

Fix heads j,k. Let A=C\{j,k}, x=u_j,y=u_k and t,s,p be the elementary polynomials on A. Let P,Q⊆A be their in-neighbor sets from A. Let δ_j indicate k→j and δ_k indicate j→k. Put

U=P if δ_j=0, and U=A if δ_j=1;
V=Q if δ_k=0, and V=A if δ_k=1.

Set ε_P=1(P≠∅), ε_Q=1(Q≠∅), η_P=1(U≠∅), η_Q=1(V≠∅). Let ε indicate that P,Q admit distinct representatives. Write b=b(P,Q), so the coefficient f_{jk}=εp. Then

c_j=B_P+yL_U, d_j=ε_Pp+yB_U, g_j=η_Pyp,
c_k=B_Q+xL_V, d_k=ε_Qp+xB_V, g_k=η_Qxp,
e₃=p+(x+y)s+xyt, e₄=(x+y)p+xys.

The desired head-pair coefficient is
R=4εpe₃+6d_jd_k−be₄−4(c_jg_k+c_kg_j).

Its constant term is p²(4ε+6ε_Pε_Q), nonnegative.

Its x coefficient, divided by p, is
4εs+6ε_PB_V−b−4η_QB_P.
If ε=1, use B_P≤s and b≤B_V. If ε=0, then b=0. The expression is zero unless ε_P=η_Q=1; in that case either δ_k=1, giving B_V=s≥B_P, or P=Q is a common singleton, giving B_V=B_P. So it is nonnegative. The y coefficient is symmetric.

The xy coefficient is
4εpt+6B_UB_V−bs−4p(η_QL_U+η_PL_V).
If η_Pη_Q=0 it is zero. Otherwise both η's are one.

If ε=0 and at least one δ is one, suppose U=A. The expression is 6sB_V−4p(t+L_V), nonnegative by §3.2. If ε=0 and both δ's are zero, the nonempty sets P,Q must be the same singleton; §3.2 gives B_U²≥2pL_U, again sufficient.

Finally, if ε=1, §3.2 gives B_UB_V≥bs (because b(P,Q)≤b(U,V)), and B_UB_V≥2pL_{U∩V}. As
L_U+L_V−t≤L_{U∩V},
we get
6B_UB_V−bs+4p(t−L_U−L_V)
≥5B_UB_V−4pL_{U∩V}≥0.

Every coefficient of R is therefore nonnegative. This completes the ordinary proof of (II).

### 3.5. Proof of (III)

Fix a head j and set x=u_j, with z the other four tail activities. Write e_r(z) as z_r. The constant and x coefficients of
2d_j e₃(u)−2e₂(u)g_j−c_j e₄(u)
are respectively

Q₀=2d_jz₃−(2z₂+c_j)g_j,
Q₁=2d_jz₂−2z₁g_j−c_jz₃.

For a neighborhood of size at least two, d_j=z₃ and c_j≤z₂. The coefficientwise identities z₃²≥2z₂z₄ and z₂z₃≥3z₁z₄ imply Q₀,Q₁≥0.

For a singleton neighborhood of activity a, write t,s,p for the other three activities. Then

Q₀=a²(2s²−3tp),
Q₁=a²(st−2p)+a(2s²−3tp),

both coefficientwise nonnegative because s²≥2tp and st≥3p. The empty-neighborhood case is zero. Summing over heads proves (III).

## 4. Ordinary proof of γ₃²≥2γ₂γ₄

Classical elementary-symmetric inequalities for every finite nonnegative sink vector give

E₁E₂≥3E₃,
E₂²≥(3/2)E₁E₃,
E₁E₃≥4E₄,
E₂E₃≥2E₁E₄,
E₃²≥(4/3)E₂E₄.

These follow from binomial-normalized Newton inequalities after discarding the extra finite-count factors; cases with vanishing relevant coefficients are immediate. For five tail variables Newton gives e₃²≥2e₂e₄.

Expand

γ₃²=f²E₁²+2fdE₁E₂+(2fe₃E₁E₃+d²E₂²)+2de₃E₂E₃+e₃²E₃².

Use (I) for the second term:
2fdE₁E₂≥6fdE₃≥2bgE₃.

Use (II) for the parenthesized pair:
2fe₃E₁E₃+d²E₂²
≥(2fe₃+(3/2)d²)E₁E₃
≥((1/2)be₄+2cg)E₁E₃
≥2be₄E₄+2cgE₁E₃.

Use (III) for the next term:
2de₃E₂E₃≥2e₂gE₂E₃+ce₄E₂E₃
≥2e₂gE₂E₃+2ce₄E₁E₄.

Finally
 e₃²E₃²≥(8/3)e₂e₄E₂E₄≥2e₂e₄E₂E₄.

Adding and discarding f²E₁² gives exactly

γ₃²≥2(b+cE₁+e₂E₂)(gE₃+e₄E₄)=2γ₂γ₄.

Everything holds directly on the closed nonnegative orthant. The proof does not use an assumption that γ₅ is positive, although its coefficient 2 is the correct rank-ULC middle constant only at rank five.

## 5. Other rank-five comparisons and degree-drop caution

The known actual-degree first-coefficient argument gives 4γ₁²≥10γ₂ at actual degree five. The ordinary general universal-sink last-gap theorem gives γ₄²≥(25/8)γ₃γ₅, stronger than the rank-five requirement γ₄²≥(5/2)γ₃γ₅. Thus at full rank five, only γ₂²≥2γ₁γ₃ remains outside the ordinary results in this note.

A proof at actual degree five does not establish all lower actual degrees. Rank four needs γ₂²≥(9/4)γ₁γ₃ and γ₃²≥(8/3)γ₂γ₄; rank three needs γ₂²≥3γ₁γ₃. A zero tail activity does not delete that physical vertex's possible head role, so the earlier four-core theorem cannot be applied automatically. Five positive core tails with at most four positive sinks can also have actual degree four.

## 6. Exact audit and limits of stronger packages

The directory core-comparisons contains exact coefficient audits based on the Boolean subset definition, not a numerical activity search. They corroborate (I)–(III) and strengthen (I) to fd≥bg. Only arcs into a selected head-exponent support matter, requiring at most 12 arc bits. The proofs above do not depend on these scripts.

A direct attempt to replace 2 by 8/3 via stronger analogues of (II),(III) fails:

* H={1→0}, u=(0,t,1,1,1), v=(1,0,0,0,0) gives 3de₃−4e₂g−2ce₄=−3t+9t²<0 for 0<t<1/3.
* H={2→0,3→1}, u=(0,1,t,1,1), v=(1,1,0,0,0) gives 12fe₃+9d²−16cg−4be₄=−4t+112t²<0 for 0<t<1/28.

These refute only that proposed proof package, not the stronger total coefficient inequality on a rank-four face.

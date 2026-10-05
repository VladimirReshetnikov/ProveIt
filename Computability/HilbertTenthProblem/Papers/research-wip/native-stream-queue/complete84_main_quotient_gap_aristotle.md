# The missing main-quotient gap exceeds the paid input root

On every full positive zero in the canonical branch of the unchanged independent-gamma83 source,

    psi_A(R-1) < gamma-rho < gamma < 2*psi_A(R-1).       (1)

In particular `gamma-rho>mu>kappa>delta`, `gamma-rho>rho`, and `gamma-rho>w`. In the noncanonical branch `gamma-rho<0`. Thus identifying the missing positive gap with any one of the five existing values `mu,kappa,delta,rho,w` gives no positive zero on any inherited valid compiler slice. This concerns the gap **gamma-rho**, not the already excluded direct identification of gamma itself with a donor.

The bound also gives a valid weighted-split chart `gamma=2*rho+sigma_new` for the complete84 parent, with an honest **85=47M+38A** schedule. There is no gate saving, no new global lower bound, and no resolution of the independent-gamma83 language.

## 1. Actual source and inherited premises

The source is `complete83_independent_gamma_scout.json`, SHA256 `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20`. It deletes only `gamma_sum=rho+sigma` from complete84 and uses its supplied positive `sigma` as independent gamma in `gam=sigma*a4m5`. Every other source row and the full finalizer remain literal. Its original ordinary input, positive-coordinate domain and six fixed compiler numerals are retained, including the shifted MF convention. The exact all-ring relation is

    F83(gamma)=F84(sigma_old=gamma-rho).                 (2)

Use mathematical Pell parameter A=a+2 and discriminant Delta=A^2-1. The literal source register named `A` contains Delta, not this Pell parameter. Define

    X=w*q, Y=s*q^3, a=Y*(X+1), H=4a+3=4A-5,
    c=psi_A(R), D=chi_A(R),
    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.

Here `c=R10a`, `D=R14`, `kappa=index_rhs`, `mu=exponent_rhs`, `H=a4m5`, and `R=r_lhs`. All five candidate donors listed above are already supplied or computed; there is no free new operation implicit in naming them.

The full-zero native bootstrap and exact dichotomy are inherited from `complete83_input_quotient_dichotomy.md`, Sections2–5. They were proved without assuming gamma>rho or an accepted ordinary input. Their relevant conclusions are

    A>X=2^R>w>0, R>=49, R and u odd, 3<=u<R,
    H>0, Delta>1, c_j=psi_A(j), D_j=chi_A(j),
    E_j=D_j-(A-2)*c_j=2*c_j-c_(j-1) for j>=1,
    gamma*H=E_R-X,
    kappa=c_v>0, mu=D_v>0, rho*H=E_v-W.

Exactly one of these branches holds at every full positive83 zero:

* Canonical: v=u, W=2^u, and 0<rho<gamma<c. The inverse (2) is positive and restores a complete84 zero at the same input.
* Noncanonical: rho>c>gamma, hence gamma-rho<0. This branch includes known same-input completions above every positive parent zero; it is not equated with false inputs.

No part of this note reproves the native bootstrap or assumes every modular Pell index occurs. The new comparison below starts from these authenticated all-zero facts.

## 2. A sharp Pell-scale interval for the gap

Put b1=c_(R-1) and b2=c_(R-2); these names are unrelated to the fixed cell-bit numeral b. The Pell recurrence gives

    E_R=(4A-1)*b1-2*b2,
    E_R-H*b1=4*b1-2*b2.                              (3)

Consider the canonical branch. Since R and u are odd and u<R, u<=R-2. The E sequence is strictly increasing, and

    E_u<=E_(R-2)=2*b2-c_(R-3)<2*b2.

Write S=gamma-rho only as a proof abbreviation. Its two projection identities yield

    H*(S-b1)=4*b1-2*b2-E_u-X+W
             >4*(b1-b2)-X+W.                         (4)

The positive Pell coefficients are strictly increasing. Thus their recurrence implies b1>(2A-1)*b2>2*b2, because A>=3. Also b1>=c_2=2A since R>=3. Therefore

    4*(b1-b2)>2*b1>=4A>X,

and W=2^u>0 makes (4) strictly positive. Consequently S>b1.

Positivity of rho gives S<gamma. Finally (3) gives the upper bound directly:

    2*H*b1-(E_R-X)=(4A-9)*b1+2*b2+X>0.

Hence gamma<2*b1. These are exactly the strict inequalities (1). In particular S>gamma/2 and rho=gamma-S<gamma/2<S. No approximation or limiting argument enters this proof.

## 3. The five donor exclusions and their exact scope

The addition law supplies `c_(j+1)=A*c_j+D_j>D_j`. Since u<=R-2,

    mu=D_u<=D_(R-2)<c_(R-1)<S.                       (5)

The norm equation and Delta>1 imply mu>kappa, while `kappa=u+Delta*delta` implies kappa>delta. Also mu>=D_1=A>X>w. Together with Section2 this proves

    S>mu>kappa>delta>0,  S>rho>0,  S>w>0              (6)

in the canonical branch. In the noncanonical branch S<0 while mu,kappa,delta,rho,w are all strictly positive by the inherited source conclusions. Thus, on **all** full positive83 zeros, none of the equalities

    gamma-rho=mu, kappa, delta, rho, or w               (7)

can hold.

This is a semantic obstruction to those exact identifications, even if another rearrangement made their arithmetic free. It is not a census of all donors or a theorem about arbitrary functions of them. In particular it does not rule out a genuinely different chart with additional free coordinates or altered norm producers.

The signed-w theorem supplies a useful domain check for the last equality. In the positive independent-gamma83 source, allowing only w to be signed still forces w>0 by the same proof: cP>0 and gamma>0 give D<a*cP<0 when w<=-1, while w=0 makes H divide the main norm. Delta is positive in both signed branches. Consequently replacing w by gamma-rho and keeping gamma,rho and all other coordinates positive cannot escape (7) through a negative restored w. Such a child zero would first have w>0, then map to a positive independent-gamma83 zero satisfying the impossible equality S=w. This applies the new signed-domain fact to this concrete coupled chart; it does not assume soundness of independent-gamma83.

## 4. A valid weighted split, with its paid cost

At every parent84 positive zero, sigma_old=S and Section2 gives sigma_old>rho. Therefore

    sigma_new=sigma_old-rho>0,
    gamma=rho+sigma_old=2*rho+sigma_new.                (8)

Conversely every positive zero of the polynomial obtained by the substitution `sigma_old=rho+sigma_new` restores positive sigma_old immediately. Equations(8) give mutually inverse maps on the entire positive zero sets, preserving all other supplied coordinates and the ordinary input. This uses the canonical theorem only in the parent-to-child direction; the reverse is the exact substitution followed by positivity.

A fully charged literal implementation replaces the old addition `gamma_sum=rho+sigma_old` by

    doubled_rho=rho+rho,
    gamma_sum=doubled_rho+sigma_new.

Every other row is unchanged. There is one additional addition, so the result costs85=47M+38A, still with eighteen positive witnesses. The inverse affine change preserves exact degree187 on each fixed compiler slice. This is a proof and a literal two-row schedule, not a newly emitted or executed source packet.

**Review remark 1 (two unsuccessful shortcuts).** The proposed shortcuts “padding makes the independent gamma split automatically positive” and “use the existing w or input-root value as its positive gap” do not supply a saving. The first is already refuted by the frozen same-input Pell-period family: above every genuine parent zero, holding the compiler and outer data fixed and increasing the compatible input Pell index gives rho>gamma. Every valid padded compiler with a nonempty represented language still has such a parent zero. This is an inherited obstruction, not a new result here. The second is refuted on all full positive zeros by (7), with the signed-w point addressed in Section3. These failures leave unrelated transformations and the unresolved83 ordinary-input language open.

## 5. Pins and limits

All dependencies are in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:

| File | SHA256 | Read/use scope |
|---|---|---|
| `complete83_independent_gamma_scout.md` | `bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41` | Full proof, especially all-zero pretyping and same-input counterfamily |
| `complete83_input_quotient_dichotomy.md` | `46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505` | Full mathematical theorem/Sections1–5; all-zero domain inherited |
| `complete83_direct_gamma_witness_obstruction.md` | `c1f7a146ba85020ea1ed436e64de9a9163f9c5c7ac8d013d46d719ccef92d3f4` | Full; distinguish old gamma-donor exclusions from the new gap comparison |
| `complete83_computed_gamma_obstruction.md` | `02b55f39ea585c76563897fcb0040f75d4257c410ffc3c27d5f3686822632d04` | Lines1–150; same novelty check, no new catalogue certification |
| `complete84_signed_w_charts_aristotle.md` | `ead1d6a5847fcaa7ce9a1f5c2408dd5716e126014225d145bdcdd0c7716176b5` | Full; signed-w norm argument and earlier chart counts |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` | Literal definitions and original47M+37A ledger |

The independent83 source pin is stated in Section1. Static source rows were read to bind gamma, the two input roots and the unchanged output. No archived, supplied, frozen or predecessor helper or source array was executed or imported; no full tuple was materialized. Only new metadata-only byte/JSON reads were used. The companion receipt binds hashes and declared spans, not a machine-checked proof. No repository or Git mutation was made. The established universal84 frontier is unchanged.

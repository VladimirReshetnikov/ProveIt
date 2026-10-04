# A uniform 54th-power gap between the two input-witness ranges

Every full positive zero of the unchanged independent-gamma83 source, on its inherited valid fixed-program compiler slice, lies in exactly one of these ranges:

    canonical:     0 < delta < c/Delta,  0 < rho < gamma < c;
    noncanonical:  delta > c^(L-1),     rho > c^(L-1),
                   L=floor(A*u/R) >= 55.

Here A=a+2 is the Pell parameter, Delta=A²−1 is the source register `A`, u=2d*x+b, and c=psi_A(R). The positive supplied witness delta is distinct from Delta. In particular, both input witnesses exceed **c^54** in the noncanonical range. On the full zero set, either condition delta<=c^54 or rho<=c^54 therefore implies a positive literal parent84 inverse at the same ordinary input.

This strengthens the [quotient dichotomy](complete83_input_quotient_dichotomy.md) by a quantified bound on **both** input witnesses. It does not resolve the input language: known noncanonical completions at accepted, unchanged inputs already occupy this large range. The power with the variable exponent L is an external mathematical bound, not an unpaid arithmetic operation or a new circuit. The source remains 83=47M+36A, eighteen positive witnesses, exact degree187; the universal84 bound is unchanged.

## 1. Exact source and inherited full-zero premises

The [fresh helper](complete83_input_witness_power_gap.py) and [receipt](complete83_input_witness_power_gap.json) authenticate six files, including the full quotient-dichotomy trio, the independent83 JSON/proof and current84 JSON. Their exact hashes are retained in both helper and receipt. Immediate proof/source pins are:

| File | SHA-256 |
|---|---|
| `complete83_input_quotient_dichotomy.md` | `46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505` |
| `complete83_independent_gamma_scout.json` | `ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |

The complete literal84→83 deletion is reconstructed from inert JSON. Twenty exact boundary rows identify the native parameter, discriminant, main quotient, input index and input root. All83 rows and25 free ports remain live; no source is changed or re-emitted.

The pinned dichotomy's native bootstrap applies to every full positive child zero before ordinary-input decoding. It cancels the positive Delta through the all-ring scaled identity, proves the normalized norm signs and main rank, and recovers the native half-binomial curve with X=2^R. We use only its following consequences:

    R>=7, A>2^R, q<A, 3<=u<R<A,
    Delta=A²−1, H=4A−5, |W|<q,
    c=psi_A(R), D=chi_A(R),
    kappa=psi_A(v)=u+delta*Delta,
    E_v=chi_A(v)-(A−2)psi_A(v)=W+rho*H.

The integers A,u have opposite parity: A is even and u is odd. The input index is positive. Its two exact discriminant progressions are

    odd v:  v=u+2Delta*j,  j>=0;
    even v: v=A*u+2Delta*j, j>=0.

The canonical case is exactly v=u, and then rho<gamma<c and the literal inverse sigma_parent=gamma−rho is positive. Every other case has rho>c>gamma. These inherited assertions concern full zeros, not freely assigned Pell components, and require no assumption that a noncanonical marker has already decoded a computation.

## 2. A parameter-independent lower exponent

Since u<A, we have A*u<2Delta. Thus every noncanonical odd index satisfies v>=u+2Delta>A*u, while every even index satisfies v>=A*u directly. Put

    L=floor(A*u/R).

Then v>=L*R. Because u>=3 and integer A>2^R,

    L>=floor(3*(2^R+1)/R)>=55.

For the second inequality, the function (2^R+1)/R increases at integer R>=2: its consecutive difference has positive numerator (R−1)2^R−1. At R=7 the displayed lower floor is floor(387/7)=55. The actual compiler supplies stronger lower bounds on R; this argument deliberately uses only R>=7 and hence a uniform constant.

The native coefficient is larger than every denominator and error term needed below. Monotonicity and R>=3 give

    c>=psi_A(3)=4A²−1>Delta,
    c>H+q,  c>u.

Indeed q<A implies H+q<5A−5, and 4A²−1>5A−5 for A>=2. In particular c is an integer greater than1.

## 3. Both supplied witnesses cross the power gap

Write c_j=psi_A(j), D_j=chi_A(j). Positive Pell addition gives

    c_(j+k)=c_j*D_k+c_k*D_j,
    D_j>c_j>0  for j>=1.

Induction therefore gives c_(L*R)>c^L for every integer L>=2. Since v>=L*R, monotonicity implies c_v>c^L. Consequently

    delta=(c_v−u)/Delta > (c^L−u)/Delta > c^(L−1).

For the last inequality, (c−Delta)c^(L−1)>u follows from the integer inequality c−Delta>=1 and c>u, with L−1>=1.

For the other witness, the exact Pell identity is

    E_v=2c_v−c_(v−1)>c_v.

The retained marker bound |W|<q now gives

    rho=(E_v−W)/H > (c^L−q)/H > c^(L−1).

Here (c−H)c^(L−1)>q follows from c>H+q. These inequalities do not need W positive, an ordinary-power marker, an order bound, or an assumption about the input Pell index's parity beyond the two already proved progressions.

In the canonical case v=u<R, strict Pell monotonicity gives

    delta=(c_u−u)/Delta < c/Delta.

Together with the inherited 0<rho<gamma<c this proves the complete two-range theorem. Since L>=55, a full zero with either input witness at most c^54 must be canonical; the already proved positive parent inverse then certifies acceptance of its ordinary input.

## 4. What remains unresolved

The native multiplicative-order criterion still determines whether a noncanonical completion exists above a particular outer tuple. For a fixed genuine parent history its alias spacing is

    m_alias=gcd(2Delta,ord_H(2))
            /gcd(gcd(2Delta,ord_H(2)),2d),

with the original positive-alpha interval retained. The new exponent L is unrelated to the name m_alias and is not a bound on that period. The theorem supplies no control of the remaining prime factors of m_alias and no authentic rejected-input history.

In particular, a large input witness alone is not evidence of a false input: the pinned independent83 CRT argument supplies arbitrarily large compatible v at every genuine parent input, hence actual same-input zeros in the large range. The new gap is a necessary condition for any false input and a sufficient condition for sound restoration below the gap. It is not a new sufficiency condition for language failure, and neither witness bound is enforced by the83 polynomial.

## 5. Fresh bounded evidence

The standalone standard-library checker imports no author or predecessor module and executes no historical builder. It authenticates the complete unchanged source and the twenty boundary rows. Twelve relaxed Pell parameter models use R=7 or11 and even A>2^R; these are **not** native half-binomial histories or compiler zeros. Independent binary Pell multiplication checks the exact triple-angle identities, the canonical integral input components, the block-growth inequality and the large-index bounds. Thirty-six delta numerator comparisons and108 rho numerator comparisons cover three large indices and negative, zero and positive bounded W. These latter comparisons deliberately do not assert H-integrality; they test the inequalities at a larger domain than the full-zero theorem.

Seventy-four finite floor checks corroborate the uniform55 lower bound. The proof of monotonicity, rather than these samples, supplies its unrestricted range. Large component integers are saved by bit length and exact hexadecimal digest. No full compiler tuple, huge native modulus, multiplicative-order factorization, or giant history is materialized.

The receipt includes the helper's source hash and the complete83 packet hash. Checks use explicit exceptions, duplicate/nonfinite JSON rejection, and canonical type-sensitive comparison under normal and optimized Python. Use `--root ABS_WIP --output FILE` for generation and `--root ABS_WIP --expect FILE` for replay. Fresh generation and fresh normal and `-O` exact receipt replays from `/` all passed.

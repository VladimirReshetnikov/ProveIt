"""Generate exact formulas, rational enclosures, and verification receipts.

Run from any directory: python code/verify.py
Outputs are written under the package's results/ directory.  No network is
used.  The polynomial proofs and the numerical enclosures have distinct roles.
"""

import argparse
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as Q
import json
from pathlib import Path
import platform
import sys
import time

import sympy as s
import holder as h
import identities as ids

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def decimal_upper(q, digits=8):
    assert q >= 0
    with localcontext() as context:
        context.prec = digits
        context.rounding = ROUND_CEILING
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def decimal_value(q, digits=65):
    with localcontext() as context:
        context.prec = digits
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def eval_polynomial(expression, atoms):
    answer = h.interval(0)
    for term in ids.polynomial_terms(expression):
        value = h.interval(Q(term["coefficient"]))
        for name, power in term["powers"].items():
            value *= atoms[name]**power
        answer += value
    return answer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", type=int, default=384)
    args = parser.parse_args()
    output = Path(__file__).resolve().parents[1]/"results"
    output.mkdir(exist_ok=True)
    start = time.perf_counter()
    all_certificates, atoms, cache = {}, {}, {}

    def mpl(indices, colors=None):
        indices = tuple(indices)
        colors = tuple(colors or (h.I,)+(h.ONE,)*(len(indices)-1))
        key = (indices, colors)
        if key not in cache:
            cache[key] = h.certified_mpl(indices, colors, args.bits)
        return cache[key]

    def remember(name, cert):
        data = cert.encode()
        data["decimal_center"] = [decimal_value(cert.center.re),
                                  decimal_value(cert.center.im)]
        data["decimal_radius_upper"] = decimal_upper(cert.radius)
        all_certificates[name] = data

    li1 = mpl((1,))
    remember("Li1_i", li1)
    atoms["pi"], atoms["ell"] = 4*li1.imag(), -2*li1.real()
    for n in (2,4,6,8):
        cert = mpl((n,))
        name = "G" if n == 2 else f"beta_{n}"
        atoms[name] = cert.imag()
        remember(name, cert)
    for n in (3,5,7):
        cert = mpl((n,), (h.ONE,))
        atoms[f"zeta_{n}"] = cert.real()
        remember(f"zeta_{n}", cert)
    for n in range(3,9):
        raw = h.certified_gpl((h.ZERO,)*(n-1)+(h.ONE-h.I,), args.bits)
        cert = h.Certificate(raw.word, raw.cutoff, -raw.center, raw.radius, -1)
        remember(f"Li{n}_half_gaussian", cert)
        atoms[f"mu_{n}"], atoms[f"lambda_{n}"] = cert.real(), cert.imag()

    rows, checks = [], []

    def add_row(name, indices, expression, component, origin, colors=None):
        cert = mpl(indices, colors)
        remember(name, cert)
        lhs = cert.imag() if component == "imaginary" else cert.real()
        difference = lhs-eval_polynomial(expression,atoms)
        assert difference.contains_zero(), (name,difference)
        upper = difference.max_abs()
        # This threshold is a deliberately much weaker display target than the
        # raw atom precision; it allows the exact product interval to widen.
        assert upper < Q(1,2**max(1,args.bits-60)), (name,upper)
        rows.append({"name":name,"indices":list(indices),"component":component,
                     "colors":[x.encode() for x in (colors or (h.I,)+(h.ONE,)*(len(indices)-1))],
                     "origin":origin,"terms":ids.polynomial_terms(expression)})
        checks.append({"name":name,"residual_interval":difference.encode(),
                       "contains_zero":True,"absolute_residual_bound":str(upper),
                       "decimal_absolute_bound_upper":decimal_upper(upper)})

    # All parity components through weight eight test the general formula,
    # including both a=1 and b=1 boundaries and both parity choices.
    for weight in range(2,9):
        for a in range(1,weight):
            b=weight-a
            component="imaginary" if weight%2==0 else "real"
            origin="manuscript weight-six conjecture" if weight==6 else "general parity specialization"
            add_row(f"double_{a}_{b}_{component}",(a,b),
                    ids.double_polynomial(a,b),component,origin)

    # Check every position of the 2 through weight eight, independently of the
    # symbolic extraction and independently of the logarithmic quadrature.
    for weight in range(2,9):
        for a in range(weight-1):
            b=weight-a-2
            indices=(1,)*a+(2,)+(1,)*b
            expression=s.expand(s.im(ids.one_two_polynomial(a,b)))
            origin="manuscript triple conjecture" if weight==4 else "all-position one-2 theorem"
            add_row(f"one2_{a}_{b}_imaginary",indices,expression,"imaginary",origin)

    p,l=ids.pi,ids.ell
    mixed_real=3*p**4*l/512+p**2*ids.zeta(3)/64-587*ids.zeta(5)/1024
    mixed_imag=3*ids.beta(6)-p**2*ids.beta(4)/6-p**4*ids.G/90-5*p**5*l/3072
    add_row("mixed_gaussian_4_1_real",(4,1),mixed_real,"real",
            "correction of a candidate mixed direction",(h.I,-h.I))
    add_row("mixed_gaussian_5_1_imaginary",(5,1),mixed_imag,"imaginary",
            "correction of a candidate mixed direction",(h.I,-h.I))

    # A strict enclosure independently confirms the nonzero mixed diagonal
    # antisymmetry used as a counterexample in the correction note.
    A=mpl((1,1),(-h.ONE,h.I))
    B=mpl((1,1),(h.I,-h.ONE))
    remember("mixed_Li11_minus1_i",A)
    remember("mixed_Li11_i_minus1",B)
    anti=A.imag()-B.imag()
    assert anti.low>0
    anti_identity=anti-(atoms["pi"]*atoms["ell"]/2-atoms["G"])
    assert anti_identity.contains_zero()
    diagonal=h.certified_mpl((3,3),(h.I,h.I),args.bits)
    remember("diagonal_Li33_i_i",diagonal)
    diagonal_re=9*atoms["zeta_3"]**2/2048+47*atoms["pi"]**6/1935360
    diagonal_im=-3*atoms["pi"]**3*atoms["zeta_3"]/1024
    assert (diagonal.real()-diagonal_re).contains_zero()
    assert (diagonal.imag()-diagonal_im).contains_zero()

    exact=ids.exact_checks()
    max_error=max(Q(x["absolute_residual_bound"]) for x in checks)
    summary={
        "requested_atom_precision_bits":args.bits,
        "exact_manuscript_polynomial_checks":len(exact),
        "certified_formula_comparisons":len(checks),
        "double_parity_comparisons":28,"one_two_comparisons":28,
        "mixed_gaussian_comparisons":2,
        "rational_value_certificates":len(all_certificates),
        "largest_residual_bound_upper":decimal_upper(max_error),
        "maximum_cutoff":max(x["cutoff"] for x in all_certificates.values()),
        "strict_mixed_antisymmetry_interval":anti.encode(),
        "mixed_antisymmetry_decimal_interval":[decimal_value(anti.low,30),decimal_value(anti.high,30)],
        "diagonal_stuffle_real_imag_checks":2,
        "elapsed_seconds":round(time.perf_counter()-start,3),
        "python":platform.python_version(),"sympy":s.__version__,
        "proof_status":"Written functional-equation proofs establish identities. Exact polynomial checks certify their displayed coefficients. Enclosure comparisons independently verify finite error bounds and do not by themselves prove equality.",
    }
    for filename,data in (
        ("polynomial_identities.json",rows),
        ("exact_manuscript_checks.json",exact),
        ("rational_certificates.json",all_certificates),
        ("enclosure_checks.json",checks),
        ("verification_summary.json",summary),
    ):
        (output/filename).write_text(json.dumps(data,indent=2)+"\n")
    print(json.dumps({k:v for k,v in summary.items() if "interval" not in k},indent=2))


if __name__=="__main__":
    main()

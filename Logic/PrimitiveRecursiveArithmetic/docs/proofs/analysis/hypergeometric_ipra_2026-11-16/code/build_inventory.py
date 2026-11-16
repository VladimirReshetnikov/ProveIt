from __future__ import annotations

import csv
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "theorem_inventory.csv"
TEX_PATH = ROOT / "sections" / "generated_inventory_table.tex"

rows = []

def add(i, source, locator, statement, status, report_ref, route, notes=""):
    rows.append({
        "id": i,
        "source": source,
        "source_locator": locator,
        "statement": statement,
        "status": status,
        "report_ref": report_ref,
        "formalization_route": route,
        "notes": notes,
    })

# Wikipedia inventory
add("W01","Wikipedia","series definition","Gauss 2F1 power-series definition","A/B","Def. 3.3; Thm. 4.2","PR coefficients plus explicit strict-disk tail")
add("W02","Wikipedia","Pochhammer definition","Rising factorial product and recurrences","A","Def. 3.1; Lem. 3.2","quantifier-free induction")
add("W03","Wikipedia","singular c","Ordinary coefficients fail when c is a nonpositive integer","A","Def. 3.3","finite denominator guard","Undefined means the guard fails")
add("W04","Wikipedia","termination","Termination and explicit polynomial for a=-m","A","Thm. 3.6","negative Pochhammer and finite binomial")
add("W05","Wikipedia","analytic continuation","Continuation along paths avoiding 1 and infinity","C","Thm. 10.2","coded disk chain with distance margins")
add("W06","Wikipedia","regularized limit","Limit of 2F1/Gamma(c) as c approaches -m","B","Thm. 3.8","reciprocal-gamma zeros plus head-tail modulus")
add("W07","Wikipedia","generalized pFq","2F1 as the p=2,q=1 generalized series","A","Def. 3.9","bounded products")
add("W08","Wikipedia","first derivative","First derivative parameter shift","A/B","Thm. 3.12; Thm. 4.4","coefficient identity plus analytic tail")
add("W09","Wikipedia","nth derivative","Arbitrary finite derivative order","A/B","Thm. 3.12; Thm. 4.4","induction on order")
add("W10","Wikipedia","special case","2F1(1,1;2;-z)=log(1+z)/z","A/B","Thm. 6.3","coefficient identity and named log")
add("W11","Wikipedia","special case","2F1(a,b;b;z)=(1-z)^(-a)","A/B","Thm. 6.1","first-order ODE uniqueness")
add("W12","Wikipedia","special case","Arcsine hypergeometric representation","A/B","Thm. 6.4","central-binomial coefficients")
add("W13","Wikipedia","special case","Cubic-radical representation","A/B","Thm. 6.5","algebraic cubic plus ODE uniqueness")
add("W14","Wikipedia","geometric series","2F1(1,b;b;z)=1/(1-z)","A/B","Cor. 6.2","binomial specialization")
add("W15","Wikipedia","confluent limit","1F1 as b->0 limit of 2F1(a,b^-1;c;bz)","B","Thm. 4.8","finite-head product limit plus uniform tail")
add("W16","Wikipedia","Bessel limiting cases","Functions reducible through confluent/0F1 limits","C","Sec. 4.5; Sec. 11","requires separate effective Bessel identifications","General claim only; not each Bessel formula")
add("W17","Wikipedia","Legendre function","Associated Legendre representation","C","Rem. 6.11","ODE change of variable plus branch normalization")
add("W18","Wikipedia","Jacobi polynomials","Jacobi polynomial representation","A","Thm. 6.8","terminating ODE and normalization")
add("W19","Wikipedia","other orthogonal polynomials","Krawtchouk, Meixner, Meixner-Pollaczek mentions","D","Sec. 12","no explicit formulas on source page")
add("W20","Wikipedia","modular lambda","Theta quotient inverts a hypergeometric ratio","D","Sec. 10.7","reduced to elliptic-modular inversion")
add("W21","Wikipedia","incomplete beta","Incomplete beta hypergeometric identity","B","Cor. 8.4","Euler integral and substitution")
add("W22","Wikipedia","elliptic K","Complete elliptic K representation","B","Cor. 8.5","Euler integral and t=sin^2 theta")
add("W23","Wikipedia","elliptic E","Complete elliptic E representation","B","Cor. 8.5","Euler integral and t=sin^2 theta")
add("W24","Wikipedia","ODE","Gauss hypergeometric differential equation","A/B","Thm. 5.1","coefficient recurrence")
add("W25","Wikipedia","singularities","Regular singular points at 0,1,infinity","A","Sec. 5.2","finite pole-order calculation")
add("W26","Wikipedia","Riemann reduction","Any certified three-regular-singularity equation reduces to Gauss","C","Thm. 5.9","Mobius change plus gauge certificate")
add("W27","Wikipedia","solutions at 0","Regular solution at zero","A/B","Prop. 5.3","Frobenius recurrence")
add("W28","Wikipedia","solutions at 0","Second nonresonant solution z^(1-c)F(...) ","A/C","Prop. 5.3","gauge identity plus branch")
add("W29","Wikipedia","resonance","Logarithmic second solution for integral exponent difference","C","Rem. 5.6","finite inhomogeneous recurrence; uniform library incomplete")
add("W30","Wikipedia","solutions at 1","Two local solutions at one","A/C","Prop. 5.4","z->1-z and gauge")
add("W31","Wikipedia","solutions at infinity","Two local solutions at infinity","A/C","Prop. 5.5","z->1/z and gauge")
add("W32","Wikipedia","six solutions","Six Frobenius expressions","A/C","Sec. 5.2","operator certificates plus branches")
add("W33","Wikipedia","Kummer 24","Twenty-four Kummer forms","A/C","Thm. 7.8","6x4 finite generator")
add("W34","Wikipedia","Kummer transformations","Euler/Pfaff equivalences among Kummer forms","A/B","Thms. 7.2-7.3","pullback-gauge certificates")
add("W35","Wikipedia","Q-form","Elimination of first derivative and printed Q(z)","A","Prop. 5.8","ring normalization")
add("W36","Wikipedia","Schwarz maps","Ratios of pairs of solutions","C","Prop. 10.7","named quotient under apartness")
add("W37","Wikipedia","Schwarz maps","Connection matrices act by Mobius transformations","A/C","Prop. 10.7","cross multiplication")
add("W38","Wikipedia","monodromy matrices","Printed monodromy matrices from exponents and connection data","C","Sec. 10.6","finite matrix check after connection certificate")
add("W39","Wikipedia","finite monodromy","Finite iff 1/k+1/l+1/m>1 in stated rational case","D","Audit 10.8","global group classification not reconstructed")
add("W40","Wikipedia","Euler integral","Euler beta integral representation","B","Thm. 8.2","endpoint cutoffs and termwise finite head")
add("W41","Wikipedia","Barnes integral","Barnes contour representation","C","Thm. 10.6","finite residue rectangle plus strip bounds")
add("W42","Wikipedia","John transform","Existence of a John-transform representation","D","Sec. 10.8","source gives no explicit formula or normalization")
add("W43","Wikipedia","contiguous functions","Six contiguous functions and basic identities","A","Thm. 9.1","coefficientwise rational identities")
add("W44","Wikipedia","15 relations","Fifteen pairwise contiguous relations","A","Cor. 9.2","equate master expressions")
add("W45","Wikipedia","integer shifts","Linear relation among any three integer-shifted functions","A","Thm. 9.3","bounded reduction algorithm")
add("W46","Wikipedia","continued fraction","Gauss ratio continued fraction","A/C","Thms. 9.5, 9.7","exact finite tail; infinite convergence certificate")
add("W47","Wikipedia","Euler transform","Euler transformation","A/B","Thm. 7.2","ODE pullback/gauge")
add("W48","Wikipedia","Pfaff transform","First Pfaff transformation","A/B","Thm. 7.3","ODE pullback/gauge")
add("W49","Wikipedia","Pfaff transform","Second Pfaff transformation","A/B","Thm. 7.3","symmetry plus first Pfaff")
add("W50","Wikipedia","connection at 1","Two-term connection formula","C","Thm. 10.4","local bases plus parameter/path certificates")
add("W51","Wikipedia","quadratic conditions","Existence pattern for quadratic transformations","C","Sec. 7.3","individual identities finitely checkable; classification not redone")
add("W52","Wikipedia","quadratic example","Printed transformation for 2F1(a,b;2b;z)","A/B","Thm. 7.5","pullback-gauge certificate")
add("W53","Wikipedia","higher transformations","Mention of cubic and higher transformations","C","Sec. 7.6","generic algebraic certificate checker")
add("W54","Wikipedia","z=1","Gauss summation theorem","B","Thm. 8.8","Euler chamber; parameter continuation conditional")
add("W55","Wikipedia","z=1","Chu-Vandermonde terminating sum","A","Thm. 8.6","uniform induction in m")
add("W56","Wikipedia","z=-1","Kummer summation theorem","B","Thm. 8.10","quadratic transform plus Gauss and duplication")
add("W57","Wikipedia","Kummer quadratics","Two Kummer quadratic transformations","A/B","Thm. 7.6","pullback-gauge certificates")
add("W58","Wikipedia","z=1/2","Gauss second summation theorem","B","Thm. 8.11","quadratic transform plus Gauss")
add("W59","Wikipedia","z=1/2","Bailey summation theorem","B","Thm. 8.12","Euler integral substitutions plus duplication")
add("W60","Wikipedia","other points","Algebraic Chebyshev form with x^2/(4(x-1))","A/C","Thm. 6.10","equivalent pullback identity; branches guarded")
add("W61","Wikipedia","other points","2F1(a,-a;1/2;sin^2(x/2))=cos(ax)","A/B","Thm. 6.10","transformed ODE and effective cosine")

# MathWorld inventory
add("M01","MathWorld","Eq. (1)","Generalized hypergeometric successive-term ratio","A","Prop. 3.10","bounded Pochhammer products")
add("M02","MathWorld","Eq. (2)","Hypergeometric ODE","A/B","Thm. 5.1","coefficient recurrence")
add("M03","MathWorld","Eqs. (3)-(4)","Frobenius coefficient recurrence","A","Lem. 3.4; Thm. 5.1","ring identity")
add("M04","MathWorld","Eqs. (5)-(8)","Regular series solution","A/B","Defs. 3.3-3.5","formal coefficients plus tail")
add("M05","MathWorld","convergence","Convergence for |z|<1","B","Thm. 4.2","explicit ratio cutoff")
add("M06","MathWorld","unit circle","Convergence at |z|=1 under positive excess","B","Thm. 4.6","gamma-ratio power tail with margin")
add("M07","MathWorld","Eq. (9)","Two-term complete local solution at zero","A/C","Prop. 5.3","nonresonant Frobenius basis")
add("M08","MathWorld","Eq. (10)","First derivative formula","A/B","Thm. 3.12; Thm. 4.4","coefficient shift")
add("M09","MathWorld","Eq. (11)","Second derivative formula","A/B","Thm. 3.12; Thm. 4.4","second induction instance")
add("M10","MathWorld","Eq. (12)","2F1(1,1;1;z)=1/(1-z)","A/B","Cor. 6.2","binomial")
add("M11","MathWorld","Eq. (13)","2F1(1,1;2;z)=-log(1-z)/z","A/B","Thm. 6.3","log series")
add("M12","MathWorld","Eq. (14)","2F1(1,2;1;z)=1/(1-z)^2","A/B","Cor. 6.2","coefficient n+1")
add("M13","MathWorld","Eq. (15)","2F1(1,2;2;z)=1/(1-z)","A/B","Cor. 6.2","binomial cancellation")
add("M14","MathWorld","Eq. (16)","Euler integral","B","Thm. 8.2","effective beta integral")
add("M15","MathWorld","Eq. (17)","Barnes contour integral","C","Thm. 10.6","residue and strip certificates")
add("M16","MathWorld","Eq. (18)","2F1(1/3,2/3;5/6;27/32)=8/5","D","Audit 8.14","numerically audited; modular/pullback proof absent")
add("M17","MathWorld","Eq. (19)","2F1(1/4,1/2;3/4;80/81)=9/5","D","Audit 8.14","numerically audited; modular proof absent")
add("M18","MathWorld","Eq. (20)","Value 2 sqrt(7)/3 at 2400/2401","D","Audit 8.14","numerically audited; modular proof absent")
add("M19","MathWorld","Eq. (21)","Value 3 sqrt(3)/4 at 25/27","D","Audit 8.14","numerically audited; modular proof absent")
add("M20","MathWorld","Eq. (22)","Value (4/3)2^(1/6) at 125/128","D","Audit 8.14","numerically audited; modular proof absent")
add("M21","MathWorld","Eq. (23)","Value (3/4)11^(1/4) at 1323/1331","D","Audit 8.14","numerically audited; modular proof absent")
add("M22","MathWorld","Eq. (24)","Gamma quotient at 121/125","D","Audit 8.14","numerically audited; modular proof absent")
add("M23","MathWorld","Eqs. (25)-(26)","Glasser well-poised algebraic family","A/B","Thm. 6.6","Fuss-Catalan algebraic equation")
add("M24","MathWorld","Eq. (27)","k=2 Glasser specialization and rational value","A/B","Cor. 6.7","specialize general family")
add("M25","MathWorld","Eqs. (28)-(34)","Euler/Pfaff transformations and substitutions","A/B","Thms. 7.2-7.3","pullback-gauge certificates")
add("M26","MathWorld","Eq. (35)","Connection formula at one","C","Thm. 10.4","basis connection with path data")
add("M27","MathWorld","Eqs. (36)-(41)","Six Kummer solutions","A/C","Props. 5.3-5.5","Frobenius and branch data")
add("M28","MathWorld","Eqs. (42)-(65)","Twenty-four Kummer forms","A/C","Thm. 7.8; App. 13","6x4 generator and table")
add("M29","MathWorld","cubic transformations","Existence of Goursat cubic transformations","C","Sec. 7.6","finite certificate interface; list not reconstructed")
add("M30","MathWorld","Eq. (66)","Legendre polynomial representation","A","Cor. 6.9","Jacobi specialization")
add("M31","MathWorld","Eq. (67)","(1+z)^n terminating hypergeometric identity","A","Cor. 3.7","finite binomial theorem")
add("M32","MathWorld","Eq. (68)","log(1+z)=z 2F1(1,1;2;-z)","A/B","Thm. 6.3","log series")
add("M33","MathWorld","elliptic mention","Complete elliptic integral representations","B","Cor. 8.5","Euler integral")
add("M34","MathWorld","Eq. (69)","Kummer z=-1 formula in duplication form","B","Thm. 8.10","quadratic plus Gauss")
add("M35","MathWorld","Eq. (70)","2F1(1,-a;a;-1) gamma evaluation","B","Thm. 8.13","Euler integral split and duplication")
add("M36","MathWorld","Eq. (71)","z=1/2 to z=-1 Pfaff conversion","A/B","Cor. 7.4","Pfaff at one half")
add("M37","MathWorld","Eq. (72)","Gauss second theorem","B","Thm. 8.11","quadratic plus Gauss")
add("M38","MathWorld","Eq. (73)","Bailey theorem","B","Thm. 8.12","beta substitutions")
add("M39","MathWorld","Eq. (74)","Gauss theorem","B","Thm. 8.8","Euler beta integral")
add("M40","MathWorld","Eq. (75)","Kummer first formula with -n","A","Cor. 8.7","Vandermonde plus gamma notation")
add("M41","MathWorld","Eq. (76)","Generalized nFm definition","A/B","Def. 3.9; Sec. 4","PR terms plus convergence by p-q regime")
add("M42","MathWorld","confluent mention","1F1 confluent function as a limiting family","B","Thm. 4.8","effective confluent limit")
add("M43","MathWorld","0F1 mention","0F1 coefficient definition and strict-disk convergence","A/B","Def. 3.9; Sec. 4","factorial-dominated tail")

fieldnames = ["id","source","source_locator","statement","status","report_ref","formalization_route","notes"]
with CSV_PATH.open("w", newline="", encoding="utf-8") as f:
    w=csv.DictWriter(f,fieldnames=fieldnames)
    w.writeheader(); w.writerows(rows)

# TeX escaping, deliberately compact.
def tex(s: str) -> str:
    rep = {
        "\\": r"\textbackslash{}",
        "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
        "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(rep.get(ch,ch) for ch in s)

with TEX_PATH.open("w",encoding="utf-8") as f:
    f.write("\\begin{longtable}{@{}p{.065\\textwidth}p{.53\\textwidth}p{.08\\textwidth}p{.245\\textwidth}@{}}\n")
    f.write("\\toprule ID & Statement & Status & Report route \\\\\n")
    f.write("\\midrule\\endfirsthead\n")
    f.write("\\toprule ID & Statement & Status & Report route \\\\\n")
    f.write("\\midrule\\endhead\n")
    f.write("\\midrule\\multicolumn{4}{r}{\\emph{continued}}\\\\\\endfoot\n")
    f.write("\\bottomrule\\endlastfoot\n")
    for r in rows:
        f.write(f"{tex(r['id'])} & {tex(r['statement'])} & \\textsf{{{tex(r['status'])}}} & {tex(r['report_ref'])} \\\\\n")
    f.write("\\end{longtable}\n")

counts = Counter(r["status"] for r in rows)
print(f"rows={len(rows)}")
print(dict(sorted(counts.items())))

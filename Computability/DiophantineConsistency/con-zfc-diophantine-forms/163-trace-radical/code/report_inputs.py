#!/usr/bin/env python3
"""Generate literal report inputs from the sealed equation artifacts."""
from pathlib import Path
from collections import Counter
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "report"

def load(path):
    return json.loads((ROOT / path).read_text())

def term_tex(coefficient, indices, first=False):
    counts = Counter(indices)
    factors = []
    for index, exponent in sorted(counts.items()):
        text = "x_{" + str(index) + "}"
        if exponent != 1:
            text += "^{" + str(exponent) + "}"
        factors.append(text)
    body = r"\,".join(factors)
    magnitude = abs(coefficient)
    if magnitude != 1 or not factors:
        body = str(magnitude) + (r"\," if factors else "") + body
    sign = "-" if coefficient < 0 else ("" if first else "+")
    weight = 2 + len(str(magnitude)) + sum(3 + len(str(i)) for i in indices)
    return sign + body, weight

def render_residuals(equation):
    result = [
        "% Generated from direct/equations/self_power236/equation.json.",
        r"\begingroup\small",
        r"\setlength{\jot}{1pt}",
        r"\begin{align*}",
    ]
    for i, row in enumerate(equation["residuals"]):
        parts = []
        line = []
        weight = 0
        for j, (coefficient, indices) in enumerate(row["terms"]):
            text, cost = term_tex(coefficient, indices, first=(j == 0))
            if line and weight + cost > 106:
                parts.append(" ".join(line))
                line = []
                weight = 0
            line.append(text)
            weight += cost
        parts.append(" ".join(line))
        for j, part in enumerate(parts):
            prefix = "R_{" + str(i) + "} &={} " if j == 0 else r"&\quad{} "
            if j != len(parts)-1:
                suffix = r" \\*"
            elif i != len(equation["residuals"])-1:
                suffix = r" \\[3pt]"
            else:
                suffix = ""
            result.append(prefix + part + suffix)
    result.extend([r"\end{align*}", r"\endgroup", ""])
    return "\n".join(result)

def comparison():
    compact = load("compact/RESULTS.json")
    lines = [
        r"\begin{table}[ht]\centering\small",
        r"\begin{tabular}{@{}rrrr@{}}\toprule",
        r"Unknowns/domain & Operations & Parent degree & New degree\\\midrule",
    ]
    for item in compact:
        lines.append("10 positive & %d & %s & %s\\\\" %
                     (item["operations"], f'{item["parent_degree"]:,}', f'{item["degree"]:,}'))
    lines += [
        r"\bottomrule\end{tabular}",
        r"\caption{The five compact improvements. Each retains its parent's operation count and complete fixed coefficient tuple.}\label{tab:compact}",
        r"\end{table}",
        r"\begin{table}[ht]\centering\small",
        r"\begin{tabular}{@{}lrrrr@{}}\toprule",
        r"Integer quartic & Variables & Rows & Terms & Height\\\midrule",
    ]
    for name, display in (("self_power236", "Sparse diagonal power"),
                          ("self_power235", "Dense diagonal power"),
                          ("shared_error234", "Shared factorial error")):
        m = load(f"direct/equations/{name}/METRICS.json")
        lines.append(display + " & " + " & ".join(
            f'{m[k]:,}' for k in ("variables","rows","terms","height")) + r"\\")
    lines += [
        r"\bottomrule\end{tabular}",
        r"\caption{Three new direct equations over unrestricted integers. All have exact degree four.}\label{tab:direct}",
        r"\end{table}",
        r"The matched direct parents have respectively $242$, $241$, and $240$ variables.",
        r"The first two new branches also replace the label base by $t^t$.",
        r"Each final radical projection phase removes exactly six variables and six rows.",
        r"The $240$-variable shared-error parent has $21{,}482$ terms and height $6{,}144$;",
        r"its $234$-variable descendant reduces dimension and support but increases height.",
        "",
    ]
    return "\n".join(lines)

def degrees():
    receipt = load("compact/VERIFICATION.json")
    lines = [
        r"Set $q_0=\beta J$ and $k_0=\eta+\zeta$. The complete highest homogeneous part",
        r"of the principal equation is",
        r"\[",
        r"[P_{\mathrm{tr}}]_{232}",
        r"=-9\,2^{10}q_0^{100}w^{26}s^{58}i^{10}k_0^{32}",
        r"\bigl(k_0sT-q_0^2(q_0-F)\bigr)^2.",
        r"\]",
        r"It is nonzero because $\beta>0$. The new degrees of $f,V,Q,G,M,Z$",
        r"are respectively $36,40,80,50,11,57$. Thus $-QM^2GV^2$ has degree",
        r"$80+22+50+80=232$, while $QZ^2$ has degree $194$ and the remaining",
        r"terms are lower. The verifier computes the full highest forms, including",
        r"every possible cancellation in the arithmetic circuit.",
        "",
        r"For each circuit, the following is one coefficient-certified term of",
        r"its highest homogeneous part. Here $\beta$ is a fixed positive integer",
        r"and is assigned degree zero.",
        r"\begin{align*}",
    ]
    texnames = {v: "\\"+v for v in ("alpha","beta","eta","zeta")}
    for pos, circuit in enumerate(receipt["circuits"]):
        top = circuit["leading"]["top"]
        selected = min(top, key=lambda a:(len(a["powers"]),sum(a["powers"].get(v,0) for v in ("F","alpha","T")), sorted(a["powers"].items())))
        powers = selected["powers"]
        inputs = {k:v for k,v in powers.items() if k != "beta"}
        duplicates = [a for a in top if {k:v for k,v in a["powers"].items() if k!="beta"}==inputs]
        if len(duplicates) != 1:
            raise ValueError("Selected coefficient has more than one fixed-port contribution")
        if sum(inputs.values()) != circuit["leading"]["degree"]:
            raise ValueError("Wrong selected homogeneous degree")
        body = str(selected["coefficient"])
        for v, e in sorted(powers.items()):
            body += r"\," + texnames.get(v,v)
            if e != 1:
                body += "^{" + str(e) + "}"
        line = r"d=%d:\quad & %s" % (circuit["leading"]["degree"],body)
        if pos != len(receipt["circuits"])-1:
            line += r"\\"
        lines.append(line)
    lines += [r"\end{align*}", ""]
    return "\n".join(lines)

def all_outputs():
    recipe = (ROOT/"compact/coefficient_recipe.tex").read_text()
    recipe = recipe.replace(
        "The alphabet, in order of digit values $0,\\ldots,61$, is\n",
        "The alphabet, in order of digit values $0,\\ldots,61$, is\n\\par\\noindent\n")
    recipe = recipe.replace(r"\fontsize{7.7}{8.2}",r"\fontsize{9.0}{10.5}")
    return {
        "residuals236.tex":render_residuals(load("direct/equations/self_power236/equation.json")),
        "comparison.tex":comparison(),
        "degrees.tex":degrees(),
        "coefficient_note.tex":(
            r"The compact equation retains its native/K215 ancestry. The direct"
            "\n" r"quartics in Appendix~\ref{app:direct} use the separate proof-calculus route."
            "\n" r"The four coefficient payloads in \texttt{compact/coefficients/} have"
            "\n" r"bit lengths $590{,}069$, $592{,}884$, $590{,}069$, and $590{,}070$"
            "\n" r"for $\beta,K_0,M_C,M_F$ respectively. The following complete finite"
            "\n" r"recipe is retained unchanged and its reconstruction is checked exactly."
            "\n" r"\input{coefficient_recipe_formatted.tex}" "\n"),
        "coefficient_recipe_formatted.tex":recipe,
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args()
    outputs=all_outputs()
    for name, text in outputs.items():
        path=REPORT/name
        if args.check:
            if path.read_text()!=text:
                raise ValueError("Literal report mismatch: "+name)
        else:
            path.write_text(text)
    print(json.dumps({"status":"PASS","literal_inputs":sorted(outputs),"residuals":172}))

if __name__=="__main__":
    main()

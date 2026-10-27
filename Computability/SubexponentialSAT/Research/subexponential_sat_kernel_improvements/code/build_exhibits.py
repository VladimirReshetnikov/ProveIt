#!/usr/bin/env python3
"""Regenerate the report's tables and scientific figure from recorded data.

Tables use only the standard library. Plotting requires matplotlib. This
script does not rerun benchmarks or replace measured data.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
FIGURES = ROOT / "figures"


def table(path, caption, columns, header, rows):
    lines = [r"\begin{table}[htbp]", r"\centering\small",
             r"\begin{tabular}{@{}" + columns + r"@{}}",
             r"\toprule", header + r"\\\midrule"]
    lines.extend(" & ".join(row) + r"\\" for row in rows)
    lines += [r"\bottomrule", r"\end{tabular}",
              r"\caption{" + caption + "}", r"\end{table}"]
    path.write_text("\n".join(lines)+"\n")


def main():
    data = json.loads((RESULTS / "benchmarks.json").read_text())["rows"]
    selected = [("squarefree",14,"Squarefree"),
                ("multiplicity-two",18,"All exponents two"),
                ("three-modes",48,"Three exponents sixteen"),
                ("one-odd-exponent",13,"One odd exponent"),
                ("quadratic-extension",10,"Quadratic extension"),
                ("nilpotent-extension",8,"Nilpotent extension")]
    rows=[]
    for family,R,label in selected:
        item=next(x for x in data if x["family"]==family and x["R"]==R)
        times=item["median_seconds"]
        rows.append([label,str(R),f'{times["baseline"]:.6f}',
                     f'{times["gray"]:.6f}',f'{times["antipodal_gray"]:.6f}',
                     f'{item["speedup_antipodal"]:.2f}'])
    table(RESULTS / "extraction_table.tex",
          "Selected packet extraction medians in seconds. Gain is the old runtime divided by the antipodal runtime; it is not a SAT speedup.",
          "lrrrrr", "Case & $R$ & Old & Gray & Antipodal & Gain",rows)

    pdata=json.loads((RESULTS / "projective_benchmarks.json").read_text())["rows"]
    rows=[]
    pselected=[("paired-quadratic",6,"All two, small"),
               ("paired-quadratic",18,"All two, quadratic"),
               ("paired-nilpotent",12,"All two, nilpotent"),
               ("paired-low-precision",12,"All two, $p=1$"),
               ("mixed",10,"Mixed one/two")]
    for family,R,label in pselected:
        item=next(x for x in pdata if x["family"]==family and x["R"]==R)
        times=item["median_seconds"]
        rows.append([label,str(R),f'{times["baseline"]:.6f}',
                     f'{times["antipodal_gray"]:.6f}',f'{times["projective"]:.6f}',
                     f'{item["speedup_over_baseline"]:.2f}'])
    table(RESULTS / "projective_table.tex",
          "Projective specialization, median seconds. The same extension ring and same coefficient input are used for all methods within each row. Gain compares old and projective runtimes.",
          "lrrrrr","Case & $R$ & Old & Antipodal & Projective & Gain",rows)

    adaptive=json.loads((RESULTS / "adaptive_mode_results.json").read_text())["comparisons"]
    rows=[]
    for x in adaptive:
        rows.append([str(1<<x["a"]),str(x["i"]),str(x["precision"]),str(x["rows"]),
                     str(len(x["baseline_weights"])),str(len(x["adaptive_weights"])),
                     f'{x["baseline_inventory"]:,}',f'{x["adaptive_inventory"]:,}'])
    table(RESULTS / "adaptive_table.tex",
          "Exact local inventories over the quadratic extension with interpolation value $\\zeta=U$. There are $m$ real rows and columns. Mode and tuple counts compare the normalized restricted padded basis with adaptive separation.",
          "rrrrrrrr", "$L$ & $i$ & $p$ & $m$ & Old modes & New modes & Old tuples & New tuples",rows)

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size":10,"axes.spines.top":False,
                         "axes.spines.right":False,"pdf.fonttype":42})
    fig,axes=plt.subplots(1,2,figsize=(9,3.3),constrained_layout=True)
    styles=[("baseline","Existing finite differences","#656565","o"),
            ("gray","Gray updates","#3578a8","s"),
            ("antipodal_gray","Antipodal Gray","#147d58","^")]
    for axis,family,title in zip(axes,["squarefree","multiplicity-two"],
                                 ["Squarefree target","Every exponent equals two"]):
        subset=[x for x in data if x["family"]==family]
        for key,label,color,marker in styles:
            axis.plot([x["R"] for x in subset],
                      [x["median_seconds"][key] for x in subset],
                      label=label,color=color,marker=marker,linewidth=1.7)
        axis.set_yscale("log")
        axis.set_xlabel("Number of affine factors R")
        axis.set_ylabel("Median runtime (seconds)")
        axis.set_title(title)
        axis.set_xticks([x["R"] for x in subset])
        axis.grid(axis="y",alpha=.18)
    axes[0].legend(frameon=False,fontsize=8,loc="upper left")
    FIGURES.mkdir(exist_ok=True)
    fig.savefig(FIGURES / "extraction_scaling.pdf")
    fig.savefig(FIGURES / "extraction_scaling.png",dpi=180)
    print("Regenerated three tables and the runtime figure from recorded results.")


if __name__ == "__main__":
    main()

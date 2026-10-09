"""Rebuild article tables, macros and figure from retained paired measurements."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ARTICLE = ROOT / "article"
DATA = ROOT / "synthesis/data"


def read(path):
    return json.loads(path.read_text())


def number(x, decimals=3):
    return f"{x:,.{decimals}f}".replace(",", r"\,")


def integer(x):
    return f"{x:,}".replace(",", r"\,")


def main():
    scoring = read(DATA / "cocycle-transport-benchmark.json")["benchmarks"]
    boundary = read(ROOT / "fast/marked_boundary_research/measurements_matched_final.json")
    lines = [
        r"\small",
        r"\begin{tabular}{rrrrrr}",
        r"\toprule",
        r"$t$ & Sites & Bits & Local (ms) & Fresh $H^1$ (ms) & Ratio\\",
        r"\midrule",
    ]
    for row in scoring:
        med = row["median_seconds"]
        lines.append(
            f'{row["tetrahedra"]} & {row["candidates"]} & {row["height_bits"]} & '
            f'{number(1000*med["local"])} & {number(1000*med["restart"])} & '
            f'{number(row["median_speedup"], 2)}'+r"$\times$\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    (ARTICLE / "cocycle_scoring_table.tex").write_text("\n".join(lines)+"\n")

    lines = [
        r"\small",
        r"\begin{tabular}{rrrrrr}",
        r"\toprule",
        r"Marks & \multicolumn{2}{c}{Producer (ms)} & \multicolumn{2}{c}{Replay (ms)} & Replay\\",
        r" & Moments & One-hot & Moments & One-hot & ratio\\",
        r"\midrule",
    ]
    for case in boundary["cases"]:
        m, h = (case["medians"][name] for name in ("moments", "one_hot"))
        lines.append(
            f'{case["marked_vertices"]} & {number(1000*m["producer_seconds"])} & '
            f'{number(1000*h["producer_seconds"])} & {number(1000*m["replay_seconds"])} & '
            f'{number(1000*h["replay_seconds"])} & {number(case["replay_speedup"],2)}'
            + r"$\times$\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    (ARTICLE / "boundary_encoding_table.tex").write_text("\n".join(lines)+"\n")

    top, btop = scoring[-1], boundary["cases"][-1]
    m, h = (btop["medians"][name] for name in ("moments", "one_hot"))
    macros = {
        "ScoringLocalMax": number(1000*top["median_seconds"]["local"]),
        "ScoringRestartMax": number(1000*top["median_seconds"]["restart"]),
        "ScoringSpeedupMax": number(top["median_speedup"],2),
        "BoundaryTraceMax": integer(m["trace_events"]),
        "BoundaryReplaySpeedupMax": number(btop["replay_speedup"],2),
        "BoundaryCombinedSpeedupMax": number(btop["combined_speedup"],2),
        "BoundaryMomentBytes": integer(m["certificate_bytes"]),
        "BoundaryBasisBytes": integer(h["certificate_bytes"]),
    }
    (ARTICLE / "benchmark_macros.tex").write_text(
        "\n".join(r"\newcommand{\%s}{%s}" % item for item in macros.items())+"\n"
    )
    log = (ROOT / "validation/full_tests.log").read_text()
    match = re.search(r"Ran (\d+) tests in ([\d.]+)s", log)
    if match is None or not re.search(r"^OK(?:\s|$)", log, re.MULTILINE):
        raise RuntimeError("A successful completed full-suite record is required")
    (ARTICLE / "validation_counts.tex").write_text(
        r"\newcommand{\FullTestCount}{"+integer(int(match[1]))+"}\n"
    )

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import ScalarFormatter
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 8.5, "axes.titlesize": 9,
        "axes.labelsize": 8.5, "legend.fontsize": 7.5, "pdf.fonttype": 42,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.edgecolor": "#687784", "text.color": "#18334A",
        "axes.labelcolor": "#18334A", "xtick.color": "#485966",
        "ytick.color": "#485966",
    })
    fig, axes = plt.subplots(1,2,figsize=(6.5,2.9),layout="constrained")
    colors = {"local":"#00848A","restart":"#A94F25",
              "moments":"#00848A","one_hot":"#A94F25"}
    left = axes[0]
    xs = [row["tetrahedra"] for row in scoring]
    for name, label in (("local","Five-height scoring"),("restart","Fresh cohomology at each site")):
        ys = [1000*row["median_seconds"][name] for row in scoring]
        left.plot(xs,ys,color=colors[name],marker="o",markersize=3.5,label=label,linewidth=1.6)
        for x,row in zip(xs,scoring):
            raw = row["seconds"][name]
            jitter = [x*(1+0.018*(i-(len(raw)-1)/2)) for i in range(len(raw))]
            left.scatter(jitter,[1000*y for y in raw],s=9,alpha=0.35,color=colors[name],zorder=1)
    left.set(title="All eligible collapse scores",xlabel="Tetrahedra",ylabel="Milliseconds")
    left.set_xscale("log",base=2)
    left.set_yscale("log")
    left.set_xticks(xs)
    left.xaxis.set_major_formatter(ScalarFormatter())
    left.legend(loc="upper left",frameon=False)

    right = axes[1]
    ps = [case["marked_vertices"] for case in boundary["cases"]]
    for name,label in (("moments","Four moments"),("one_hot","One-hot endpoint vectors")):
        ys = [1000*case["medians"][name]["replay_seconds"] for case in boundary["cases"]]
        right.plot(ps,ys,color=colors[name],marker="o",markersize=3.5,label=label,linewidth=1.6)
        for p,case in zip(ps,boundary["cases"]):
            raw = [obs["replay_seconds"] for trial in case["trials"]
                   for obs in trial["observations"] if obs["weight_encoding"]==name]
            jitter = [p*(1+0.025*(i-(len(raw)-1)/2)) for i in range(len(raw))]
            right.scatter(jitter,[1000*y for y in raw],s=10,alpha=0.4,color=colors[name],zorder=1)
    right.set(title="Independent marked-order replay",xlabel="Explicit marks",ylabel="Milliseconds")
    right.set_xscale("log",base=2)
    right.set_yscale("log")
    right.set_xticks(ps)
    right.xaxis.set_major_formatter(ScalarFormatter())
    right.legend(loc="upper left",frameon=False)
    for ax in axes:
        ax.grid(axis="y",which="major",alpha=0.2,linewidth=0.5)
        ax.set_axisbelow(True)
    out = ARTICLE/"figures"
    out.mkdir(exist_ok=True)
    fig.savefig(out/"paired_performance.pdf",metadata={"Title":"Paired geometric-kernel performance"})
    fig.savefig(out/"paired_performance.png",dpi=180)
    plt.close(fig)
    print("Tables, macros and paired-performance figure rebuilt from retained samples.")


if __name__ == "__main__":
    main()

"""Regenerate the article's exact illustration and measured-results fragment.

Run from any working directory with Python and matplotlib installed.  This
script reads the retained benchmark JSON; it neither reruns a benchmark nor
changes any measured observation.  All geometry in the strip illustration
is constructed and checked with Fraction before conversion for rendering.
"""

from datetime import datetime
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import statistics

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "article" / "figures"
RESULTS = ROOT / "results" / "paired_benchmark.json"
INK = "#173046"
TEAL = "#006579"
GOLD = "#AD6B16"
PLUM = "#923D58"
GRAY = "#66717D"

plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif"],
    "font.size": 9,
    "mathtext.fontset": "cm",
    "axes.labelcolor": INK,
    "text.color": INK,
    "xtick.color": INK,
    "ytick.color": INK,
    "axes.edgecolor": INK,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "savefig.facecolor": "white",
})


def protocol(case, name):
    return next(row for row in case["protocols"] if row["protocol"] == name)


def fraction_label(value):
    if value.denominator == 1:
        return str(value.numerator)
    return rf"$\frac{{{value.numerator}}}{{{value.denominator}}}$"


def save_figure(fig, name, title, date):
    metadata = dict(Title=title, Author="ProveIt research continuation",
                    CreationDate=date, ModDate=date)
    fig.savefig(FIGURES / (name + ".pdf"), metadata=metadata,
                bbox_inches="tight", pad_inches=0.04)
    fig.savefig(FIGURES / (name + ".png"), dpi=240,
                bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def minimum_overlay(date):
    m, n = 2, 3
    xs = tuple(Fraction(j, m + 1) for j in range(m + 2))
    ys = tuple(Fraction(j, n + 1) for j in range(n + 2))

    def forms(count):
        return tuple((-j, Fraction(j * (j + 1), 2 * (count + 1)))
                     for j in range(count + 1))

    def minimizers(fs, point):
        values = tuple(a * point + b for a, b in fs)
        return {j for j, value in enumerate(values) if value == min(values)}

    xforms, yforms = forms(m), forms(n)
    for grid, fs, count in ((xs, xforms, m), (ys, yforms, n)):
        for j, (left, right) in enumerate(zip(grid, grid[1:])):
            assert minimizers(fs, (left + right) / 2) == {j}
        for j, point in enumerate(grid[1:-1], 1):
            assert minimizers(fs, point) == {j - 1, j}
        assert minimizers(fs, grid[0]) == {0}
        assert minimizers(fs, grid[-1]) == {count}

    xvertices = set(product(xs, (Fraction(0), Fraction(1))))
    yvertices = set(product((Fraction(0), Fraction(1)), ys))
    overlay = set(product(xs, ys))
    crossings = set(product(xs[1:-1], ys[1:-1]))
    corners = set(product((Fraction(0), Fraction(1)), repeat=2))
    boundary = overlay - crossings - corners
    assert len(xvertices) == 8 and len(yvertices) == 10
    assert len(overlay) == (m + 2) * (n + 2) == 20
    assert (len(corners), len(boundary), len(crossings)) == (4, 10, 6)

    fig, axes = plt.subplots(1, 3, figsize=(6.5, 2.65))
    fig.subplots_adjust(left=0.06, right=0.985, bottom=0.26,
                        top=0.81, wspace=0.40)
    titles = (r"(a) Minima in $x$", r"(b) Minima in $y$", "(c) Common subdivision")
    counts = ("3 cells; 8 vertices", "4 cells; 10 vertices",
              "12 cells; 20 vertices\n6 proper crossings")
    for index, ax in enumerate(axes):
        ax.set(xlim=(0, 1), ylim=(0, 1), aspect="equal")
        ax.set_title(titles[index], fontsize=9.3, pad=9)
        ax.set_xlabel(r"$x$", labelpad=0)
        ax.set_ylabel(r"$y$", rotation=0, labelpad=3)
        ax.tick_params(length=2, pad=3, labelsize=8.5)
        ax.set_xticks([float(x) for x in (xs if index != 1 else (xs[0], xs[-1]))])
        ax.set_xticklabels([fraction_label(x) for x in (xs if index != 1 else (xs[0], xs[-1]))])
        ax.set_yticks([float(y) for y in (ys if index != 0 else (ys[0], ys[-1]))])
        ax.set_yticklabels([fraction_label(y) for y in (ys if index != 0 else (ys[0], ys[-1]))])
        for spine in ax.spines.values():
            spine.set_linewidth(0.9)
        ax.text(0.5, -0.46, counts[index], transform=ax.transAxes,
                ha="center", va="top", fontsize=8.4, linespacing=1.4)

    for j, (left, right) in enumerate(zip(xs, xs[1:])):
        axes[0].add_patch(Rectangle((float(left), 0), float(right-left), 1,
                                   facecolor=TEAL, alpha=0.07+0.055*j, edgecolor="none"))
        axes[0].text(float((left+right)/2), 0.50, rf"$h_{j}$",
                     ha="center", va="center", color=TEAL, fontsize=11)
        for ell, (bottom, top) in enumerate(zip(ys, ys[1:])):
            axes[2].add_patch(Rectangle((float(left), float(bottom)),
                                       float(right-left), float(top-bottom),
                                       facecolor=TEAL, alpha=0.035+0.019*(j+ell),
                                       edgecolor="none"))
    for j, (bottom, top) in enumerate(zip(ys, ys[1:])):
        axes[1].add_patch(Rectangle((0, float(bottom)), 1, float(top-bottom),
                                   facecolor=GOLD, alpha=0.06+0.043*j, edgecolor="none"))
        axes[1].text(0.50, float((bottom+top)/2), rf"$g_{j}$",
                     ha="center", va="center", color=GOLD, fontsize=11)
    for x in xs[1:-1]:
        for ax in (axes[0], axes[2]):
            ax.axvline(float(x), color=TEAL, lw=1.15, zorder=3)
    for y in ys[1:-1]:
        for ax in (axes[1], axes[2]):
            ax.axhline(float(y), color=GOLD, lw=1.15, zorder=3)

    def dots(ax, points, color, size=15):
        points = sorted(points)
        ax.scatter([float(p[0]) for p in points], [float(p[1]) for p in points],
                   s=size, color=color, edgecolors="white", linewidths=0.45,
                   zorder=5, clip_on=False)

    dots(axes[0], xvertices, TEAL)
    dots(axes[1], yvertices, GOLD)
    dots(axes[2], boundary, INK)
    dots(axes[2], corners, INK)
    dots(axes[2], crossings, PLUM, 23)
    save_figure(fig, "minimum_overlay", "Exact rational minimum-strip overlay", date)

    data = dict(m=m, n=n, domain="[0,1]^2",
                formula="h_j(x)=-j*x+j*(j+1)/(2*(m+1)); analogous g_j(y)",
                x_forms=[[str(a), str(b)] for a, b in xforms],
                y_forms=[[str(a), str(b)] for a, b in yforms],
                x_breaks=[str(x) for x in xs[1:-1]],
                y_breaks=[str(y) for y in ys[1:-1]],
                overlay_vertices=[[str(x), str(y)] for x, y in sorted(overlay)],
                counts=dict(x_cells=m+1, x_vertices=len(xvertices),
                            y_cells=n+1, y_vertices=len(yvertices),
                            overlay_cells=(m+1)*(n+1), overlay_vertices=len(overlay),
                            corners=len(corners), boundary_endpoints=len(boundary),
                            proper_crossings=len(crossings)),
                scope="Rational potential system; no normal-sector realization asserted.")
    (FIGURES / "minimum_overlay_data.json").write_text(json.dumps(data, indent=2)+"\n")


def family_cases(result):
    return sorted((case for case in result["cases"]
                   if case["kind"] == "double-capped Fibonacci solid torus"),
                  key=lambda case: case["family_n"])


def measured_calls(row, arm):
    return [call for replicate in row["rounds"] for call in replicate["calls"]
            if call["arm"] == arm and call["status"] == "COMPLETE"]


def timing_figure(result, date):
    family = family_cases(result)
    fig, axes = plt.subplots(1, 2, figsize=(6.5, 3.2), sharey=True)
    fig.subplots_adjust(left=0.105, right=0.98, bottom=0.20,
                        top=0.79, wspace=0.23)
    for ax, name, title in zip(axes, ("prepared", "full"),
                               ("(a) Prepared kernel", "(b) Build + enumerate")):
        for arm, label, color, marker in (
                ("baseline", "Maintained arrangement", GRAY, "o"),
                ("planar", "Planar minimum overlay", TEAL, "s")):
            points = []
            for case in family:
                calls = measured_calls(protocol(case, name), arm)
                if calls:
                    values = [1000*call["seconds"] for call in calls]
                    points.append((case["kernel_stats"]["tetrahedra"],
                                   statistics.median(values), min(values), max(values)))
            xs, medians, lower, upper = map(list, zip(*points))
            ax.errorbar(xs, medians,
                        yerr=([m-lo for m, lo in zip(medians, lower)],
                              [hi-m for m, hi in zip(medians, upper)]),
                        color=color, marker=marker, markersize=4, lw=1.25,
                        elinewidth=0.8, capsize=2.2, label=label, zorder=3)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        ticks = [case["kernel_stats"]["tetrahedra"] for case in family]
        ax.xaxis.set_major_locator(FixedLocator(ticks))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, _: str(int(value))))
        ax.xaxis.set_minor_locator(NullLocator())
        ax.yaxis.set_minor_locator(NullLocator())
        ax.set_ylim(1, 23000)
        ax.set_xlim(2.65, 39)
        ax.grid(axis="y", which="major", color="#DEE4E9", lw=0.65)
        ax.set_xlabel(r"Total tetrahedra $t=n+2$", labelpad=6)
        ax.set_title(title, fontsize=10, pad=10)
        ax.tick_params(labelsize=8)
        for spine in ("top", "right"):
            ax.spines[spine].set_visible(False)
    axes[0].set_ylabel("Elapsed wall time (ms)", labelpad=4)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", bbox_to_anchor=(0.52, 1.015),
               ncol=2, frameon=False, fontsize=8.5, handlelength=2.3)
    save_figure(fig, "paired_timings", "Paired supplied-sector timing observations", date)


def ms(value):
    return "capped" if value is None else f"{1000*value:,.3f}"


def ratio(value):
    return "---" if value is None else f"{value:,.2f}"


def latex_fragment(result):
    cases = result["cases"]
    by_id = {case["id"]: case for case in cases}
    family = family_cases(result)
    rows = [row for case in cases for row in case["protocols"]]
    calls = [call for row in rows for call in row["warmup"]]
    calls += [call for row in rows for r in row["rounds"] for call in r["calls"]]
    pair_count = sum(row["summary"]["complete_paired_rounds"] for row in rows)
    identical = [value for row in rows for value in row["summary"]["identical_planar_ratios"]]
    verified = sum(case["independent_replay"]["status"] == "VERIFIED" for case in cases)
    complete = sum(call["status"] == "COMPLETE" for call in calls)
    capped = len(calls)-complete
    assert (len(cases), len(rows), pair_count, len(calls), complete, capped) == (23, 46, 216, 752, 750, 2)
    assert verified == len(cases) and len(identical) == 222
    assert [case["family_n"] for case in family] == [1, 2, 4, 8, 16, 32]
    assert all(case["expected_ray_count"] == 7 for case in family)
    assert "finite_trefoil_selected_d3" not in by_id

    text = [r"% Generated by experiments/make_article_assets.py from retained measurements.",
            r"% Edit the generator, not this fragment, to preserve reproducibility.",
            r"\subsection{Protocol, pairing, and completeness}", "",
            rf"The retained run uses Python {result['python']} on the recorded Linux",
            rf"environment and contains {len(cases)} distinct supplied-sector cases,",
            rf"{len(rows)} case--protocol combinations, and {pair_count} complete measured",
            r"arrangement/planar pairs. Each small combination has five measured",
            r"rounds; the principal family at $n\ge16$ has three. A round randomly",
            r"orders the arrangement arm, the planar arm, and a second identical",
            r"planar arm. Each protocol also records an excluded warmup for each",
            r"primary arm. Source construction, expected-list derivation, ray hashing,",
            r"independent coverage replay, and result serialization are outside the",
            r"timed intervals. Native coordinate validation remains inside enumeration.", "",
            rf"There are {len(calls)} retained arm calls including warmups: {complete} complete",
            rf"and {capped} resource-capped. All complete outputs agree with their case's",
            r"canonical primitive-ray digest. Separately, the independent exhaustive",
            rf"checker returns \code{{VERIFIED}} for all {verified} benchmark cases, including",
            r"the $n=32$ case whose arrangement warmups are capped. This replay is",
            r"outside both enumeration protocols. The additional high-size capability",
            r"runs below have their own, separately reported replay outcomes.", "",
            r"For complete matched rounds $i$, the reported ratio is",
            r"\[",
            r" \rho=\operatorname{median}_i",
            r"       \left(\frac{T_i^{\mathrm{arrangement}}}{T_i^{\mathrm{planar}}}\right).",
            r"\]",
            r"The time columns show the separate median durations of the two arms.",
            r"Their quotient need not equal $\rho$: pairing is performed before",
            r"taking the median. Values above one favor the new enumerator. All",
            r"individual ratios and durations are retained; no ratio is assigned",
            r"when the baseline does not finish.", "",
            r"\subsection{The growing family and the removed work}", "",
            r"\begin{table}[htbp]",
            r"\centering\small",
            r"\setlength{\tabcolsep}{4pt}",
            r"\begin{tabular*}{\linewidth}{@{\extracolsep{\fill}}rr rrr rrr r@{}}",
            r"\toprule",
            r"& & \multicolumn{3}{c}{Prepared kernel} & \multicolumn{3}{c}{Build + enumerate} & \\",
            r"\cmidrule(lr){3-5}\cmidrule(lr){6-8}",
            r"$n$ & $t$ & Old (ms) & New (ms) & $\rho$ & Old (ms) & New (ms) & $\rho$ & Pairs\\",
            r"\midrule"]
    for case in family:
        p, f = (protocol(case, name)["summary"] for name in ("prepared", "full"))
        assert p["complete_paired_rounds"] == f["complete_paired_rounds"]
        text.append(" & ".join([str(case["family_n"]), str(case["kernel_stats"]["tetrahedra"]),
                    ms(p["medians"]["baseline"]), ms(p["medians"]["planar"]), ratio(p["median_paired_ratio"]),
                    ms(f["medians"]["baseline"]), ms(f["medians"]["planar"]), ratio(f["median_paired_ratio"]),
                    str(p["complete_paired_rounds"])])+r"\\")
    text.extend([r"\bottomrule",
            r"\end{tabular*}",
            r"\caption{Principal double-cap family, with cap types $(1,1)$ and",
            r"$t=n+2$ tetrahedra. Every complete list has seven non-link rays.",
            r"Times are median milliseconds; $\rho$ is the median matched ratio.",
            r"The pair count applies separately to each protocol. At $n=32$ there",
            r"are three completed new/new rounds per protocol and no completed",
            r"arrangement/planar pair.}",
            r"\label{tab:family-benchmark}",
            r"\end{table}", "",
            r"At $n=32$, the baseline warmup reaches the 15-second cooperative",
            r"wall-time allowance in each protocol. The driver does not repeat that",
            r"capped arm. It retains both unsuccessful warmups and reports the",
            r"complete new-arm times, with no speedup ratio. Every arm uses the",
            r"same clock policy, checked once per 256 callback invocations; the",
            r"allowance is cooperative rather than an exact preemptive timeout.", "",
            r"\begin{figure}[htbp]",
            r"\centering",
            r"\includegraphics[width=\linewidth]{figures/paired_timings.pdf}",
            r"\caption{Observed complete-call medians for the principal family.",
            r"Whiskers show the full range of measured primary-arm replicates,",
            r"not confidence intervals. Both axes use logarithmic scaling.",
            r"The arrangement curve stops at $n=16$; its $n=32$ warmup was capped",
            r"and contributes no completed point. No asymptotic exponent is fitted.}",
            r"\label{fig:paired-times}",
            r"\end{figure}", "",
            r"The retained work counters give a concrete mechanism for the growing",
            r"difference. Table~\ref{tab:family-work} records completed prepared",
            r"calls. The maintained arrangement still has increasingly many equality",
            r"candidates to inspect and nonextreme positive candidates to reject.",
            r"Across these particular family instances, the planar diagram retains",
            r"three full-dimensional minimum cells and three internal segments, and",
            r"emits seven rays. These are measured instance counts; their finite",
            r"pattern is not used as a proof of an asymptotic family formula.", "",
            r"\begin{table}[htbp]",
            r"\centering\small",
            r"\begin{tabular*}{\linewidth}{@{\extracolsep{\fill}}rrrrrrrr@{}}",
            r"\toprule",
            r"& \multicolumn{4}{c}{Maintained arrangement} & \multicolumn{3}{c}{Planar overlay}\\",
            r"\cmidrule(lr){2-5}\cmidrule(lr){6-8}",
            r"$n$ & Planes & Bases & Positive & Nonextreme & Cells & Segments & Rays\\",
            r"\midrule"])
    for case in family:
        row = protocol(case, "prepared")
        old = measured_calls(row, "baseline")
        if not old:
            continue
        new = measured_calls(row, "planar")
        old_keys = ("hyperplanes", "bases_attempted", "positive_directions", "nonextreme_directions")
        new_keys = ("minimum_cells", "skeleton_segments", "emitted_rays")
        assert all(tuple(c["stats"][k] for k in old_keys) == tuple(old[0]["stats"][k] for k in old_keys)
                   for c in old)
        assert all(tuple(c["stats"][k] for k in new_keys) == tuple(new[0]["stats"][k] for k in new_keys)
                   for c in new)
        text.append(" & ".join([str(case["family_n"])] +
                    [str(old[0]["stats"][key]) for key in old_keys] +
                    [str(new[0]["stats"][key]) for key in new_keys])+r"\\")
    text.extend([r"\bottomrule",
            r"\end{tabular*}",
            r"\caption{Exact counters from complete calls. ``Bases'' means attempted",
            r"arrangement bases; ``Positive'' includes candidates subsequently",
            r"rejected by the standard-ray rank filter. The new output has no final",
            r"rank-filter stage. Partial work at a cap is excluded from this table.}",
            r"\label{tab:family-work}",
            r"\end{table}", "",
            r"\subsection{Knot sources, controls, and timing noise}", "",
            r"For each listed frozen source, the driver maximizes",
            r"\[",
            r" (\mathbf{1}_{\dim P=2},p,k,R,\text{support})",
            r"\]",
            r"lexicographically among the declared audited raw-nullity-three candidates.",
            r"This is a reproducible",
            r"selection rule for the stated stratum, with no claim of typical-knot",
            r"performance. The declared source \code{finite_trefoil} has no such",
            r"candidate and is explicitly skipped; its interior-subdivision source",
            r"does supply an eligible case. The three selected trefoil/figure-eight",
            r"sources in Table~\ref{tab:other-benchmarks} have zero essential-disc",
            r"rays in their frozen complete reference lists. Thus they also supply",
            r"negative disc-search controls at the supplied-sector level.", "",
            r"\begin{table}[htbp]",
            r"\centering\small",
            r"\setlength{\tabcolsep}{4pt}",
            r"\begin{tabularx}{\linewidth}{@{}Xrrrrrr@{}}",
            r"\toprule",
            r"& & & \multicolumn{2}{c}{Full median (ms)} & \multicolumn{2}{c}{Paired $\rho$}\\",
            r"\cmidrule(lr){4-5}\cmidrule(lr){6-7}",
            r"Source / control & $t$ & $R$ & Old & New & Prep. & Full\\",
            r"\midrule"])
    selected = (
        ("finite_trefoil_interior_selected_d3", "Trefoil, interior subdivision"),
        ("finite_figureEight_selected_d3", "Figure-eight"),
        ("finite_figureEight_interior_selected_d3", "Figure-eight, interior subdivision"),
        ("solid_torus_sum_rp3_selected_d3", r"Solid torus $\#\mathbb{RP}^3$"),
        ("solid_torus_sum_s2xs1_selected_d3", r"Solid torus $\#(S^2\!\times S^1)$"),
        ("cap_1_2_3_selected_d3", r"\code{cap_1_2_3}"),
        ("interior_3_5_selected_d3", r"\code{interior_3_5}"),
        ("empty_sector", "Empty support"),
        ("one_type_sector", "One allowed type"),
    )
    for identifier, label in selected:
        case = by_id[identifier]
        p, f = (protocol(case, name)["summary"] for name in ("prepared", "full"))
        assert p["complete_paired_rounds"] == f["complete_paired_rounds"] == 5
        if identifier.startswith("finite_"):
            assert case["reference_essential_disc_rays"] == 0
        text.append(" & ".join([label, str(case["kernel_stats"]["tetrahedra"]),
                    str(case["expected_ray_count"]), ms(f["medians"]["baseline"]),
                    ms(f["medians"]["planar"]), ratio(p["median_paired_ratio"]),
                    ratio(f["median_paired_ratio"])])+r"\\")
    text.extend([r"\bottomrule",
            r"\end{tabularx}",
            r"\caption{Selected frozen sources and small-query controls. Every row",
            r"has five complete pairs in each protocol and an independent exhaustive",
            r"replay. ``Full'' includes kernel construction; ``Prep.'' uses a common",
            r"prebuilt kernel. Exact source identifiers and supports are in the JSON.}",
            r"\label{tab:other-benchmarks}",
            r"\end{table}", "",
            r"All nine cap-type choices at $n=2$ are included in the retained data;",
            r"the $(1,1)$ choice is already part of the principal family and is",
            r"counted once. The empty-sector control was slower in this run:",
            r"its prepared median times are approximately $1.42\,\mu\mathrm{s}$",
            r"for the baseline and $3.56\,\mu\mathrm{s}$ for the new call. At this",
            r"scale individual durations are especially sensitive to measurement",
            r"noise. Its full-call ratio below one is retained rather than discarded.", "",
            rf"The {len(identical)} identical-planar (A/A) ratios have median",
            rf"${statistics.median(identical):.4f}$, minimum ${min(identical):.4f}$, and maximum",
            rf"${max(identical):.4f}$. The two arms execute the same algorithm on the same",
            r"input, so these extremes demonstrate timing variation, not algorithmic",
            r"improvement. The minimum occurs in the empty-sector full control and",
            r"the maximum in a small cap-type full control. Every outlier remains in",
            r"the JSON. The sample sizes and this A/A spread support descriptive",
            r"comparisons for these cases, with no narrow confidence interval or",
            r"universal speedup claim.", "",
            r"\subsection{Separate capability runs and independent-replay limits}", "",
            r"The following larger principal-family cases receive one complete",
            r"new-only build-and-enumerate call each, with a 90-second cooperative",
            r"allowance. Their independent exhaustive replay has a separate",
            r"30-second allowance. These observations are neither paired timings",
            r"nor speedup measurements, and no baseline is extrapolated.", "",
            r"\begin{table}[htbp]",
            r"\centering\small",
            r"\begin{tabular*}{\linewidth}{@{\extracolsep{\fill}}rrrrrl@{}}",
            r"\toprule",
            r"$n$ & $t$ & Build (s) & Enumerate (s) & Total (s) & Independent replay\\",
            r"\midrule"])
    for case in result["capacity"]:
        assert case["status"] == "COMPLETE" and case["ray_count"] == 7
        n = int(case["id"].split("_")[2])
        replay = case["independent_replay"]
        if replay["status"] == "VERIFIED":
            status = f"Verified ({replay['seconds']:.3f} s)"
        else:
            assert replay["status"] == "INCONCLUSIVE_RESOURCE_LIMIT"
            status = "Capped (30 s); inconclusive"
        text.append(" & ".join([str(n), str(case["kernel_stats"]["tetrahedra"]),
                    f"{case['build_seconds']:.3f}", f"{case['enumeration_seconds']:.3f}",
                    f"{case['total_seconds']:.3f}", status])+r"\\")
    text.extend([r"\bottomrule",
            r"\end{tabular*}",
            r"\caption{Single new-only capability observations, all returning seven",
            r"rays. The replay duration is outside the displayed total. The $n=256$",
            r"producer finishes, but the independent complete-list replay reaches its",
            r"separate cap; its coverage replay is therefore inconclusive.}",
            r"\label{tab:capacity}",
            r"\end{table}", "",
            r"At $n=256$, all returned rays pass the producer's native coordinate",
            r"validation, and the exact producer theorem applies under its stated",
            r"hypotheses. The timed experiment does not claim a completed independent",
            r"coverage replay for that case. This distinction exposes a practical",
            r"next target: after reducing enumeration work, dense preparation and",
            r"independent verification can become the dominant costs.", "",
            r"The authoritative observations, source hashes, canonical ray digests,",
            r"counters, arm orders, warmups, and limits are in",
            r"\code{results/paired_benchmark.json}; the compact comparison table is",
            r"\code{results/paired_benchmark.csv}. The reproduction driver is",
            r"\code{experiments/benchmark.py}. Figures and this input fragment are",
            r"regenerated by \code{experiments/make_article_assets.py}. Finite timing",
            r"data are used to evaluate the implementation on the declared inputs;",
            r"the asymptotic conclusions come from the proved bounds, and the global",
            r"unknot-recognition coverage problem remains separate.", ""])
    return "\n".join(text)


def main():
    result = json.loads(RESULTS.read_text())
    assert result["schema"] == "planar-sector-paired-benchmark-v1"
    FIGURES.mkdir(parents=True, exist_ok=True)
    date = datetime.fromisoformat(result["started_utc"])
    minimum_overlay(date)
    timing_figure(result, date)
    fragment = ROOT / "article" / "benchmark_details.tex"
    fragment.write_text(latex_fragment(result))
    print(f"Generated {fragment.relative_to(ROOT)}")
    print("Generated exact overlay PDF/PNG/data and paired timing PDF/PNG in article/figures/")


if __name__ == "__main__":
    main()

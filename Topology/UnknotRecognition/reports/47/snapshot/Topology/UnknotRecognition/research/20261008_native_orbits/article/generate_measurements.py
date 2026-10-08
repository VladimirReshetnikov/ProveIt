"""Regenerate article tables and vector figures from the delivered raw data."""
from pathlib import Path
import json
from statistics import median
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
FAST = HERE.parents[2] / "fast"
seed = json.loads((FAST / "results/two_meridian_search_20261008.json").read_text())
normal = json.loads((FAST / "results/normal_orbits_20261008.json").read_text())
incidence = json.loads((FAST / "results/interval_incidence_20261008.json").read_text())
names = {"kinoshita_terasaka": "Kinoshita--Terasaka", "figure_eight": "Figure-eight",
         "hard_unknot_8": "Hard unknot 8", "gordian": "Gordian", "conway": "Conway",
         "trefoil": "Trefoil"}
lines = [r"\begingroup\small\setlength{\LTpre}{6pt}\setlength{\LTpost}{6pt}", r"\begin{longtable}{@{}lrrrrrr@{}}",
         r"\toprule Diagram & $n$ & Old trials & New trials & Old ms & New ms & Paired ratio\\\midrule\endhead"]
for row in seed["rows"]:
    samples = row["standalone"]["samples"]
    base = [s["measurements"]["baseline"] for s in samples]
    new = [s["measurements"]["optimized"] for s in samples]
    ratio = median(a["seconds"] / b["seconds"] for a, b in zip(base, new))
    title = names.get(row["name"], row["name"])
    lines.append(f"{title} & {row['crossings']} & {base[0]['statistics']['attempts']:,} & "
                 f"{new[0]['statistics']['attempts']:,} & {1000*median(a['seconds'] for a in base):.3f} & "
                 f"{1000*median(a['seconds'] for a in new):.3f} & {ratio:.3f}\\\\")
lines += [r"\bottomrule\end{longtable}\endgroup"]
(HERE / "seed_table.tex").write_text("\n".join(lines) + "\n")

rows = normal["rows"]
lines = [r"The layered-solid-torus family is inherited from the preceding reports.",
         r"Its supplied meridian vector has Fibonacci growth; no claim of a new family is made.",
         r"Each measured vector is certified as one orientable disc with one essential boundary circle.",
         r"The following timings use three shuffled rounds, with raw samples retained.",
         r"\begin{center}\small\begin{tabular}{@{}rrrrrr@{}}",
         r"\toprule $t$ & Disc-count bits & Count ms & Proof ms & Replay ms & Proof KiB\\\midrule"]
for row in rows:
    times = row["median_seconds"]
    lines.append(f"{row['tetrahedra']} & {row['summary']['normal_discs'].bit_length()} & "
                 f"{times['native_count']*1000:.3f} & {times['native_proof']*1000:.3f} & "
                 f"{times['native_replay']*1000:.3f} & {row['proof_json_bytes']/1024:.1f}\\\\")
lines += [r"\bottomrule\end{tabular}\end{center}",
          r"At $t=128$, the input has 384 nonempty stacks, 764 surface face bands, and", 
          r"\[N=2\,791\,715\,456\,571\,051\,233\,611\,642\,548\]",
          r"normal discs. The ordinary orbit query needs 390 cycles and 41,643 transmissions;",
          r"its orientation lift needs 779 cycles. These are algorithmic counts, not sheet counts.",
          r"The full five-query certificate occupies 13,504,926 bytes as compact JSON.",
          r"The size is charged explicitly; binary geometry does not make certificate transport free.",
          "",
          r"\begin{figure}[ht]\centering\includegraphics[width=\textwidth]{figures/normal_scaling.pdf}",
          r"\caption{Measured native topology costs and ordinary orbit work on supplied Fibonacci",
          r"meridian vectors. Lines join measured points only. They are not a fitted universal",
          r"complexity law.}\end{figure}",
          "",
          r"The small explicit controls are often faster. At $t=12$, literal polygon assembly",
          r"takes 9.659 ms versus 29.744 ms for the new aggregate query; Regina's component",
          r"routine takes 0.906 ms. At $t=16$, the literal control takes 98.205 ms versus",
          r"80.155 ms, while Regina remains faster at 3.226 ms. Those controls return a",
          r"different output protocol, and these figures are not claimed as certificate-level speedups.",
          r"Both explicit controls are restricted to at most 20,000 discs in the final benchmark.",
          r"Regina's documented \code{components()} routine explicitly constructs normal discs",
          r"\cite{reginadoc}; an initial uncapped diagnostic reached the 64-tetrahedron case",
          r"and raised \code{MemoryError: std::bad\_alloc}. Its aborted log is retained separately",
          r"and contributes no primary timing ratio. We then applied the same finite-oracle",
          r"cap to both explicit controls and reran the complete source-guarded benchmark.",
          r"The large rows therefore establish native compressed completion and proof replay,",
          r"not a fabricated ratio against a censored explicit computation."]
(HERE / "normal_results.tex").write_text("\n".join(lines) + "\n")

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.labelcolor": "#193044", "text.color": "#193044",
                     "axes.titleweight": "bold", "savefig.bbox": "tight"})
(HERE / "figures").mkdir(exist_ok=True)
gordian = next(row for row in seed["rows"] if row["name"] == "gordian")
keys = ["baseline", "stamped", "candidate_only", "optimized"]
labels = ["Original dense search", "Generation arrays", "+ Prerequisite pairs", "+ Closed-set pruning"]
values = [1000 * median(s["measurements"][key]["seconds"] for s in gordian["standalone"]["samples"]) for key in keys]
fig, ax = plt.subplots(figsize=(8.8, 3.6))
ax.barh(labels, values, color=["#93a4b2", "#507da1", "#259b9f", "#087579"], height=.62)
ax.invert_yaxis(); ax.set_xscale("log"); ax.set_xlim(.8, 700)
ax.set_xlabel("Standalone class-query time (ms, logarithmic scale)")
for i, value in enumerate(values):
    ax.text(value * 1.08, i, f"{value:.3f} ms", va="center")
ax.grid(axis="x", alpha=.2); ax.set_axisbelow(True)
fig.tight_layout(); fig.savefig(HERE / "figures/seed_ablation.pdf"); plt.close(fig)

fig, (left, right) = plt.subplots(1, 2, figsize=(10.5, 4.1))
x = [row["tetrahedra"] for row in rows]
for key, title, style, color in [("native_count", "Count", "o-", "#285d87"),
                                  ("native_proof", "Proof production", "s--", "#8095a8"),
                                  ("native_replay", "Independent replay", "^-", "#008785")]:
    left.plot(x, [r["median_seconds"][key] for r in rows], style, color=color, label=title, lw=1.8)
left.set_xscale("log", base=2); left.set_yscale("log")
left.set_xlabel("Tetrahedra"); left.set_ylabel("Seconds")
left.set_title("Full native topology query"); left.legend(fontsize=8)
right.plot(x, [r["orbit_stats"]["components"]["cycles"] for r in rows], "o-", color="#008785", label="Cycles")
right.plot(x, [r["orbit_stats"]["components"]["transmissions"] for r in rows], "s-", color="#285d87", label="Transmissions")
right.set_xscale("log", base=2); right.set_yscale("log")
right.set_xlabel("Tetrahedra"); right.set_ylabel("Operations")
right.set_title("Ordinary component query"); right.legend(fontsize=8)
for ax in (left, right): ax.grid(alpha=.18); ax.set_axisbelow(True)
fig.tight_layout(); fig.savefig(HERE / "figures/normal_scaling.pdf"); plt.close(fig)
print("Generated seed table, normal results, and two vector figures from raw data.")

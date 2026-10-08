#!/usr/bin/env python3
"""Regenerate measured tables, aggregates, and marked article passages.

Run after benchmark.py. The benchmark contracts and case names are deliberately
fixed; an incompatible result file raises an exception rather than silently
inserting unrelated data into the paper.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ARMS = ("selected_line", "shear_structured", "shear_flow")


def main() -> None:
    benchmark = json.loads((ROOT / "results/benchmark.json").read_text())
    synthetic = benchmark["synthetic"]
    rows = []
    for record in synthetic:
        _, _, k, h = record["name"].split("-")
        k, h = k[1:], h[1:]
        m, output = record["medians_ms"], record["outputs"]
        rows.append(
            f"{k} & {h} & {m['selected_line']:.3f} & "
            f"{m['shear_structured']:.3f} & {m['shear_flow']:.3f} & "
            f"{output['selected_line']['phases']}/"
            f"{output['shear_structured']['phases']} & "
            f"{m['selected_line']/m['shear_structured']:.2f}\\\\"
        )
    synthetic_table = "\n".join(rows)
    (ROOT / "tables/synthetic.tex").write_text(synthetic_table + "\n")

    rows, aggregates = [], {}
    for stage, label in ((0, "Raw presentations"), (1, "After singleton elimination")):
        records = [r for r in benchmark["braid_stages"]
                   if r["name"].endswith("-" + str(stage))]
        totals = {arm: sum(r["medians_ms"][arm] for r in records) for arm in ARMS}
        aggregates[str(stage)] = totals
        wins = sum(r["outputs"]["shear_structured"]["length"] <
                   r["outputs"]["selected_line"]["length"] for r in records)
        rows.append(
            f"{label} & {wins}/{len(records)} & "
            f"{totals['selected_line']:.3f} & {totals['shear_structured']:.3f} & "
            f"{totals['shear_flow']:.3f}\\\\"
        )
    braid_table = "\n".join(rows)
    (ROOT / "tables/braid.tex").write_text(braid_table + "\n")
    (ROOT / "results/stage_aggregates.json").write_text(
        json.dumps(aggregates, indent=2) + "\n"
    )

    totals = benchmark["summary"]["braid_sum_medians_ms"]
    braid_summary = (
        "There are 5,400 measured calls in this part. Across both stages the sums are\n"
        f"${totals['selected_line']:.3f}$ ms for the selected-line baseline, "
        f"${totals['shear_structured']:.3f}$ ms for structured joint\n"
        f"optimization, and ${totals['shear_flow']:.3f}$ ms for forced flow. "
        "Thus the more powerful query\n"
        "has substantial overhead on these ordinary small inputs. The shortcuts reduce\n"
        "that overhead, but the corpus does not support replacing the default policy."
    )
    by_name = {r["name"]: r for r in synthetic}
    x = by_name["star-Z-k12-h20"]["medians_ms"]
    y = by_name["star-Z-k6-h500"]["medians_ms"]
    synthetic_summary = (
        "There are 105 measured calls. The observed phase counts agree with the\n"
        f"exact theorem: $k$ versus one. At $(k,h)=(12,20)$, medians are "
        f"${x['selected_line']:.3f}$ ms\n"
        f"and ${x['shear_structured']:.3f}$ ms, approximately "
        f"${x['selected_line']/x['shear_structured']:.2f}$ times apart. "
        "At $(6,500)$ they are\n"
        f"${y['selected_line']:.3f}$ ms and ${y['shear_structured']:.3f}$ ms, "
        f"approximately ${y['selected_line']/y['shear_structured']:.2f}$ times apart. These are\n"
        "completed synthetic-presentation measurements, not ratios against censored\n"
        "runs and not unknot-diagram benchmarks.\n\n"
        "For the identical joint query at $(6,500)$, disabling the shortcuts raises\n"
        f"the median from ${y['shear_structured']:.3f}$ ms to ${y['shear_flow']:.3f}$ ms. "
        "This isolates the cost of processing\n"
        "many capacity bits unnecessarily on structured graphs. The large integer\n"
        "sizes remain encoded throughout; no $2^{500}$-letter materialization occurs."
    )
    if (benchmark["summary"]["measured_braid_calls"] != 5400 or
            benchmark["summary"]["measured_synthetic_calls"] != 105):
        raise ValueError("Article narrative requires the documented fixed-size benchmark")
    article = (ROOT / "article.tex").read_text()
    for label, content in (
        ("BRAID TABLE", braid_table),
        ("SYNTHETIC TABLE", synthetic_table),
        ("BRAID SUMMARY", braid_summary),
        ("SYNTHETIC SUMMARY", synthetic_summary),
    ):
        pattern = re.compile(
            re.escape("% BEGIN GENERATED " + label) + r"\n.*?\n" +
            re.escape("% END GENERATED " + label), re.DOTALL
        )
        replacement = "% BEGIN GENERATED " + label + "\n" + content + "\n% END GENERATED " + label
        article, count = pattern.subn(lambda match: replacement, article)
        if count != 1:
            raise ValueError(f"Expected exactly one generated article region: {label}")
    (ROOT / "article.tex").write_text(article)


if __name__ == "__main__":
    main()

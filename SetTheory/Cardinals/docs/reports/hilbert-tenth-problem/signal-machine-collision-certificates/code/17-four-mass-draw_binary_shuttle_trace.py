#!/usr/bin/env python3
"""Reproduce a vector spacetime figure from the exported radius-six rule.

Run from any directory with Python 3 and matplotlib installed. No external
services are used. The CSV and JSON contain every configuration shown.
"""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle


HERE = Path(__file__).resolve().parent
CERTIFICATE = HERE.parent / "binary-radius6-conservation-certificate.json"
D = 9
CYCLES = 4
BASENAME = "binary-four-particle-shuttle"


def component_step(occupied: set[int]) -> set[int]:
    """Independent literal implementation used only to cross-check the table."""
    rewrites = {(0, 1): (1, 2), (0, 2): (-1, 1),
                (0, 1, 3): (-1, 1, 4), (0, 2, 4): (0, 3, 4)}
    components: list[list[int]] = []
    for x in sorted(occupied):
        if not components or x - components[-1][-1] > 2:
            components.append([x])
        else:
            components[-1].append(x)
    result: set[int] = set()
    for component in components:
        left = component[0]
        normalized = tuple(x - left for x in component)
        target = {left + x for x in rewrites.get(normalized, normalized)}
        assert not result.intersection(target)
        result.update(target)
    return result


def table_step(occupied: set[int], table: list[int]) -> set[int]:
    """Evaluate the complete radius-six neighborhood at each possible output."""
    if not occupied:
        return set()
    result = set()
    # Full radius-six light cone, independent of the tighter propagation bound.
    for x in range(min(occupied) - 6, max(occupied) + 7):
        code = sum(1 << i for i in range(13) if x + i - 6 in occupied)
        if table[code]:
            result.add(x)
    return result


def main() -> None:
    certificate_bytes = CERTIFICATE.read_bytes()
    certificate = json.loads(certificate_bytes)
    assert certificate["radius"] == 6
    table = list(map(int, certificate["rule_bits_indexed_by_window"]))
    assert len(table) == 8192
    assert table[0] == 0
    # Verify the supplied conservation potential, rather than trust its label.
    potential = certificate["potential_by_vertex"]
    assert len(potential) == 4096
    for word in range(8192):
        assert table[word] - ((word >> 6) & 1) == (
            potential[word >> 1] - potential[word & 4095])

    returns = [k * k + (2 * D - 11) * k for k in range(CYCLES + 1)]
    occupied = {0, 3, 4, D}
    trace = []
    actual_returns = []
    for t in range(returns[-1] + 1):
        assert len(occupied) == 4
        hit = occupied.intersection(range(5)) == {0, 3, 4}
        k = returns.index(t) if t in returns else None
        assert hit == (k is not None)
        if hit:
            actual_returns.append(t)
            assert occupied == {0, 3, 4, D + k}
        trace.append({"t": t, "occupied_sites": sorted(occupied),
                      "rightmost_site": max(occupied), "return_index": k})
        next_occupied = table_step(occupied, table)
        assert next_occupied == component_step(occupied)
        occupied = next_occupied
    assert actual_returns == returns

    metadata = {
        "description": "Exact table-evaluated four-particle binary shuttle trace",
        "initial_configuration": [0, 3, 4, D],
        "d": D, "cycles": CYCLES,
        "certificate_relative_path": "../" + CERTIFICATE.name,
        "certificate_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
        "rule_radius": 6,
        "return_formula": "t_k = k^2 + (2*d - 11)*k",
        "return_times": returns,
        "return_marker_positions": [D + k for k in range(CYCLES + 1)],
        "checks": {"conservation_edges": 8192,
                   "mass_four_at_each_plotted_time": True,
                   "table_matches_independent_component_rule": True,
                   "anchored_pattern_hits_match_return_formula": True},
        "trace": trace,
    }
    (HERE / (BASENAME + ".json")).write_text(json.dumps(metadata, indent=2) + "\n")
    with (HERE / (BASENAME + ".csv")).open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["t", "particle_1", "particle_2", "particle_3", "particle_4",
                         "rightmost_site", "return_index"])
        for row in trace:
            writer.writerow([row["t"], *row["occupied_sites"], row["rightmost_site"],
                             "" if row["return_index"] is None else row["return_index"]])

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 8,
        "mathtext.fontset": "dejavusans", "pdf.fonttype": 42,
        "ps.fonttype": 42, "axes.linewidth": 0.5,
    })
    ink = "#142C45"
    muted = "#52616F"
    pale = "#E8EEF3"
    fig = plt.figure(figsize=(6.0, 4.95), facecolor="white")
    ax = fig.add_axes([0.12, 0.17, 0.665, 0.625])
    ax.set_xlim(-0.6, D + CYCLES + 0.6)
    ax.set_ylim(returns[-1] + 0.6, -0.6)
    ax.xaxis.tick_top()
    ax.xaxis.set_label_position("top")
    ax.set_xticks(range(D + CYCLES + 1))
    ax.set_yticks(returns)
    ax.set_xlabel("Position $x$", fontsize=9, labelpad=8, color=ink)
    ax.set_ylabel("Time $t$", fontsize=9, labelpad=10, color=ink)
    ax.tick_params(axis="both", colors=muted, length=2.5, width=0.5,
                   labelsize=8, pad=3)
    for spine in ax.spines.values():
        spine.set_color("#AEBBC6")
    ax.spines["right"].set_visible(False)
    ax.spines["bottom"].set_visible(False)

    # Return rows are a guide only; the dark cells encode all occupancy.
    for k, t in enumerate(returns):
        ax.axhspan(t - 0.5, t + 0.5, color=pale, zorder=0, linewidth=0)
        ax.text(D + CYCLES + 1.0, t, rf"$k={k}$   $r_k={D + k}$",
                va="center", ha="left", fontsize=8, color=muted,
                clip_on=False)
    for row in trace:
        for x in row["occupied_sites"]:
            ax.add_patch(Rectangle((x - 0.32, row["t"] - 0.41), 0.64, 0.82,
                                   facecolor=ink, edgecolor="none", zorder=2))

    fig.text(0.12, 0.963, "Binary four-particle shuttle", fontsize=11,
             fontweight="semibold", color=ink, ha="left", va="top")
    fig.text(0.12, 0.923, r"$d=9$; initial support $\{0,3,4,9\}$",
             fontsize=8.5, color=muted, ha="left", va="top")
    fig.text(0.82, 0.81, "Return / marker", fontsize=7.5,
             color=muted, ha="left", va="bottom")
    fig.text(0.12, 0.107,
             r"$t_k=k^2+(2d-11)k=k^2+7k$,     $r_k=d+k$",
             fontsize=10, color=ink, ha="left", va="center")
    fig.text(0.12, 0.057, "Return intervals: 8, 10, 12, 14 steps. "
             "The right marker advances one site per cycle.",
             fontsize=8, color=muted, ha="left", va="center")
    fig.savefig(HERE / (BASENAME + ".pdf"),
                metadata={"Title": "Binary four-particle expanding shuttle",
                          "Subject": "Exact radius-six rule trace; d=9, four cycles",
                          "Creator": "draw_binary_shuttle_trace.py"})
    fig.savefig(HERE / (BASENAME + ".png"), dpi=220)
    plt.close(fig)
    print(json.dumps({"pdf": str(HERE / (BASENAME + ".pdf")),
                      "configurations": len(trace), "returns": returns,
                      "certificate_sha256": metadata["certificate_sha256"]}, indent=2))


if __name__ == "__main__":
    main()

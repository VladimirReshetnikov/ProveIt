#!/usr/bin/env python3
"""Regenerate the article tables from the preserved experiment results."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
TABLES = ROOT / "article/tables"


def number(value):
    return format(value, ",").replace(",", r"\,")


def write_table(name, columns, header, rows):
    text = "\\begin{center}\n\\small\n\\begin{tabular}{" + columns + "}\n\\toprule\n"
    text += header + "\\\\\n\\midrule\n"
    text += "\n".join(" & ".join(map(str, row)) + "\\\\" for row in rows)
    text += "\n\\bottomrule\n\\end{tabular}\n\\end{center}\n"
    (TABLES / name).write_text(text)


def main():
    TABLES.mkdir(exist_ok=True)
    a = json.loads((ROOT / "results/affine_modular_benchmarks.json").read_text())
    g = json.loads((ROOT / "results/normal_interval_verification.json").read_text())
    s = json.loads((ROOT / "results/scalar_inheritance_20261008.json").read_text())
    counts = [(r"Scalar merges, $m\le48$", 38024),
              (r"Two-coordinate merges, $m\le8$", 8772),
              (r"Two-generator scalar cosets, $m\le10$", 3025),
              (r"Scalar congruences, $m\le24$", 4900),
              (r"$2\times2$ systems, $m\le4$", 4890),
              (r"One-variable one-seam families, $m\le6$", 2275),
              ("Seeded dense random families", 2000)]
    assert sum(value for _, value in counts) == 63886
    write_table("arithmetic_cases.tex", "lr", "Independent arithmetic comparison & Cases",
                [(name, number(value)) for name, value in counts] +
                [(r"\textbf{Total}", r"\textbf{63\,886}")])
    rows = []
    for row in a["records"]:
        if row["case"] == "prime_power_saturation" and row["exponent_e"] not in (1024, 16384, 65536):
            continue
        label = r"$2+z$, no seams" if row["case"] == "prime_power_saturation" else "Dense constrained"
        rows.append([label, number(row["modulus_bits"]),
                     f'{row["variables"]}/{row["constraints"]}/{row["holonomies"]}',
                     row["minimum_components"], f'{row["median_seconds"]:.6f}'])
    write_table("arithmetic_timings.tex", "lrrrr", r"Family & Modulus bits & $n/q/\beta$ & Min. & Seconds", rows)
    rows = [[row["tetrahedra"], number(row["coordinate_bits"]), row["surface_face_bands"],
             row["prism_face_bands"], row["prism_to_residual_contacts"], row["local_residual_cells"],
             f'{1000 * row["median_seconds"]:.3f}'] for row in g["scaling"]["layered_tori"]]
    write_table("normal_scaling.tex", "rrrrrrr", "$t$ & Coordinate bits & Surface & Prism & Contacts & Residue & ms", rows)
    rows = []
    for row in s["copies"]:
        n = row["copies"]
        rows.append([n, number(n*(n+1)*(2*n+1)//3-2), number(2*n*n), n-1, 1,
                     f'{row["median_reference_over"]["inheritance"]:.3f}',
                     f'{row["median_reference_over"]["control"]:.3f}'])
    write_table("copy_scaling.tex", "rrrrrrr", "$r$ & Old equations & Inherited & Old solves & New & Ratio & A/A", rows)
    rows = [[row["degree"]] + [f'{row["median_reference_over"][key]:.3f}' for key in
             ("inheritance", "locality", "combined", "monogenic", "control")]
            for row in s["fields"] if row["degree"] in (8, 10, 12) and row["mixing"] == "dense"]
    assert len(rows) == 3
    write_table("field_scaling.tex", "rrrrrr", "$r$ & Inheritance & Local stop & Both & One generator & A/A", rows)
    labels = {"trefoil": "Trefoil", "conway": "Conway", "kinoshita_terasaka": "Kinoshita--Terasaka",
              "hard_unknot_8": "Hard unknot 8", "stress_braid5_36": "Stress braid 5/36", "torus_3_5": "$T(3,5)$"}
    rows = []
    for row in s["natural"]:
        ratios = row["median_reference_over"]
        old = row["outcomes"]["baseline"]["stats"]["fitting_cache_misses"]
        new = row["outcomes"]["inheritance"]["stats"]["fitting_endomorphism_computations"]
        rows.append([labels[row["name"]], row["crossings"], f'{1000*row["median_seconds"]["baseline"]:.3f}',
                     f'{ratios["inheritance"]:.3f}', f'{ratios["monogenic"]:.3f}', f'{ratios["control"]:.3f}',
                     f'{old}\\,$\\to$\\,{new}'])
    write_table("natural_scaling.tex", "lrrrrrl", "Diagram & Crossings & Old ms & Inherit & One gen. & A/A & Solves", rows)
    print("Regenerated six article tables from the preserved measurements.")


if __name__ == "__main__":
    main()

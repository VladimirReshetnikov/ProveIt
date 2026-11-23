#!/usr/bin/env python3
"""Regenerate the exact declaration inventory from the nine proof chapters.

One row means one labeled theorem/lemma/proposition/corollary declaration.
Definitions, remarks, displayed equations, and consequences inside a single
declaration are not counted separately. This inventories the authored human
arguments; it does not assert Lean compilation or machine-checked proofs.
"""
from __future__ import annotations
from collections import Counter
import csv
import json
from pathlib import Path
import re


ROOT=Path(__file__).resolve().parents[1]
CHAPTERS=[
    ("foundation","Arithmetic foundation"),
    ("elimination","Elementary geometry transfer"),
    ("affine","Incidence and affine geometry"),
    ("triangles","Metric geometry and triangles"),
    ("circles","Circles and constructions"),
    ("polygons","Polygonal area and quadrilaterals"),
    ("solids","Euclidean space and solids"),
    ("obstructions","Construction obstructions"),
    ("limits","Finite observations and boundary"),
]
CATEGORIES={
    "exact_geometry":("Exact geometry and construction results",
        "Finite algebraic coordinates, geometric data, or construction traces"),
    "arithmetic_infrastructure":("Arithmetic and transfer infrastructure",
        "Finite arithmetic, fields, elimination, or degree certificates"),
    "observation_geometry":("Finite-observation geometry",
        "Explicit polygonal or prism enclosures and fixed observation recipes"),
    "observation_infrastructure":("Observation infrastructure",
        "Rationalization or finite-sum estimates for the named observations"),
    "external_metatheory":("External computability obstruction",
        "Metatheoretic nondecidability; not an exact iPRA Euclidean theorem"),
}
ARTICLE="https://en.wikipedia.org/wiki/"


def category(chapter,label):
    if label=="lim:equality-boundary":
        return "external_metatheory"
    if label in {"lim:rationalize","lim:sums"}:
        return "observation_infrastructure"
    if chapter=="limits":
        return "observation_geometry"
    if chapter in {"foundation","elimination"} or label=="obs:degree":
        return "arithmetic_infrastructure"
    return "exact_geometry"


def representation(chapter,label):
    if label=="lim:equality-boundary":
        return ("external_computability_on_uniform_PR_names", "External metatheory")
    if label=="lim:polygons":
        return ("finite_algebraic_enclosures_at_each_stage", "Algebraic brackets")
    if label=="lim:sums":
        return ("finite_rational_sums_with_explicit_modulus", "Finite rational sums")
    if chapter=="limits":
        return ("fixed_PR_rational_observation_names", "PR interval names")
    if label=="obs:degree":
        return ("finite_number_field_bases_and_quadratic_towers", "Finite field bases")
    if chapter=="obstructions":
        return ("finite_construction_traces_over_the_rational_frame", "Construction traces")
    if chapter=="foundation":
        return ("finite_natural_rational_and_algebraic_codes", "Arithmetic codes")
    if chapter=="elimination":
        return ("finite_polynomial_sign_data_and_fixed_formula_schemata", "Finite sign data")
    if label=="tri:ssa":
        return ("explicit_rational_plane_coordinates", r"Exact $\Q^2$")
    if label=="aff:desargues":
        return ("homogeneous_algebraic_triples", r"Homogeneous $\K^3$")
    if chapter=="polygons":
        return ("finite_algebraic_vertex_and_triangulation_lists", "Finite polygons")
    if label=="sol:gram":
        return ("finite_dimensional_algebraic_coordinate_lists", r"Finite $\K^d$")
    if chapter=="solids":
        return ("finite_algebraic_spatial_polyhedral_or_tetrahedral_data", "Finite spatial data")
    if label=="circ:construction-arithmetic":
        return ("finite_straightedge_compass_construction_traces", "Construction traces")
    return ("exact_real_algebraic_plane_coordinates", r"Exact $\K^2$")


def neighborhood(chapter,label):
    """Thematic entry pages, not claims of verbatim theorem occurrence."""
    if chapter in {"foundation","elimination"}:
        return ("Supporting arithmetic", [])
    if label=="lim:equality-boundary":
        return ("Scope boundary", [])
    if label in {"lim:rationalize","lim:sums"}:
        return ("Supporting analysis", [])
    if chapter=="obstructions":
        return ("Constructions", [ARTICLE+"Straightedge_and_compass_construction"])
    if chapter=="limits":
        if label in {"lim:polygons","lim:circle"}:
            return ("Circle", [ARTICLE+"Circle"])
        return ("Solid geometry", [ARTICLE+"Solid_geometry"])
    if label in {"sol:five-types","sol:realizations"}:
        return ("Platonic solids", [ARTICLE+"Platonic_solid"])
    if chapter=="solids":
        return ("Space; solids", [ARTICLE+"Euclidean_space",ARTICLE+"Solid_geometry"])
    if chapter=="polygons":
        return ("Elements; area", [ARTICLE+"Euclid%27s_Elements",ARTICLE+"Euclidean_geometry"])
    if label in {"aff:parallel"}:
        return ("Parallel postulate", [ARTICLE+"Parallel_postulate"])
    if label=="aff:ceva":
        return ("Ceva", [ARTICLE+"Ceva%27s_theorem"])
    if label=="aff:menelaus":
        return ("Menelaus", [ARTICLE+"Menelaus%27s_theorem"])
    if chapter=="affine":
        return ("Analytic geometry", [ARTICLE+"Analytic_geometry"])
    if label=="tri:heron":
        return ("Heron", [ARTICLE+"Heron%27s_formula"])
    if label=="tri:bisector":
        return ("Angle bisector", [ARTICLE+"Angle_bisector_theorem"])
    if label=="tri:nine-point":
        return ("Nine-point circle", [ARTICLE+"Nine-point_circle"])
    if label=="tri:pythagoras":
        return ("Pythagoras", [ARTICLE+"Pythagorean_theorem"])
    if chapter=="triangles":
        return ("Main; Elements", [ARTICLE+"Euclidean_geometry",ARTICLE+"Euclid%27s_Elements"])
    if label=="circ:butterfly":
        return ("Butterfly", [ARTICLE+"Butterfly_theorem"])
    if label in {"circ:elementary-constructions","circ:perpendicular-construction","circ:construction-arithmetic"}:
        return ("Constructions", [ARTICLE+"Straightedge_and_compass_construction"])
    if label.startswith("circ:ptolemy"):
        return ("Main; circle", [ARTICLE+"Euclidean_geometry",ARTICLE+"Circle"])
    return ("Circle", [ARTICLE+"Circle"])


def plain_title(title):
    text=re.sub(r"\s+"," ",title.strip())
    text=text.replace(r"\pi","pi").replace(r"\ipra{}","iPRA")
    text=text.replace("$","").replace("--","-")
    return text


def tex_escape(text):
    return "".join({"\\":r"\textbackslash{}","&":r"\&","%":r"\%","$":r"\$",
        "#":r"\#","_":r"\_","{":r"\{","}":r"\}","~":r"\textasciitilde{}",
        "^":r"\textasciicircum{}"}.get(c,c) for c in text)


def extract():
    pattern=re.compile(r"\\begin\{(theorem|lemma|proposition|corollary)\}(?:\s*\[([^\]]*)\])?")
    rows=[]
    seen={}
    for chapter,chapter_title in CHAPTERS:
        path=ROOT/"chapters"/(chapter+".tex")
        source=path.read_text(encoding="utf-8")
        declarations=list(pattern.finditer(source))
        for position,match in enumerate(declarations):
            kind,title=match.group(1),match.group(2)
            assert title, f"Untitled {kind} in {path}"
            ending=source.find(r"\end{"+kind+"}",match.end())
            assert ending>=0, f"Unterminated {kind} in {path}"
            body=source[match.end():ending]
            labels=re.findall(r"\\label\{([^}]+)\}",body)
            labels=[x for x in labels if x.split(":",1)[0] in {"found","qe","aff","tri","circ","poly","sol","obs","lim"}]
            assert len(labels)==1, f"Expected one declaration label for {title!r}: {labels}"
            label=labels[0]
            assert label not in seen, f"Duplicate declaration label {label}"
            seen[label]=str(path)
            following=declarations[position+1].start() if position+1<len(declarations) else len(source)
            assert r"\begin{proof}" in source[ending:following], f"No proof environment after {label}"
            category_code=category(chapter,label)
            rep_code,rep_tex=representation(chapter,label)
            source_area,urls=neighborhood(chapter,label)
            row={
                "ordinal":len(rows)+1,"label":label,"environment":kind,
                "title":plain_title(title),"title_tex":re.sub(r"\s+"," ",title.strip()),
                "chapter":chapter,"chapter_title":chapter_title,
                "source_file":f"chapters/{chapter}.tex",
                "source_line":source.count("\n",0,match.start())+1,
                "category":category_code,"category_description":CATEGORIES[category_code][0],
                "representation":rep_code,"representation_tex":rep_tex,
                "source_neighborhood":source_area,"neighborhood_urls":urls,
                "human_argument_included":True,
                "new_lean_compiled":False,
                "lean_status":"Uncompiled candidate source and/or formalization outline; no completed full proof claimed",
                "external_metatheoretic_obstruction":label=="lim:equality-boundary",
                "fixed_formula_transfer_schema":label=="qe:transfer",
                "counted_as_exact_geometry":category_code=="exact_geometry",
            }
            if label=="lim:equality-boundary":
                row["scope_note"]="External uniform computability obstruction; not an exact iPRA Euclidean theorem."
            elif chapter=="limits":
                row["scope_note"]="Finite-stage enclosure or fixed PR observation schema; not unrestricted real-name decision."
            elif label=="qe:transfer":
                row["scope_note"]="An externally indexed fixed-formula transfer schema; no internal universal arithmetic truth predicate."
            elif label in {"sol:five-types","sol:realizations"}:
                row["scope_note"]="Five admissible face-vertex types or their exact realizations; no separate global rigidity theorem."
            else:
                row["scope_note"]="Read all validity, nondegeneracy, orientation, sign, and representation hypotheses in the declaration."
            rows.append(row)
    # Check all labels in every authored chapter, not just the inventory rows.
    all_labels={}
    for path in sorted((ROOT/"chapters").glob("*.tex")):
        if path.name=="inventory.tex":
            continue
        for label in re.findall(r"\\label\{([^}]+)\}",path.read_text(encoding="utf-8")):
            assert label not in all_labels, f"Duplicate report label {label}: {all_labels.get(label)} and {path}"
            all_labels[label]=path.name
    assert "sec:inventory" not in all_labels, "Generated inventory section label would collide"
    all_labels["sec:inventory"]="inventory.tex (generated)"
    return rows,len(all_labels)


def make_tex(rows,chapter_counts,category_counts):
    N=len(rows)
    lines=[r"\section{Proof inventory and representation ledger}",r"\label{sec:inventory}",
        f"The inventory contains {N} labeled theorem, lemma, proposition, or corollary",
        "declarations. Each declaration is counted once, even when it contains",
        "several familiar consequences. Definitions, remarks, and equations are",
        "not additional entries. This is a count of the report's human-readable",
        "arguments, not a claim of that many distinct classical named theorems",
        "or compiled Lean proofs. All new Lean sources remain uncompiled.",
        "",r"\begin{center}\small",
        r"\begin{tabular}{@{}>{\raggedright\arraybackslash}p{0.48\textwidth}r>{\raggedright\arraybackslash}p{0.40\textwidth}@{}}",
        r"\toprule Category & Count & Interpretation\\\midrule"]
    for key,(name,description) in CATEGORIES.items():
        lines.append(f"{tex_escape(name)} & {category_counts[key]} & {tex_escape(description)}\\\\")
    lines += [r"\midrule Total & "+str(N)+r" & One row per labeled declaration\\",
        r"\bottomrule\end{tabular}\end{center}","",
        r"Proposition~\ref{lim:equality-boundary} is an \emph{external metatheoretic}",
        "computability obstruction. It is explicitly excluded from the category",
        "of exact iPRA Euclidean results. The observation entries prove finite",
        "enclosures or equalities of separately specified PR rational interval",
        "names; they do not decide equality for arbitrary real names.",
        r"The transfer result in Theorem~\ref{qe:transfer} is indexed by a fixed",
        "formula, rather than an internal universal truth predicate.","",
        r"\begin{center}\small\begin{tabular}{@{}lr@{}}",
        r"\toprule Chapter & Declarations\\\midrule"]
    for chapter,title in CHAPTERS:
        lines.append(f"{tex_escape(title)} & {chapter_counts[chapter]}\\\\")
    lines += [r"\bottomrule\end{tabular}\end{center}","",
        "In the detailed ledger, the source-area column is a thematic route",
        "through the requested article neighborhood, not a claim that every",
        "statement is printed verbatim on the main article. Supporting arithmetic",
        "and analysis entries supply the interpretation used by the geometric",
        "proofs. The machine-readable CSV and JSON retain the stable labels,",
        "source files, declaration kinds, categories, scope notes, and entry-page",
        r"URLs: \texttt{sources/theorem\_inventory.csv} and",
        r"\texttt{sources/theorem\_inventory.json}.","",
        r"{\small\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.13}",
        r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.07\textwidth}>{\raggedright\arraybackslash}p{0.51\textwidth}>{\raggedright\arraybackslash}p{0.19\textwidth}>{\raggedright\arraybackslash}p{0.18\textwidth}@{}}",
        r"\toprule Ref. & Result & Representation & Source area\\\midrule",
        r"\endfirsthead",
        r"\multicolumn{4}{@{}l}{\textit{Proof inventory (continued)}}\\",
        r"\toprule Ref. & Result & Representation & Source area\\\midrule",
        r"\endhead",
        r"\midrule\multicolumn{4}{r@{}}{\textit{Continued on the next page}}\\",
        r"\endfoot",r"\bottomrule\endlastfoot"]
    last=None
    for row in rows:
        if row["chapter"]!=last:
            last=row["chapter"]
            lines.append(r"\multicolumn{4}{@{}l}{\textbf{"+tex_escape(row["chapter_title"])+"} ("+str(chapter_counts[last])+r" declarations)}\\*[2pt]")
        title=row["title_tex"]
        if row["external_metatheoretic_obstruction"]:
            title+=r" \emph{(external)}"
        lines.append(r"\ref{"+row["label"]+"} & "+title+" & "+row["representation_tex"]+" & "+tex_escape(row["source_neighborhood"])+r"\\")
    lines += [r"\end{longtable}","}",""]
    return "\n".join(lines)


def main():
    rows,global_label_count=extract()
    chapter_counts=Counter(row["chapter"] for row in rows)
    category_counts=Counter(row["category"] for row in rows)
    report={
        "schema":"euclidean-ipra-theorem-inventory-v1",
        "counting_rule":"One labeled theorem/lemma/proposition/corollary declaration per entry; no split consequences or equation counts.",
        "declaration_count":len(rows),
        "chapter_counts":{chapter:chapter_counts[chapter] for chapter,_ in CHAPTERS},
        "category_counts":{key:category_counts[key] for key in CATEGORIES},
        "label_uniqueness":{"all_authored_chapter_labels_checked":global_label_count,"unique":True},
        "all_new_lean_sources_uncompiled":True,
        "external_metatheoretic_result_labels":["lim:equality-boundary"],
        "fixed_formula_transfer_schema_labels":["qe:transfer"],
        "entry_page_semantics":"Thematic source-neighborhood routes, not claims of verbatim occurrence of every theorem on an entry page.",
        "results":rows,
    }
    sources=ROOT/"sources"
    sources.mkdir(exist_ok=True)
    (sources/"theorem_inventory.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    fields=list(rows[0])
    with (sources/"theorem_inventory.csv").open("w",encoding="utf-8",newline="") as f:
        writer=csv.DictWriter(f,fieldnames=fields)
        writer.writeheader()
        for row in rows:
            csv_row=dict(row)
            csv_row["neighborhood_urls"]=" | ".join(row["neighborhood_urls"])
            writer.writerow(csv_row)
    (ROOT/"chapters/inventory.tex").write_text(make_tex(rows,chapter_counts,category_counts),encoding="utf-8")
    print(f"Inventory: {len(rows)} declarations; all {global_label_count} authored chapter labels unique.")
    print("By chapter: "+", ".join(f"{c}={chapter_counts[c]}" for c,_ in CHAPTERS))
    print("By category: "+", ".join(f"{c}={category_counts[c]}" for c in CATEGORIES))


if __name__=="__main__":
    main()

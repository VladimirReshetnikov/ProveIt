#!/usr/bin/env python3
"""Reproduce and verify the source inventory for the q-series mega-merge.

The reviewed ``source_concordance.csv`` contains editorial decisions which a
text extractor cannot infer.  This program therefore treats the ten source
columns as immutable, reconstructs them from the commit pinned by
``MERGE_SOURCE_REVISION``, and compares them with the checked-in concordance.
It never overwrites the reviewed CSV.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


RESULT_KINDS = (
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "conjecture",
    "problem",
    "researchproblem",
    "definition",
    "algorithm",
    "computationalresult",
    "example",
)
PROVED_KINDS = {"theorem", "proposition", "lemma", "corollary"}
SOURCE_FIELDS = (
    "source_key",
    "source_package",
    "source_file",
    "source_line",
    "source_label",
    "source_kind",
    "source_title",
    "source_chapter",
    "source_section_path",
    "source_proof_present",
)
EDITORIAL_FIELDS = (
    "canonical_label",
    "canonical_status",
    "disposition_notes",
)
ALL_FIELDS = SOURCE_FIELDS + EDITORIAL_FIELDS

BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(RESULT_KINDS) + r")\}"
    r"(?:\[(?P<title>.*?)\])?",
    re.DOTALL,
)
LEADING_LABEL_RE = re.compile(r"^\s*\\label\{([^}]+)\}")
PROOF_RE = re.compile(r"\\begin\{(?:proof|proofidea)\}")
SECTION_RE = re.compile(
    r"\\(?P<level>part|chapter|section|subsection)\*?"
    r"\{(?P<title>.*?)\}",
    re.DOTALL,
)
COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")
Q_STATUS_RE = re.compile(
    r"\\Cref\{(?P<labels>[^}]+)\}\s*&\s*"
    r"\\status(?P<status>exact|partial|none|na)\b",
    re.DOTALL,
)

AUDIT_DIR = Path(__file__).resolve().parent
PACKAGE_ROOT = AUDIT_DIR.parent
PIN_FILE = AUDIT_DIR / "MERGE_SOURCE_REVISION"
CONCORDANCE = PACKAGE_ROOT / "source_concordance.csv"
INVERSE_CONCORDANCE = PACKAGE_ROOT / "theorem_concordance.csv"
REPOSITORY_SOURCE_ROOT = Path(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/exponents-and-q-series"
)

# Paths are deliberately historical and relative to REPOSITORY_SOURCE_ROOT.
# Do not replace them by the post-merge package paths.
SOURCE_GROUPS = (
    (
        "q_pochhammer_q_binomial_monograph",
        "Q",
        (
            "q-pochhammer-and-inversion/q_pochhammer_q_binomial_monograph/"
            "q_pochhammer_q_binomial_monograph.tex",
        ),
        276,
    ),
    (
        "inverse_q_analogs_and_series",
        "inverse",
        tuple(
            "q-pochhammer-and-inversion/inverse_q_analogs_and_series/chapters/"
            + name
            for name in (
                "00_scope_status_and_normalizations.tex",
                "01_universal_inversion.tex",
                "02_finite_q_pochhammer.tex",
                "03_infinite_q_pochhammer.tex",
                "04_gaussian_multinomial.tex",
                "05_q_special_functions.tex",
                "06_cyclotomic_fabius.tex",
                "07_certification_and_frontiers.tex",
                "08_reference_appendices.tex",
            )
        ),
        103,
    ),
    (
        "q_series_from_first_principles",
        "guides",
        (
            "general-q-series-guides/q_series_from_first_principles/"
            "q_series_from_first_principles.tex",
        ),
        43,
    ),
    (
        "q_series_monograph",
        "guides",
        (
            "general-q-series-guides/q_series_monograph/q_series_monograph.tex",
        ),
        62,
    ),
    (
        "q_series_proof_article",
        "guides",
        (
            "general-q-series-guides/q-series-proof-oriented-article/"
            "q_series_proof_article.tex",
        ),
        63,
    ),
)
EXPECTED_GROUP_COUNTS = {"Q": 276, "inverse": 103, "guides": 168}
EXPECTED_TOTAL = 547

GUIDE_PACKAGE_ALIASES = {
    "F": "q_series_from_first_principles",
    "M": "q_series_monograph",
    "A": "q_series_proof_article",
}

# Reviewed statement-level comparison of all 168 guide environments.  The
# fourth field is a stable machine disposition; prose in the CSV is generated
# from it so that the mapping is audited in one place rather than copied by
# hand into the extractor and checker independently.
GUIDE_MAP_DATA = r"""
F,102,qg:def-qshifted-factorial,merged_duplicate_Q_definition
F,126,thm:poch-entire,merged_into_stronger_Q
F,148,qg:def-gaussian-coefficient,merged_duplicate_Q_definition
F,156,thm:qpascal,merged_into_stronger_Q
F,175,thm:finite-qbinomial,merged_into_stronger_Q
F,197,thm:reciprocal-finite,merged_equivalent_index_shift
F,218,thm:infinite-qbinomial,merged_into_stronger_Q
F,235,cor:euler-infinite,merged_duplicate
F,252,qg:def-basic-hypergeometric-series,merged_duplicate_Q_definition
F,263,thm:heine,merged_duplicate
F,298,thm:q-gauss,merged_duplicate
F,315,cor:q-chu,merged_duplicate
F,336,qg:lem-euler-telescope,merged_into_A478_canonical
F,359,thm:q-pfaff,merged_duplicate
F,413,qg:def-partition,merged_into_A1279_canonical
F,417,thm:partition-products,merged_weaker
F,432,prop:bounded-partitions,merged_duplicate
F,440,cor:durfee-all,merged_duplicate
F,451,thm:partition-products,merged_weaker
F,471,thm:jtp,merged_duplicate
F,508,qg:def-ramanujan-theta|qg:prop-ramanujan-product,split_and_merged_into_A1195_A1203
F,528,thm:pentagonal,merged_duplicate
F,546,cor:euler-partition-recurrence,merged_duplicate
F,580,qg:prop-theta-products|qg:thm-theta-eta-modular,split_and_merged_into_stronger_A
F,620,qg:thm-poisson,merged_into_A1047_canonical
F,639,qg:lem-gaussian-fourier,merged_into_stronger_A1074
F,656,qg:thm-jacobi-imaginary,merged_into_stronger_A1092
F,688,qg:thm-theta-eta-modular,merged_into_stronger_A1148
F,716,qg:prop-squares-theta,retained_new
F,734,qg:def-bailey-pair,merged_duplicate_Q_definition
F,745,lem:qdiff-annihilation,merged_into_stronger_Q
F,763,thm:bailey-inversion,merged_into_stronger_Q
F,804,cor:unit-bailey-pairs,merged_into_stronger_Q
F,821,qg:thm-bailey-lemma,merged_into_A1757_canonical
F,878,thm:bailey-limit-finite,merged_duplicate
F,894,cor:bailey-limit-infinite,merged_duplicate
F,921,qg:lem-bailey-lowering,retained_stronger_new
F,965,thm:rogers-ramanujan,merged_duplicate
F,1030,qg:cor-rr-partitions,merged_into_stronger_A1988
F,1062,qg:thm-rrcf,merged_into_A2043_canonical
F,1118,qg:lem-bailey-chain-iterate,retained_stronger_new
F,1138,qg:thm-andrews-gordon,retained_stronger_new
F,1251,thm:rogers-ramanujan,merged_derived_modulus5
M,130,qg:def-qshifted-factorial,merged_duplicate_Q_definition
M,153,thm:poch-entire,merged_into_stronger_Q
M,167,qg:def-gaussian-coefficient,merged_duplicate_Q_definition
M,175,thm:qpascal,merged_into_stronger_Q
M,204,thm:finite-qbinomial,merged_weaker
M,220,cor:weighted-subsets,merged_duplicate
M,232,thm:infinite-qbinomial,merged_duplicate
M,262,cor:euler-infinite,merged_duplicate
M,284,thm:reciprocal-finite,merged_equivalent_index_shift
M,300,thm:q-cauchy,merged_duplicate
M,321,qg:def-basic-hypergeometric-series,merged_duplicate_Q_definition
M,332,thm:heine,merged_duplicate
M,366,thm:q-gauss,merged_duplicate
M,384,cor:q-chu,merged_duplicate_first_qChu
M,401,prop:qchu2-by-reversal,merged_duplicate_second_qChu
M,437,lem:cauchy-II,merged_exact_under_c_equals_t
M,496,thm:q-pfaff,merged_duplicate
M,528,thm:jtp,merged_duplicate
M,577,thm:pentagonal,merged_duplicate
M,589,qg:thm-quintuple-product,merged_into_stronger_A906
M,644,qg:def-partition,merged_into_A1279_canonical
M,650,thm:partition-products,merged_weaker
M,668,cor:euler-partition-recurrence,merged_duplicate
M,683,thm:rectangle-partitions,merged_duplicate
M,709,qg:def-bailey-pair,merged_duplicate_Q_definition
M,719,lem:qdiff-annihilation,merged_into_stronger_Q
M,739,thm:bailey-inversion,merged_into_stronger_Q
M,776,cor:unit-bailey-pairs,merged_into_stronger_Q
M,798,qg:thm-bailey-lemma,merged_into_A1757_canonical
M,846,thm:bailey-limit-finite,merged_duplicate
M,866,cor:bailey-limit-infinite,merged_duplicate
M,893,qg:lem-bailey-lowering,merged_into_stronger_F921
M,944,thm:rogers-ramanujan,merged_duplicate
M,1015,qg:lem-rogers-recurrence,retired_imprecise_continuant_duplicate
M,1032,qg:thm-rrcf,merged_into_stronger_A2043
M,1067,qg:thm-andrews-gordon,merged_into_stronger_F1138
M,1165,thm:rogers-ramanujan,merged_derived_modulus5
M,1175,qg:cor-andrews-gordon-mod7,retained_new
M,1200,qg:def-fourier-transform,retained_new_definition
M,1207,qg:thm-poisson,merged_into_A1047_canonical
M,1231,qg:lem-gaussian-fourier,merged_into_stronger_A1074
M,1260,qg:thm-jacobi-imaginary,merged_into_stronger_A1092
M,1284,qg:prop-theta-products,merged_into_stronger_A990
M,1307,qg:def-dedekind-eta,merged_into_A1140_canonical
M,1315,qg:thm-theta-eta-modular,merged_into_stronger_A1148
M,1332,qg:thm-theta-eta-modular,merged_into_stronger_A1148
M,1356,qg:thm-qpochhammer-modular-asymptotic,retained_new
M,1412,thm:1psi1,merged_duplicate
M,1450,thm:1psi1|prop:1psi1-convergence,merged_expository_convergence_corollary
M,1468,qg:lem-rogers-recurrence|qg:thm-rrcf,retired_imprecise_duplicate
M,1489,qg:prop-coefficientwise-limit,retained_new
M,1525,qg:prop-borwein-reciprocity,retained_new
M,1547,,retired_outdated_known_theorem
M,1637,qg:prob-finite-andrews-gordon-certificates,problem_retain_but_sharpen
M,1646,qg:prob-even-modulus-lowering,problem_retain_provisionally_literature_screen
M,1654,qg:prop-borwein-tail-stabilization,correct_and_recast_as_proposition
M,1667,qg:prob-bailey-kernel-total-positivity,problem_retain
M,1678,qg:prob-root-of-unity-asymptotics|conj:cyclotomic-resurgent-inverse,problem_merge_forward_inverse_frontier
M,1686,chap:formalization,retire_as_problem_move_to_status_roadmap
M,1699,,retire_or_recast_after_bilateral_Bailey_literature_screen
M,1771,thm:poch-entire|prop:phi-convergence|prop:1psi1-convergence,split_merge_specific_Q_results
M,1787,lem:polynomial-identity-principle|cor:safe-specialization,merged_into_stronger_Q
A,102,qg:def-qshifted-factorial,merged_duplicate_Q_definition
A,126,qg:def-negative-qshifted-index,merged_duplicate_Q_definition
A,133,prop:concat|prop:base-reversal|prop:negative-index,split_into_stronger_Q_results
A,167,qg:def-gaussian-coefficient,merged_duplicate_Q_definition
A,180,thm:qpascal|thm:qbinom-structure,split_into_stronger_Q_results
A,201,thm:finite-qbinomial,merged_duplicate
A,225,thm:reciprocal-finite,merged_duplicate
A,248,thm:q-vandermonde,merged_duplicate
A,286,thm:rectangle-partitions,merged_duplicate
A,301,thm:infinite-qbinomial,merged_duplicate
A,336,cor:euler-infinite,merged_duplicate
A,353,thm:lambert-log,merged_into_stronger_Q
A,378,qg:def-basic-hypergeometric-series,merged_duplicate_Q_definition
A,392,thm:heine,merged_duplicate
A,429,thm:q-gauss,merged_duplicate
A,447,cor:q-chu,merged_duplicate
A,478,qg:lem-euler-telescope,retained_new
A,509,thm:q-pfaff,retired_unused_proof_certificate
A,536,thm:q-pfaff,merged_duplicate
A,602,qg:lem-jackson-rational-certificate,correct_then_retain
A,634,qg:thm-jackson-8phi7,correct_then_retain
A,720,qg:cor-jackson-6phi5,retained_new
A,750,qg:def-bilateral-basic-hypergeometric,merged_Q_definition_label_add
A,767,thm:1psi1,merged_duplicate
A,810,thm:finite-jtp,merged_into_stronger_Q
A,839,thm:jtp,merged_duplicate
A,868,cor:theta-quasi,merged_into_stronger_Q
A,884,thm:pentagonal,merged_duplicate
A,906,qg:thm-quintuple-product,retained_stronger_new
A,976,qg:def-jacobi-theta,retained_new_definition
A,990,qg:prop-theta-products,retained_stronger_new
A,1029,qg:prop-theta-heat,retained_new
A,1047,qg:thm-poisson,retained_canonical_new
A,1074,qg:lem-gaussian-fourier,retained_stronger_new
A,1092,qg:thm-jacobi-imaginary,retained_stronger_new
A,1140,qg:def-dedekind-eta,retained_canonical_definition
A,1148,qg:thm-theta-eta-modular,retained_stronger_new
A,1195,qg:def-ramanujan-theta,retained_canonical_definition
A,1203,qg:prop-ramanujan-product,retained_canonical_new
A,1226,qg:thm-schroeter,retained_new
A,1279,qg:def-partition,retained_canonical_definition
A,1285,thm:partition-products,merged_weaker
A,1305,thm:partition-products,merged_duplicate
A,1332,cor:durfee-all,merged_duplicate
A,1352,cor:euler-partition-recurrence,merged_duplicate
A,1409,qg:lem-gaussian-ufd,retained_new
A,1460,qg:thm-two-square,retained_new
A,1501,qg:cor-two-square-lambert,retained_new
A,1523,qg:thm-four-square,retained_new
A,1664,qg:def-bailey-pair,merged_duplicate_Q_definition
A,1678,lem:qdiff-annihilation,merged_into_stronger_Q
A,1700,thm:bailey-inversion,merged_into_stronger_Q
A,1739,cor:unit-bailey-pairs,merged_into_stronger_Q
A,1757,qg:thm-bailey-lemma,retained_canonical_new
A,1840,thm:bailey-limit-finite,merged_duplicate
A,1862,cor:bailey-limit-infinite,merged_duplicate
A,1931,thm:rogers-ramanujan,merged_duplicate
A,1988,qg:cor-rr-partitions,retained_stronger_new
A,2024,qg:lem-rogers-recurrence,retained_canonical_new
A,2043,qg:thm-rrcf,retained_stronger_new
A,2091,qg:lem-bailey-chain-iterate,merged_into_stronger_F1118
A,2123,qg:thm-andrews-gordon,merged_endpoint_corollary_of_F1138
A,2460,qg:prop-truncation-principle,retained_new
"""

INVERSE_REDIRECTS = {
    "prop:uq-real-residual-certificate": "prop:uq-asymptotic-residual-transfer",
    "thm:interval-newton-one-dimensional": "thm:uq-interval-newton-certificate",
    "thm:rouche-one-zero-disk": "thm:uq-rouche-disk-certificate",
    "thm:inverse-residual-transfer": "prop:uq-asymptotic-residual-transfer",
    "thm:qgamma-unique-minimum": "thm:qs-qgamma-minimum",
}


def one_line(text: str) -> str:
    return " ".join(text.split())


def strip_comments_preserving_offsets(text: str) -> str:
    return COMMENT_RE.sub(lambda match: " " * len(match.group(0)), text)


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def current_section(
    section_matches: list[re.Match[str]], result_offset: int
) -> tuple[str, str]:
    path: dict[str, str] = {}
    for match in section_matches:
        if match.start() >= result_offset:
            break
        level = match.group("level")
        path[level] = one_line(match.group("title"))
        if level == "part":
            path.pop("chapter", None)
            path.pop("section", None)
            path.pop("subsection", None)
        elif level == "chapter":
            path.pop("section", None)
            path.pop("subsection", None)
        elif level == "section":
            path.pop("subsection", None)
    ordered = [
        path[key]
        for key in ("part", "chapter", "section", "subsection")
        if key in path
    ]
    return path.get("chapter", ""), " / ".join(ordered)


def inventory_file(
    text: str,
    package: str,
    relative: str,
    ordinals: Counter[str],
    display_source: str,
) -> list[dict[str, str]]:
    clean = strip_comments_preserving_offsets(text)
    results = list(BEGIN_RE.finditer(clean))
    sections = list(SECTION_RE.finditer(clean))
    rows: list[dict[str, str]] = []

    for index, match in enumerate(results):
        kind = match.group("kind")
        ordinals[kind] += 1
        end_token = rf"\end{{{kind}}}"
        statement_end = clean.find(end_token, match.end())
        if statement_end < 0:
            raise ValueError(
                f"{display_source}:{line_number(clean, match.start())}: "
                f"missing {end_token}"
            )
        statement_end += len(end_token)
        next_start = results[index + 1].start() if index + 1 < len(results) else len(clean)
        statement = clean[match.end() : statement_end]
        label_match = LEADING_LABEL_RE.match(statement)
        label = label_match.group(1) if label_match else ""
        key = label or f"unlabelled-{kind}-{ordinals[kind]:03d}"
        chapter, section_path = current_section(sections, match.start())
        proof_present = bool(PROOF_RE.search(clean[statement_end:next_start]))
        rows.append(
            {
                "source_key": f"{package}:{key}",
                "source_package": package,
                "source_file": relative,
                "source_line": str(line_number(clean, match.start())),
                "source_label": label,
                "source_kind": kind,
                "source_title": one_line(match.group("title") or ""),
                "source_chapter": chapter,
                "source_section_path": section_path,
                "source_proof_present": "yes" if proof_present else "no",
            }
        )
    return rows


def run_git(repo_root: Path, *arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


def repository_root() -> Path:
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE_ROOT), "rev-parse", "--show-toplevel"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"cannot locate repository root: {detail}")
    return Path(completed.stdout.decode("utf-8").strip()).resolve()


def resolve_revision(repo_root: Path, revision: str) -> str:
    resolved = run_git(repo_root, "rev-parse", "--verify", f"{revision}^{{commit}}")
    commit = resolved.decode("ascii").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise RuntimeError(f"git returned a noncanonical commit id: {commit!r}")
    return commit


def q_status_projection(text: str) -> dict[str, str]:
    translation = {
        "exact": "Lean-proved",
        "partial": "human-proved frontier result",
        "none": "human-proved frontier result",
        "na": "not applicable",
    }
    statuses: dict[str, str] = {}
    clean = strip_comments_preserving_offsets(text)
    for match in Q_STATUS_RE.finditer(clean):
        for label in match.group("labels").split(","):
            statuses[label.strip()] = translation[match.group("status")]
    return statuses


def inventory_revision(
    revision: str,
) -> tuple[str, list[dict[str, str]], dict[str, str], dict[str, str]]:
    repo_root = repository_root()
    commit = resolve_revision(repo_root, revision)
    rows: list[dict[str, str]] = []
    groups: dict[str, str] = {}
    q_statuses: dict[str, str] = {}
    for package, group, relatives, expected in SOURCE_GROUPS:
        ordinals: Counter[str] = Counter()
        package_rows: list[dict[str, str]] = []
        for relative in relatives:
            repository_path = (REPOSITORY_SOURCE_ROOT / relative).as_posix()
            blob = run_git(repo_root, "show", f"{commit}:{repository_path}")
            text = blob.decode("utf-8")
            if group == "Q":
                q_statuses.update(q_status_projection(text))
            package_rows.extend(
                inventory_file(
                    text,
                    package,
                    relative,
                    ordinals,
                    f"{commit}:{repository_path}",
                )
            )
        if len(package_rows) != expected:
            kinds = Counter(row["source_kind"] for row in package_rows)
            raise ValueError(
                f"{package}: extracted {len(package_rows)} environments, expected "
                f"{expected}; by kind={dict(sorted(kinds.items()))!r}"
            )
        for row in package_rows:
            groups[row["source_key"]] = group
        rows.extend(package_rows)
    return commit, rows, groups, q_statuses


def parse_guide_map() -> dict[tuple[str, str], tuple[str, str]]:
    mapping: dict[tuple[str, str], tuple[str, str]] = {}
    for raw in GUIDE_MAP_DATA.splitlines():
        line = raw.strip()
        if not line:
            continue
        alias, source_line, canonical_label, disposition = line.split(",", 3)
        package = GUIDE_PACKAGE_ALIASES[alias]
        key = package, source_line
        if key in mapping:
            raise ValueError(f"duplicate guide editorial key: {key!r}")
        mapping[key] = canonical_label, disposition
    if len(mapping) != EXPECTED_GROUP_COUNTS["guides"]:
        raise ValueError(
            f"guide editorial map has {len(mapping)} rows, expected "
            f"{EXPECTED_GROUP_COUNTS['guides']}"
        )
    return mapping


def inverse_status_projection() -> dict[str, str]:
    if not INVERSE_CONCORDANCE.is_file():
        return {}
    with INVERSE_CONCORDANCE.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    precedence = {
        "": 0,
        "not applicable": 1,
        "conjecture": 2,
        "human-proved frontier result": 3,
        "Lean-proved": 4,
    }
    statuses: dict[str, str] = {}
    for row in rows:
        label = row.get("canonical_label", "").strip()
        status = row.get("canonical_status", "").strip()
        if not label or not status:
            continue
        old = statuses.get(label, "")
        if precedence.get(status, 0) > precedence.get(old, 0):
            statuses[label] = status
    return statuses


def status_for_proved_labels(labels: str, q_statuses: dict[str, str]) -> str:
    targets = [label for label in labels.split("|") if label]
    if targets and all(q_statuses.get(label) == "Lean-proved" for label in targets):
        return "Lean-proved"
    return "human-proved frontier result"


def reviewed_rows(
    rows: list[dict[str, str]],
    groups: dict[str, str],
    q_statuses: dict[str, str],
) -> list[dict[str, str]]:
    guide_map = parse_guide_map()
    inverse_statuses = inverse_status_projection()
    reviewed: list[dict[str, str]] = []
    seen_guide_keys: set[tuple[str, str]] = set()

    for source in rows:
        row = dict(source)
        group = groups[source["source_key"]]
        kind = source["source_kind"]
        label = source["source_label"]

        if group == "Q":
            row["canonical_label"] = label
            if kind in {"definition", "example", "algorithm"}:
                row["canonical_status"] = "not applicable"
            elif kind == "conjecture":
                row["canonical_status"] = "conjecture"
            else:
                row["canonical_status"] = q_statuses.get(
                    label, "human-proved frontier result"
                )
            if label:
                row["disposition_notes"] = (
                    "Retained in the forward q-series backbone under its existing "
                    "canonical label."
                )
            else:
                descriptor = source["source_title"] or f"line {source['source_line']}"
                row["disposition_notes"] = (
                    f"Retained as the unlabeled canonical {kind} {descriptor!r}; "
                    "the historical source line and section path identify it exactly."
                )

        elif group == "inverse":
            target = INVERSE_REDIRECTS.get(label, label)
            row["canonical_label"] = target
            if kind == "conjecture":
                status = "conjecture"
            elif kind in {"definition", "example", "algorithm"}:
                status = "not applicable"
            else:
                status = inverse_statuses.get(
                    target,
                    inverse_statuses.get(label, "human-proved frontier result"),
                )
            row["canonical_status"] = status
            if target != label:
                row["disposition_notes"] = (
                    f"Merged as a duplicate or specialization into {target}; the "
                    "stronger retained inverse result carries the canonical proof."
                )
            else:
                row["disposition_notes"] = (
                    "Retained from the inverse volume under its existing canonical "
                    "label and proof status."
                )

        else:
            key = source["source_package"], source["source_line"]
            if key not in guide_map:
                raise ValueError(f"guide source row lacks editorial mapping: {key!r}")
            seen_guide_keys.add(key)
            target, disposition = guide_map[key]
            row["canonical_label"] = target
            if not target or disposition.startswith("retire") or disposition.startswith(
                "retired"
            ):
                status = "not applicable"
            elif kind == "definition":
                status = "not applicable"
            elif kind == "problem":
                status = "conjecture"
            elif kind == "conjecture":
                status = (
                    "human-proved frontier result"
                    if "recast_as_proposition" in disposition
                    else "conjecture"
                )
            elif kind in PROVED_KINDS:
                status = status_for_proved_labels(target, q_statuses)
            else:
                status = "not applicable"
            row["canonical_status"] = status
            row["disposition_notes"] = (
                "Guide audit disposition: " + disposition.replace("_", " ") + "."
            )

        reviewed.append(row)

    guide_keys = set(guide_map)
    if seen_guide_keys != guide_keys:
        missing = sorted(guide_keys - seen_guide_keys)
        extra = sorted(seen_guide_keys - guide_keys)
        raise ValueError(
            f"guide editorial/source mismatch: missing={missing!r}, extra={extra!r}"
        )
    return reviewed


def source_projection_sha256(rows: list[dict[str, str]]) -> str:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=SOURCE_FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return hashlib.sha256(stream.getvalue().encode("utf-8")).hexdigest()


def concordance_mismatches(rows: list[dict[str, str]], path: Path) -> list[str]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        retained = list(reader)
        fields = reader.fieldnames or []
    failures: list[str] = []
    if fields != list(ALL_FIELDS):
        failures.append(f"header differs from canonical schema: {fields!r}")
    if len(retained) != EXPECTED_TOTAL:
        failures.append(
            f"concordance row count differs: retained={len(retained)}, "
            f"expected={EXPECTED_TOTAL}"
        )
    if len(rows) != len(retained):
        failures.append(f"row count differs: extracted={len(rows)}, retained={len(retained)}")
    keys = [row.get("source_key", "") for row in retained]
    duplicates = [key for key, count in Counter(keys).items() if count > 1]
    if duplicates:
        failures.append("duplicate source keys: " + ", ".join(duplicates[:10]))
    for index, (extracted, reviewed) in enumerate(zip(rows, retained), start=2):
        for field in SOURCE_FIELDS:
            if extracted[field] != reviewed.get(field, ""):
                failures.append(
                    f"CSV row {index} {field}: extracted={extracted[field]!r}, "
                    f"retained={reviewed.get(field, '')!r}"
                )
                if len(failures) >= 30:
                    failures.append("further mismatches suppressed")
                    return failures
        if not reviewed.get("canonical_status", "").strip():
            failures.append(f"CSV row {index}: missing canonical_status")
        if not reviewed.get("disposition_notes", "").strip():
            failures.append(f"CSV row {index}: missing disposition_notes")
    return failures


def print_summary(rows: list[dict[str, str]], groups: dict[str, str]) -> None:
    by_group = Counter(groups[row["source_key"]] for row in rows)
    by_package = Counter(row["source_package"] for row in rows)
    by_kind = Counter(row["source_kind"] for row in rows)
    print(f"result environments: {len(rows)}")
    print(f"source projection sha256: {source_projection_sha256(rows)}")
    print("by group: " + ", ".join(f"{key}={by_group[key]}" for key in ("Q", "inverse", "guides")))
    print("by package:")
    for package, count in sorted(by_package.items()):
        print(f"  {package:42s} {count:3d}")
    print("by kind: " + ", ".join(f"{kind}={count}" for kind, count in sorted(by_kind.items())))
    print(f"without source labels: {sum(not row['source_label'] for row in rows)}")
    unlabeled_by_group_kind = Counter(
        (groups[row["source_key"]], row["source_kind"])
        for row in rows
        if not row["source_label"]
    )
    print(
        "unlabeled by group/kind: "
        + ", ".join(
            f"{group}/{kind}={count}"
            for (group, kind), count in sorted(unlabeled_by_group_kind.items())
        )
    )
    print(f"without following proofs: {sum(row['source_proof_present'] == 'no' for row in rows)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--revision",
        help="commit-ish to inventory instead of audit/MERGE_SOURCE_REVISION",
    )
    parser.add_argument(
        "--inventory-only",
        action="store_true",
        help="print immutable-source counts without requiring the concordance",
    )
    parser.add_argument(
        "--print-source-csv",
        action="store_true",
        help="write the immutable ten-column source projection to stdout",
    )
    parser.add_argument(
        "--print-reviewed-csv",
        action="store_true",
        help="write the complete reviewed concordance to stdout",
    )
    args = parser.parse_args()

    revision = args.revision or PIN_FILE.read_text(encoding="ascii").strip()
    commit, rows, groups, q_statuses = inventory_revision(revision)
    if len(rows) != EXPECTED_TOTAL:
        raise ValueError(f"extracted {len(rows)} rows, expected {EXPECTED_TOTAL}")
    group_counts = Counter(groups[row["source_key"]] for row in rows)
    if dict(group_counts) != EXPECTED_GROUP_COUNTS:
        raise ValueError(
            f"group counts differ: extracted={dict(group_counts)!r}, "
            f"expected={EXPECTED_GROUP_COUNTS!r}"
        )

    if args.print_source_csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=SOURCE_FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
        return 0

    if args.print_reviewed_csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=ALL_FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(reviewed_rows(rows, groups, q_statuses))
        return 0

    print(f"merge source revision: {commit}")
    print_summary(rows, groups)
    if args.inventory_only:
        return 0
    if not CONCORDANCE.is_file():
        print(f"missing concordance: {CONCORDANCE}", file=sys.stderr)
        return 1
    failures = concordance_mismatches(rows, CONCORDANCE)
    if failures:
        print("\nFAILED", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1
    print("\nPASS: immutable source projection and reviewed dispositions agree")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

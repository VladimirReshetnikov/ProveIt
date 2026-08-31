#!/usr/bin/env python3
"""Reproduce the report's repository-wide TeX inventory and overlap screen."""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


HEADING_RE = re.compile(
    r"^\s*\\(?P<kind>part|chapter|section|subsection)\*?\{(?P<title>.*)\}\s*$"
)

CLUSTERS = {
    "Fourier-zero spectral zeta": (
        "spectral zeta",
        "zero divisor",
        "zero multiplicity",
        "fourier zero",
    ),
    "Exact digit-sum zero count": (
        "digit-sum",
        "digit sum",
        "zero count",
        "s_2(",
        "\\nu_2",
        "\\vtwo",
    ),
    "Complex dimensions / heat trace": (
        "complex dimension",
        "heat trace",
        "gamma--zeta",
        "gamma--\\zeta",
    ),
    "Sharp Strang--Fix aliasing defect": (
        "strang--fix",
        "strang--\\fix",
        "aliasing defect",
        "polynomial reproduction",
    ),
    "Phase-locked Lambert-W saddle": (
        "phase-locked",
        "phase locked",
        "lambert-$w",
        "lambert--$w",
        "w_{-1}",
    ),
    "Integer-base atomic family": (
        "integer-base",
        "integer base",
        "base-$b$",
        "base-\\(b\\)",
        "general-base",
        "atomic family",
    ),
}


def find_docs_root(script: Path) -> Path:
    for parent in script.parents:
        if parent.name == "docs" and parent.parent.name == "FabiusFunction":
            return parent
    raise RuntimeError("could not locate Analysis/FabiusFunction/docs")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--docs-root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    script = Path(__file__).resolve()
    package_dir = script.parent
    docs_root = (args.docs_root or find_docs_root(script)).resolve()
    output = (args.output or package_dir / "repository_audit.md").resolve()

    tex_files = sorted(
        path
        for path in docs_root.rglob("*.tex")
        if package_dir not in path.resolve().parents
    )

    digest = hashlib.sha256()
    total_lines = 0
    total_bytes = 0
    records: list[tuple[str, str, list[str], list[str]]] = []
    cluster_hits: dict[str, list[str]] = {name: [] for name in CLUSTERS}

    for path in tex_files:
        data = path.read_bytes()
        text = data.decode("utf-8", errors="replace")
        rel = path.relative_to(docs_root).as_posix()
        digest.update(data)
        total_bytes += len(data)
        total_lines += len(text.splitlines())

        headings: list[str] = []
        for line in text.splitlines():
            match = HEADING_RE.match(line)
            if match:
                headings.append(f"{match.group('kind')}: {match.group('title')}")

        lowered = text.lower()
        matched_clusters: list[str] = []
        for name, needles in CLUSTERS.items():
            if any(needle in lowered for needle in needles):
                cluster_hits[name].append(rel)
                matched_clusters.append(name)

        records.append((rel, hashlib.sha256(data).hexdigest(), headings, matched_clusters))

    lines = [
        "# Repository audit",
        "",
        "Target: `Analysis/FabiusFunction/docs/**/*.tex`, excluding this newly filed package directory.",
        "",
        f"- TeX files read: **{len(tex_files)}**",
        f"- Total source lines: **{total_lines}**",
        f"- Total source bytes: **{total_bytes}**",
        f"- Concatenated-corpus SHA-256: `{digest.hexdigest()}`",
        "",
        "The corpus digest hashes raw file bytes concatenated in lexicographic relative-path order.",
        "Phrase clusters are a broad overlap screen, not a decision procedure for mathematical equivalence",
        "or a claim of worldwide priority.",
        "",
        "## Candidate-contribution phrase clusters",
        "",
    ]

    for name in CLUSTERS:
        hits = cluster_hits[name]
        lines.append(f"### {name}")
        lines.append("")
        lines.append(f"Matched **{len(hits)}** prior TeX files:")
        lines.append("")
        lines.extend(f"- `{hit}`" for hit in hits)
        lines.append("")

    lines.extend(["## File manifest", ""])
    for rel, sha, headings, matched_clusters in records:
        lines.append(f"### `{rel}`")
        lines.append("")
        lines.append(f"- SHA-256: `{sha}`")
        if matched_clusters:
            lines.append("- Phrase clusters: " + "; ".join(matched_clusters))
        else:
            lines.append("- Phrase clusters: none")
        lines.append("- Structural headings:")
        if headings:
            lines.extend(f"  - {heading}" for heading in headings)
        else:
            lines.append("  - none detected")
        lines.append("")

    output.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Compile the paper using installed TeX, with a private minimal-config fallback.

No downloads or system configuration changes are made. A normal complete
TeX installation simply uses its existing format and font map.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


PACKAGE = Path(__file__).resolve().parents[1]
SOURCE = PACKAGE / "stirling_ipra.tex"


def kpse(name: str) -> str:
    result = subprocess.run(["kpsewhich", name], text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else ""


def checked_run(args: list[str], cwd: Path, env: dict[str, str]) -> str:
    result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError("Command failed: " + " ".join(args) + "\n" + result.stdout + result.stderr)
    return result.stdout + result.stderr


def main() -> None:
    for command in ["pdflatex", "pdftex", "kpsewhich"]:
        if not shutil.which(command):
            raise RuntimeError(f"Required installed TeX command is missing: {command}")

    env = dict(os.environ)
    fallback_format = not bool(kpse("pdflatex.fmt"))
    fallback_map = not bool(kpse("pdftex.map"))
    with tempfile.TemporaryDirectory(prefix="stirling-tex-") as temporary:
        work = Path(temporary)
        if fallback_format:
            checked_run([
                "pdftex", "-ini", "-etex", "-jobname=pdflatex", "-progname=pdflatex",
                "-interaction=nonstopmode", "-halt-on-error", "pdflatex.ini",
            ], work, env)
            env["TEXFORMATS"] = str(work) + os.pathsep + env.get("TEXFORMATS", "")

        if fallback_map:
            dirs = {Path(name).parent for item in ["lm.map", "cm.map"] if (name := kpse(item))}
            if not dirs:
                raise RuntimeError("Installed font maps lm.map/cm.map could not be located")
            entries: dict[str, str] = {}
            for directory in sorted(dirs):
                for path in sorted(directory.glob("*.map")):
                    for line in path.read_text().splitlines():
                        stripped = line.strip()
                        if stripped and not stripped.startswith("%"):
                            entries.setdefault(stripped.split()[0], line)
            (work / "pdftex.map").write_text("\n".join(entries.values()) + "\n")
            env["TEXFONTMAPS"] = str(work) + os.pathsep + env.get("TEXFONTMAPS", "")

        build_dir = work / "output"
        build_dir.mkdir()
        output = ""
        for _ in range(3):
            output = checked_run([
                "pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                "-output-directory=" + str(build_dir), str(SOURCE),
            ], PACKAGE, env)
        log = (build_dir / "stirling_ipra.log").read_text()
        checks = {
            "no_unresolved_references": "undefined references" not in log and "undefined on input" not in log,
            "no_overfull_boxes": "Overfull" not in log,
            "no_missing_characters": "Missing character:" not in log,
            "no_rerun_requested": "Rerun to get" not in log,
        }
        if not all(checks.values()):
            raise RuntimeError("PDF validation failed: " + json.dumps(checks) + "\n" + output)
        destination = PACKAGE / "stirling_ipra.pdf"
        shutil.copy2(build_dir / "stirling_ipra.pdf", destination)
        record = {
            "status": "compiled",
            "passes": 3,
            "engine": subprocess.run(["pdflatex", "--version"], text=True, capture_output=True).stdout.splitlines()[0],
            "private_format_generated": fallback_format,
            "private_font_map_generated": fallback_map,
            "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            "pdf_sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
            "pdf_size_bytes": destination.stat().st_size,
            "checks": checks,
        }
        if shutil.which("pdfinfo"):
            info = subprocess.run(["pdfinfo", str(destination)], text=True, capture_output=True).stdout
            for line in info.splitlines():
                if line.startswith("Pages:"):
                    record["pages"] = int(line.split(":", 1)[1])
        (PACKAGE / "validation" / "build.json").write_text(json.dumps(record, indent=2) + "\n")
        print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()

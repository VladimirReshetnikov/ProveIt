"""Port Compact44 modules whose width enters only as a literal to width 121.

Usage: py -I -X utf8 -S -B width_port.py MODULE [MODULE ...]

Each named Compact44 module (file stem under Lean/DiophantineConsistency/
Compact44) is copied to Lean/DiophantineConsistency/Mixed121/W121/ with:

* the width literals 67, 66 and 65 replaced by 121, 120 and 119, where they
  are standalone numerals;
* `namespace X` renamed to `namespace W121.X`, and every reference `X.name`
  or `open ... X ...` to a ported module rewritten the same way;
* `import DiophantineConsistency.Compact44.X` rewritten to the W121 copy for
  ported modules. Other imports, including width-free modules, are kept.

The copies keep the accepted proof bodies. Lean, not this script, checks the
result. The script refuses a module that mentions the period 8807: a
period-dependent module is not a width-only port.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3] / "Lean/DiophantineConsistency"
SRC = ROOT / "Compact44"
DST = ROOT / "Mixed121/W121"
NUM = {"67": "121", "66": "120", "65": "119"}


def port(stem, ported):
    text = (SRC / f"{stem}.lean").read_text(encoding="utf-8")
    if re.search(r"(?<![0-9])8807(?![0-9])", text):
        raise SystemExit(f"{stem}: mentions the period 8807; not a width-only port")
    text = re.sub(r"(?<![0-9A-Za-z_.])(67|66|65)(?![0-9])", lambda m: NUM[m.group(1)], text)
    for x in ported:
        text = text.replace(f"import DiophantineConsistency.Compact44.{x}\n",
                            f"import DiophantineConsistency.Mixed121.W121.{x}\n")
        text = re.sub(rf"^namespace {x}$", f"namespace W121.{x}", text, flags=re.M)
        text = re.sub(rf"^end {x}$", f"end W121.{x}", text, flags=re.M)
        text = re.sub(rf"(?<![A-Za-z0-9_.]){x}\.(?=[A-Za-z_])", f"W121.{x}.", text)
        text = re.sub(rf"^(open .*?)(?<![A-Za-z0-9_.]){x}(?![A-Za-z0-9_.])",
                      lambda m: m.group(1) + f"W121.{x}", text, flags=re.M)
        # `open` lines may name several ported modules; repeat until stable.
        prev = None
        while prev != text:
            prev = text
            text = re.sub(rf"^(open .*?)(?<![A-Za-z0-9_.]){x}(?![A-Za-z0-9_.])",
                          lambda m: m.group(1) + f"W121.{x}", text, flags=re.M)
    header = (f"/-! Width-121 port of `Compact44/{stem}` by "
              "`research/mixed121-calibration/tools/width_port.py`: the accepted proof\n"
              "body with the width literals 67/66/65 replaced by 121/120/119. -/\n")
    lines = text.split("\n")
    i = max(k for k, l in enumerate(lines) if l.startswith("import ")) + 1 if any(
        l.startswith("import ") for l in lines) else 0
    lines.insert(i, header)
    DST.mkdir(parents=True, exist_ok=True)
    (DST / f"{stem}.lean").write_text("\n".join(lines), encoding="utf-8", newline="\n")


def main():
    targets = sys.argv[1:]
    # References to modules ported earlier are rewritten too.
    existing = [p.stem for p in DST.glob("*.lean")] if DST.exists() else []
    ported = sorted(set(targets) | set(existing))
    for stem in targets:
        port(stem, ported)
        print("ported", stem)


if __name__ == "__main__":
    main()

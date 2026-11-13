"""Compile accepted CANONICAL four-field fixtures to the new three-field protocol.

This is an untrusted convenience translator, not part of any measured checker.
It instruments the pinned 317-token control to record its proof-tree order.
The theorem establishes canonical completeness; it does not claim that this
translator preserves arbitrary malformed or noncanonical certificate stacks.
"""
from __future__ import annotations
import argparse
import contextlib
import io
import json
from pathlib import Path


def compile_certificate(certificate, control: Path):
    source = control.read_text()
    needle = "    m, s, u, t = q()\n"
    if source.count(needle) != 1:
        raise ValueError("Unexpected control layout; use the bundled 317-token control")
    insertion = needle + """    if (m, a) == (s and [s, u] or [t] * 3, i(t, u)):
        trace.append([s, u, t])
    elif m:
        trace.append([m, 0, 0])
    else:
        trace.append([s, u, t])
"""
    instrumented = "trace = []\n" + source.replace(needle, insertion)
    text = json.dumps(certificate)
    namespace = {"open": lambda descriptor: io.StringIO(text)}
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        exec(compile(instrumented, str(control), "exec"), namespace)
    if output.getvalue() != "ACCEPT\n":
        raise ValueError("The control did not accept")
    return list(reversed(namespace["trace"])) + [certificate[-1]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--control", type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        "controls/checker_strict_tokens317.py")
    args = parser.parse_args()
    certificate = json.loads(args.input.read_text())
    compiled = compile_certificate(certificate, args.control)
    args.output.write_text(json.dumps(compiled, separators=(",", ":")) + "\n")
    print(f"Compiled {len(compiled) - 1} consumed three-field records")


if __name__ == "__main__":
    main()

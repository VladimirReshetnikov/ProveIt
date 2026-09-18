"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations

import json
import sys

from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .filters import FilterLimit, jones_obstruction
from .recognize import factored_khovanov_rank, recognize
from .scan import ScanLimit, khovanov_rank

EXIT = {"UNKNOT": 0, "KNOTTED": 0, "UNKNOWN": 3}


def load(path: str) -> Diagram:
    data = json.load(sys.stdin if path == "-" else open(path, encoding="utf-8"))
    return Diagram.from_json(data)


def _scan_worker() -> int:
    """Competitor of a race (see ``scan._Race``): a scan job as JSON on stdin, the result on stdout."""
    job = json.load(sys.stdin)
    try:
        result = khovanov_rank([tuple(row) for row in job["pd"]], order=job["order"],
                               max_objects=job.get("max_objects"), seconds=job.get("seconds"), tail=job.get("tail", 0))
    except ScanLimit:
        return 3
    json.dump({key: result[key] for key in ("rank", "reduced_rank", "by_degree", "stats", "order")}, sys.stdout)
    return 0


# One table for both parsers.  (flag, type or None for a switch, default, choices, help)
OPTIONS = {
    "recognize": [
        ("--max-objects", int, None, None, "ceiling on objects of the scanning complex (UNKNOWN when exceeded)"),
        ("--seconds", float, None, None, "cooperative time budget"),
        ("--no-reduction", None, False, None, None),
        ("--no-descending", None, False, None, None),
        ("--no-alexander", None, False, None, "disable both Alexander stages"),
        ("--no-r3", None, False, None, "no Reidemeister III search before the Khovanov scan"),
        ("--exact-alexander", None, False, None,
         "also compute the exact Alexander polynomial after the modular test passed"),
        ("--no-modular", None, False, None, "disable only the modular Alexander stage"),
        ("--no-jones", None, False, None, None),
        ("--no-factor", None, False, None, "do not split visible connected sums"),
        ("--jones-max-states", int, 4096, None, None),
        ("--pivot", str, "minfill", ("minfill", "lifo"), None),
        ("--algebra", str, "bits", ("bits", "sets"), None),
        ("--tail", int, 0, None, None),
        ("--check-d2", None, False, None, "verify d^2=0 after every crossing"),
        ("--race", int, 1, None,
         "scan N greedy orders in separate processes, first to finish wins (default 1: no race)"),
        ("--race-after", float, 1.0, None, "seconds the default order runs alone before competitors are started"),
        ("--output", str, None, None, "write the JSON result to this file"),
    ],
    "khovanov": [
        ("--check-d2", None, False, None, None),
        ("--factor", None, False, None, "multiply ranks over visible connected summands"),
        ("--pivot", str, "minfill", ("minfill", "lifo"), None),
        ("--algebra", str, "bits", ("bits", "sets"), None),
        ("--tail", int, 0, None, None),
        ("--race", int, 1, None, "scan N greedy orders in separate processes"),
        ("--race-after", float, 1.0, None, "head start of the default order in seconds"),
    ],
    "jones": [],
    "alexander": [],
}
COMMAND_HELP = {"recognize": "decide whether a knot diagram is the unknot",
                "khovanov": "total F2 Khovanov rank by scanning",
                "jones": "one-sided modular Kauffman bracket test", "alexander": "Alexander polynomial"}


class _Namespace:
    def __init__(self, **values):
        self.__dict__.update(values)


def _attribute(flag: str) -> str:
    return flag[2:].replace("-", "_")


def _parser():
    """The real parser, built from the table.  Importing and setting up ``argparse`` takes 55 ms
    (in Python 3.14 it loads ``_colorize``, ``dataclasses`` and ``shutil``), half of the run time of
    a whole ``recognize`` process, so it is used only when ``_fast_parse`` declines."""
    import argparse
    parser = argparse.ArgumentParser(prog="fastunknot", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for command, options in OPTIONS.items():
        one = sub.add_parser(command, help=COMMAND_HELP[command])
        one.add_argument("file")
        for flag, kind, default, choices, text in options:
            if kind is None:
                one.add_argument(flag, action="store_true", help=text)
            elif choices:
                one.add_argument(flag, choices=choices, default=default, help=text)
            else:
                one.add_argument(flag, type=kind, default=default, help=text)
    return parser


def _fast_parse(argv: list[str]):
    """The well-formed common case, or None to let ``argparse`` handle it: help, errors, abbreviated
    flags, ``--flag=value``, values that look like flags.  Same attributes as the ``argparse`` namespace."""
    if not argv or argv[0] not in OPTIONS:
        return None
    table = {flag: (kind, choices) for flag, kind, _, choices, _ in OPTIONS[argv[0]]}
    values = {_attribute(flag): default for flag, _, default, _, _ in OPTIONS[argv[0]]}
    values["command"] = argv[0]
    i, files = 1, []
    while i < len(argv):
        token = argv[i]
        if not token.startswith("-"):
            files.append(token)
        elif token not in table:
            return None
        else:
            kind, choices = table[token]
            if kind is None:
                values[_attribute(token)] = True
            else:
                i += 1
                if i >= len(argv) or argv[i].startswith("-"):
                    return None
                try:
                    value = kind(argv[i])
                except ValueError:
                    return None
                if choices and value not in choices:
                    return None
                values[_attribute(token)] = value
        i += 1
    if len(files) != 1:
        return None
    values["file"] = files[0]
    return _Namespace(**values)


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else list(argv)
    if argv[:1] == ["_scan"]:
        return _scan_worker()
    args = _fast_parse(argv)
    if args is None:
        args = _parser().parse_args(argv)
    try:
        diagram = load(args.file)
    except (DiagramError, ValueError, OSError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 2
    if args.command == "recognize":
        result = recognize(diagram, use_reduction=not args.no_reduction,
                           use_descending=not args.no_descending,
                           use_alexander=not args.no_alexander, use_modular=not args.no_modular,
                           use_exact_alexander=True if args.exact_alexander else None, use_r3=not args.no_r3,
                           race=args.race, race_after=args.race_after,
                           use_jones=not args.no_jones, use_factorization=not args.no_factor,
                           jones_max_states=args.jones_max_states, pivot=args.pivot,
                           algebra=args.algebra, tail=args.tail, max_objects=args.max_objects,
                           seconds=args.seconds, check_d_squared=args.check_d2).to_json()
        text = json.dumps(result, indent=1)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as handle:
                handle.write(text + "\n")
        print(text)
        return EXIT[result["status"]]
    if args.command == "khovanov":
        options = dict(check_d_squared=args.check_d2, pivot=args.pivot, algebra=args.algebra, tail=args.tail,
                       race=args.race, race_after=args.race_after)
        result = factored_khovanov_rank(diagram, **options) if args.factor else khovanov_rank(diagram.pd, **options)
        print(json.dumps(result, indent=1))
        return 0
    if args.command == "jones":
        try:
            witness = jones_obstruction(diagram, max_states=None, max_transitions=None)
        except FilterLimit as exc:
            witness = {"skipped": str(exc)}
        print(json.dumps({"verdict": "KNOTTED" if witness else "INCONCLUSIVE", "witness": witness}, indent=1))
        return 0
    poly = alexander_polynomial(diagram)
    print(json.dumps({"alexander_polynomial": format_polynomial(poly), "coefficients": poly}))
    return 0


if __name__ == "__main__":
    sys.exit(main())

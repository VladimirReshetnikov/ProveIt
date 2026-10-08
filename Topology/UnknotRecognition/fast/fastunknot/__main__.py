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
    if path == "-":
        data = json.load(sys.stdin)
    else:
        with open(path, encoding="utf-8") as handle:
            data = json.load(handle)
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
        ("--window-radius", int, None, None, "enable bounded window probes, widening up to this normalized radius"),
        ("--window-max-objects", int, 20000, None, "retained-object ceiling for optional window probes"),
        ("--window-seconds", float, 0.1, None, "one shared time allowance for all window probes per factor"),
        ("--reduction", str, "standard", ("standard", "residue", "adaptive"),
         "chain cancellation strategy (distinct from Reidemeister --no-reduction)"),
        ("--twist-max-basis", int, 1_000_000, None, "reduced basis ceiling for the optional twist backend"),
        ("--composition", str, "standard", ("standard", "component", "component-dense"),
         "opt-in component contraction for the standard scanner"),
        ("--composition-max-variables", int, 18, None, "component/output variable allocation limit"),
        ("--no-braid", None, False, None, "disable source-braid certificates"),
        ("--braid-backend", str, "free-product", ("free-product", "matrix"),
         "exact decision backend for a source braid on at most three strands"),
        ("--no-braid-reduction", None, False, None, "disable singleton endpoint destabilization"),
        ("--no-seifert", None, False, None, "disable the linear signed Seifert graph certificate"),
        ("--backend", str, "standard", ("standard", "shared", "saturated", "euler", "twist", "barcode", "fitting"),
         "Khovanov backend, including optional sharing, twists, intervals, or scalar splitting"),
        ("--euler-max-states", int, 4096, None, "state budget for optional Euler continuation"),
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
        ("--legacy-factor", None, False, None, "use the historical recursive two-edge-cut factorizer"),
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
        ("--reduction", str, "standard", ("standard", "residue", "adaptive"),
         "opt-in binary survivor prediction and degree-gap cancellation shortcut"),
        ("--twist", None, False, None, "compute a checked source braid through twist blocks"),
        ("--twist-max-basis", int, 1_000_000, None, "reduced basis ceiling for the optional twist backend"),
        ("--composition", str, "standard", ("standard", "component", "component-dense"),
         "opt-in component contraction for the standard scanner"),
        ("--composition-max-variables", int, 18, None, "component/output variable allocation limit"),
        ("--barcode", None, False, None, "exact common-coefficient interval normalization"),
        ("--fitting", None, False, None, "exact grading-preserving scalar splitting and intervals"),
        ("--shared", None, False, None, "use exact component sharing (cannot combine with --factor)"),
        ("--check-d2", None, False, None, None),
        ("--factor", None, False, None, "multiply ranks over visible connected summands"),
        ("--pivot", str, "minfill", ("minfill", "lifo"), None),
        ("--algebra", str, "bits", ("bits", "sets"), None),
        ("--tail", int, 0, None, None),
        ("--race", int, 1, None, "scan N greedy orders in separate processes"),
        ("--race-after", float, 1.0, None, "head start of the default order in seconds"),
    ],
    "window": [
        ("--lower", int, 0, None, "first queried homological degree"),
        ("--upper", int, 0, None, "last queried homological degree"),
        ("--normalized", None, False, None, "interpret endpoints after subtracting the PD negative-crossing count"),
        ("--auto-mirror", None, False, None, "select the mirror with the smaller proved object bound"),
        ("--max-objects", int, None, None, "ceiling on retained objects before allocation"),
        ("--seconds", float, None, None, "cooperative time budget including order and mirror selection"),
        ("--check-d2", None, False, None, "verify d^2=0 after each crossing"),
        ("--reduction", str, "standard", ("standard", "residue", "adaptive"), "cancellation strategy"),
        ("--composition", str, "standard", ("standard", "component", "component-dense"), "coefficient engine"),
        ("--composition-max-variables", int, 18, None, "component allocation limit"),
    ],
    "jones": [],
    "alexander": [],
}
COMMAND_HELP = {"recognize": "decide whether a knot diagram is the unknot",
                "khovanov": "total F2 Khovanov rank by scanning",
                "window": "exact partial F2 homology; raw degrees unless --normalized",
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
    if args.command in ("recognize", "khovanov"):
        if args.reduction != "standard" and (
                args.pivot != "minfill" or args.algebra != "bits" or args.race != 1
                or getattr(args, "backend", "standard") != "standard"
                or getattr(args, "barcode", False) or getattr(args, "fitting", False)
                or getattr(args, "shared", False) or getattr(args, "twist", False)):
            print("residue/adaptive reduction requires the standard backend, minfill, bits, and race=1",
                  file=sys.stderr)
            return 2
        if args.twist_max_basis < 0:
            print("--twist-max-basis must be nonnegative", file=sys.stderr)
            return 2
        if args.composition_max_variables < 0:
            print("--composition-max-variables must be nonnegative", file=sys.stderr)
            return 2
        if args.composition != "standard" and (
                args.pivot != "minfill" or args.algebra != "bits" or args.race != 1
                or getattr(args, "backend", "standard") != "standard"
                or getattr(args, "barcode", False) or getattr(args, "fitting", False)
                or getattr(args, "shared", False)):
            print("component composition requires standard backend, minfill, bits, and race=1", file=sys.stderr)
            return 2
    if args.command == "recognize":
        try:
            if args.window_seconds < 0 or not args.window_seconds < float("inf"):
                raise ValueError("--window-seconds must be finite and nonnegative")
            if args.window_radius is not None and args.window_radius < 0:
                raise ValueError("--window-radius must be nonnegative")
            if args.window_max_objects < 0:
                raise ValueError("--window-max-objects must be nonnegative")
        except ValueError as exc:
            print(f"invalid window options: {exc}", file=sys.stderr)
            return 2
        if args.euler_max_states < 0:
            print("--euler-max-states must be nonnegative", file=sys.stderr)
            return 2
        if args.backend != "standard" and (args.pivot != "minfill" or args.algebra != "bits"
                                            or args.tail != 0 or args.race != 1):
            print("alternate backends require minfill, bits, tail=0, and race=1", file=sys.stderr)
            return 2
        result = recognize(diagram, use_reduction=not args.no_reduction,
                           window_radius=args.window_radius, window_max_objects=args.window_max_objects,
                           window_seconds=args.window_seconds,
                           use_seifert=not args.no_seifert, backend=args.backend,
                           twist_max_basis=args.twist_max_basis,
                           composition=args.composition, composition_max_variables=args.composition_max_variables,
                           reduction=args.reduction,
                           use_braid=not args.no_braid, braid_backend=args.braid_backend,
                           use_braid_reduction=not args.no_braid_reduction,
                           euler_max_states=args.euler_max_states,
                           use_descending=not args.no_descending,
                           use_alexander=not args.no_alexander, use_modular=not args.no_modular,
                           use_exact_alexander=True if args.exact_alexander else None, use_r3=not args.no_r3,
                           race=args.race, race_after=args.race_after,
                           use_jones=not args.no_jones, use_factorization=not args.no_factor,
                           factor_backend="legacy" if args.legacy_factor else "interlacement",
                           jones_max_states=args.jones_max_states, pivot=args.pivot,
                           algebra=args.algebra, tail=args.tail, max_objects=args.max_objects,
                           seconds=args.seconds, check_d_squared=args.check_d2).to_json()
        text = json.dumps(result, indent=1)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as handle:
                handle.write(text + "\n")
        print(text)
        return EXIT[result["status"]]
    if args.command == "window":
        from .window_scan import khovanov_window
        from .window_bounds import khovanov_window_auto
        shift = diagram.signs().count(-1) if args.normalized else 0
        options = dict(max_objects=args.max_objects, seconds=args.seconds,
                       check_d_squared=args.check_d2, reduction=args.reduction,
                       composition=args.composition, composition_max_variables=args.composition_max_variables)
        try:
            if args.auto_mirror:
                result = khovanov_window_auto(diagram, args.lower + shift, args.upper + shift, **options)
            else:
                result = khovanov_window(diagram.pd, args.lower + shift, args.upper + shift, **options)
        except ValueError as exc:
            print(f"invalid window input: {exc}", file=sys.stderr)
            return 2
        except (ScanLimit, MemoryError) as exc:
            print(json.dumps(dict(status="UNKNOWN", method="resource-limit", reason=str(exc))))
            return 3
        result["degree_convention"] = "raw cube degrees"
        if args.normalized:
            result["normalized_by_degree"] = {h - shift: rank for h, rank in result["by_degree"].items()}
            result["normalized_lower"], result["normalized_upper"] = args.lower, args.upper
        print(json.dumps(result, indent=1))
        return 0
    if args.command == "khovanov":
        if args.barcode or args.fitting:
            if (sum((args.barcode, args.fitting, args.shared, args.twist)) > 1 or args.factor
                    or args.pivot != "minfill" or args.algebra != "bits" or args.tail or args.race != 1):
                print("--barcode/--fitting require one backend, no --factor, minfill, bits, tail=0, race=1",
                      file=sys.stderr)
                return 2
            if args.fitting:
                from .scalar_split import fitting_khovanov_rank as rank
            else:
                from .barcode_scan import barcode_khovanov_rank as rank
            try:
                result = rank(diagram.pd, check_d_squared=args.check_d2)
            except (ScanLimit, MemoryError) as exc:
                print(json.dumps(dict(status="UNKNOWN", method="resource-limit", reason=str(exc))))
                return 3
            print(json.dumps(result, indent=1))
            return 0
        if args.twist:
            if (args.shared or args.factor or args.pivot != "minfill" or args.algebra != "bits"
                    or args.tail or args.race != 1 or args.composition != "standard"):
                print("--twist requires no --shared/--factor, minfill, bits, tail=0, race=1, and standard composition",
                      file=sys.stderr)
                return 2
            from .twist.core import Budget
            from .twist_adapter import twist_khovanov_rank
            try:
                result = twist_khovanov_rank(diagram, budget=Budget(max_basis=args.twist_max_basis),
                                             check_d_squared=args.check_d2)
            except ValueError as exc:
                print(f"invalid twist input: {exc}", file=sys.stderr)
                return 2
            except (ScanLimit, MemoryError) as exc:
                print(json.dumps({"status": "UNKNOWN", "method": "resource-limit", "reason": str(exc)}))
                return 3
            print(json.dumps(result, indent=1))
            return 0
        if args.shared:
            if args.factor or args.pivot != "minfill" or args.algebra != "bits" or args.tail or args.race != 1:
                print("--shared requires no --factor, minfill, bits, tail=0, and race=1", file=sys.stderr)
                return 2
            from .component_scan import compressed_khovanov_rank
            result = compressed_khovanov_rank(diagram.pd, check_d_squared=args.check_d2)
            print(json.dumps(result, indent=1))
            return 0
        options = dict(check_d_squared=args.check_d2, pivot=args.pivot, algebra=args.algebra, tail=args.tail,
                       race=args.race, race_after=args.race_after, composition=args.composition,
                       composition_max_variables=args.composition_max_variables, reduction=args.reduction)
        try:
            result = factored_khovanov_rank(diagram, **options) if args.factor else khovanov_rank(diagram.pd, **options)
        except (ScanLimit, MemoryError) as exc:
            print(json.dumps({"status": "UNKNOWN", "method": "resource-limit",
                              "reason": str(exc) or "memory allocation failed"}))
            return 3
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

"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations

import json
import sys

from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .filters import FilterLimit
from .jones_filter import JONES_BACKENDS, select_jones_filter, validate_jones_options
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
        ("--window-strategy", str, "support", ("support", "minimal"), "allocation-pruned or cancel-before-truncate window strategy"),
        ("--ranktwo", None, False, None, "try one verified rank-two shortening pass on a retained source braid"),
        ("--ranktwo-seconds", float, 0.1, None, "local allowance for optional braid compression and replay"),
        ("--garside", None, False, None, "try verified cyclic Garside source-braid compression"),
        ("--garside-radius", int, 1, None, "maximum target word length in the optional cyclic kernel"),
        ("--garside-seconds", float, 0.1, None, "shared local allowance for Garside search and replay"),
        ("--garside-max-ticks", int, 100000, None, "cooperative operation allowance for the Garside probe"),
        ("--garside-max-targets", int, 100000, None, "target dictionary ceiling for the Garside probe"),
        ("--window-radius", int, None, None, "enable bounded window probes, widening up to this normalized radius"),
        ("--window-max-objects", int, 20000, None, "retained-object ceiling for optional window probes"),
        ("--window-seconds", float, 0.1, None, "one shared time allowance for all window probes per factor"),
        ("--reduction", str, "standard", ("standard", "residue", "adaptive", "disk-adaptive", "graded", "graded-adaptive", "corridor", "corridor-adaptive"),
         "chain cancellation strategy (distinct from Reidemeister --no-reduction)"),
        ("--twist-max-basis", int, 1_000_000, None, "reduced basis ceiling for the optional twist backend"),
        ("--composition", str, "standard", ("standard", "component", "component-dense"),
         "opt-in component contraction for the standard scanner"),
        ("--composition-max-variables", int, 18, None, "component/output variable allocation limit"),
        ("--braid-profile", None, False, None, "evaluate the Seifert structural certificate directly on a checked source braid"),
        ("--no-braid", None, False, None, "disable source-braid certificates"),
        ("--no-rational", None, False, None, "disable checked Montesinos source certificates"),
        ("--treewidth-two", None, False, None, "certify K4-minor-free projection and decide by exact determinant"),
        ("--treewidth-two-seconds", float, 0.1, None, "local time allowance for optional treewidth-two recognition"),
        ("--regina", None, False, None, "try optional isolated normal-surface recognition after filters on >=32 crossings"),
        ("--regina-seconds", float, 2.0, None, "local allowance including startup for the optional Regina probe"),
        ("--group", None, False, None, "try independently replayed cyclic knot-group certificates after filters"),
        ("--group-seconds", float, 0.05, None, "local allowance for group search and independent verification"),
        ("--group-relators", None, False, None, "enable group certificates with exact cyclic relator-overlap moves"),
        ("--group-max-work", int, 2000000, None, "work allowance for each group search and independent replay"),
        ("--group-compressed", None, False, None, "enable group certificates with exact compressed-word replay"),
        ("--group-compressed-search", None, False, None, "enable compressed group search and replay; overlaps expand within a fixed cap"),
        ("--braid-backend", str, "free-product", ("free-product", "matrix"),
         "exact decision backend for a source braid on at most three strands"),
        ("--no-braid-reduction", None, False, None, "disable singleton endpoint destabilization"),
        ("--no-seifert", None, False, None, "disable the linear signed Seifert graph certificate"),
        ("--backend", str, "standard", ("standard", "shared", "saturated", "euler", "shadow", "closure", "twist", "barcode", "fitting"),
         "Khovanov backend, including optional sharing, twists, intervals, or scalar splitting"),
        ("--euler-max-states", int, 4096, None, "state budget for optional Euler continuation"),
        ("--shadow-max-work", int, 1_000_000, None, "work allowance for optional marked determinant continuations"),
        ("--closure-max-work", int, 1_000_000, None, "work allowance for optional classical closure bounds and resets"),
        ("--max-objects", int, None, None, "ceiling on objects of the scanning complex (UNKNOWN when exceeded)"),
        ("--seconds", float, None, None, "cooperative time budget"),
        ("--no-reduction", None, False, None, None),
        ("--no-descending", None, False, None, None),
        ("--no-alexander", None, False, None, "disable both Alexander stages"),
        ("--no-r3", None, False, None, "no Reidemeister III search before the Khovanov scan"),
        ("--r3-search", str, "last", ("last", "clustered", "adaptive"), "bounded RIII search implementation"),
        ("--r3-depth", int, 4, None, "maximum RIII moves per unlocking sequence"),
        ("--r3-budget", int, 10, None, "RIII trial allowance per input crossing"),
        ("--r3-births", int, 1, None, "maximum independent starting moves in clustered RIII search"),
        ("--exact-alexander", None, False, None,
         "also compute the exact Alexander polynomial after the modular test passed"),
        ("--no-modular", None, False, None, "disable only the modular Alexander stage"),
        ("--no-jones", None, False, None, None),
        ("--no-factor", None, False, None, "do not split visible connected sums"),
        ("--legacy-factor", None, False, None, "use the historical recursive two-edge-cut factorizer"),
        ("--jones-backend", str, "matching", JONES_BACKENDS, "one-sided Jones obstruction implementation"),
        ("--potts-colors", int, 6, None, "integer color count for exact Potts filters (at least 5; faithful derives its own)"),
        ("--jones-max-transitions", int, 200000, None, "local Jones transition budget"),
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
        ("--reduction", str, "standard", ("standard", "residue", "adaptive", "disk-adaptive", "graded", "graded-adaptive", "corridor", "corridor-adaptive"),
         "chain cancellation strategy, including optional survivor and full-transfer policies"),
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
        ("--minimal", None, False, None, "cancel before truncating; certify nice-order binomial bounds"),
        ("--lower", int, 0, None, "first queried homological degree"),
        ("--upper", int, 0, None, "last queried homological degree"),
        ("--normalized", None, False, None, "interpret endpoints after subtracting the PD negative-crossing count"),
        ("--auto-mirror", None, False, None, "select the mirror with the smaller proved object bound"),
        ("--max-objects", int, None, None, "ceiling on retained objects before allocation"),
        ("--seconds", float, None, None, "cooperative time budget including order and mirror selection"),
        ("--check-d2", None, False, None, "verify d^2=0 after each crossing"),
        ("--reduction", str, "standard", ("standard", "residue", "adaptive", "disk-adaptive"), "cancellation strategy"),
        ("--composition", str, "standard", ("standard", "component", "component-dense"), "coefficient engine"),
        ("--composition-max-variables", int, 18, None, "component allocation limit"),
    ],
    "jones": [
        ("--backend", str, "matching", JONES_BACKENDS, "Jones obstruction implementation"),
        ("--potts-colors", int, 6, None, "integer color count for exact Potts filters (at least 5; faithful derives its own)"),
        ("--max-states", int, None, None, "represented-state budget"),
        ("--max-transitions", int, None, None, "transition budget"),
    ],
    "alexander": [],
}
COMMAND_HELP = {"recognize": "decide whether a knot diagram is the unknot",
                "khovanov": "total F2 Khovanov rank by scanning",
                "window": "exact partial F2 homology; raw degrees unless --normalized",
                "jones": "one-sided Jones obstruction", "alexander": "Alexander polynomial"}


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
    if args.command in ("recognize", "jones"):
        try:
            validate_jones_options(
                args.jones_backend if args.command == "recognize" else args.backend,
                args.potts_colors,
                args.jones_max_states if args.command == "recognize" else args.max_states,
                args.jones_max_transitions if args.command == "recognize" else args.max_transitions)
        except ValueError as exc:
            print(f"invalid Jones options: {exc}", file=sys.stderr)
            return 2
    if args.command in ("recognize", "khovanov"):
        if args.reduction in ("graded", "graded-adaptive", "corridor", "corridor-adaptive") and getattr(args, "window_radius", None) is not None:
            print("graded/corridor reduction cannot be combined with --window-radius", file=sys.stderr)
            return 2
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
            if args.ranktwo_seconds < 0 or not args.ranktwo_seconds < float("inf"):
                raise ValueError("--ranktwo-seconds must be finite and nonnegative")
            if args.garside_seconds < 0 or not args.garside_seconds < float("inf"):
                raise ValueError("--garside-seconds must be finite and nonnegative")
            if args.garside_radius < 1 or args.garside_max_targets < 1 or args.garside_max_ticks < 0:
                raise ValueError("Garside radius/target ceiling must be positive and ticks nonnegative")
            if args.window_seconds < 0 or not args.window_seconds < float("inf"):
                raise ValueError("--window-seconds must be finite and nonnegative")
            if args.window_radius is not None and args.window_radius < 0:
                raise ValueError("--window-radius must be nonnegative")
            if args.window_max_objects < 0:
                raise ValueError("--window-max-objects must be nonnegative")
        except ValueError as exc:
            print(f"invalid probe/window options: {exc}", file=sys.stderr)
            return 2
        if args.euler_max_states < 0:
            print("--euler-max-states must be nonnegative", file=sys.stderr)
            return 2
        if args.shadow_max_work < 0:
            print("--shadow-max-work must be nonnegative", file=sys.stderr)
            return 2
        if args.closure_max_work < 0:
            print("--closure-max-work must be nonnegative", file=sys.stderr)
            return 2
        if args.backend != "standard" and (args.pivot != "minfill" or args.algebra != "bits"
                                            or args.tail != 0 or args.race != 1):
            print("alternate backends require minfill, bits, tail=0, and race=1", file=sys.stderr)
            return 2
        result = recognize(diagram, use_reduction=not args.no_reduction,
                           use_ranktwo=args.ranktwo, ranktwo_seconds=args.ranktwo_seconds,
                           use_garside=args.garside, garside_radius=args.garside_radius,
                           garside_seconds=args.garside_seconds, garside_max_ticks=args.garside_max_ticks,
                           garside_max_targets=args.garside_max_targets,
                           window_radius=args.window_radius, window_strategy=args.window_strategy, window_max_objects=args.window_max_objects,
                           window_seconds=args.window_seconds,
                           use_seifert=not args.no_seifert, backend=args.backend,
                           twist_max_basis=args.twist_max_basis,
                           composition=args.composition, composition_max_variables=args.composition_max_variables,
                           reduction=args.reduction,
                           use_braid=not args.no_braid, braid_backend=args.braid_backend,
                           use_rational=not args.no_rational,
                           use_treewidth_two=args.treewidth_two, treewidth_two_seconds=args.treewidth_two_seconds,
                           use_regina=args.regina, regina_seconds=args.regina_seconds,
                           use_group=args.group or args.group_relators or args.group_compressed or args.group_compressed_search,
                           group_seconds=args.group_seconds, group_compressed=args.group_compressed,
                           group_compressed_search=args.group_compressed_search,
                           group_relators=args.group_relators, group_max_work=args.group_max_work,
                           use_braid_profile=args.braid_profile,
                           use_braid_reduction=not args.no_braid_reduction,
                           euler_max_states=args.euler_max_states,
                           shadow_max_work=args.shadow_max_work,
                           closure_max_work=args.closure_max_work,
                           use_descending=not args.no_descending,
                           use_alexander=not args.no_alexander, use_modular=not args.no_modular,
                           use_exact_alexander=True if args.exact_alexander else None, use_r3=not args.no_r3,
                           r3_search=args.r3_search, r3_depth=args.r3_depth,
                           r3_budget=args.r3_budget, r3_births=args.r3_births,
                           race=args.race, race_after=args.race_after,
                           use_jones=not args.no_jones, use_factorization=not args.no_factor,
                           factor_backend="legacy" if args.legacy_factor else "interlacement",
                           jones_backend=args.jones_backend, potts_colors=args.potts_colors,
                           jones_max_transitions=args.jones_max_transitions,
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
            if args.minimal:
                from .minimal_window import khovanov_minimal_window_auto
                result = khovanov_minimal_window_auto(diagram, args.lower + shift, args.upper + shift,
                                                       mirror=args.auto_mirror, **options)
            elif args.auto_mirror:
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
        statistics = {}
        try:
            test, _, extra = select_jones_filter(args.backend, args.potts_colors)
            if args.backend == "potts-faithful":
                extra.update(statistics=statistics, include_polynomial=True)
            witness = test(diagram, max_states=args.max_states,
                           max_transitions=args.max_transitions, **extra)
        except (FilterLimit, MemoryError) as exc:
            print(json.dumps({"verdict": "INCONCLUSIVE", "witness": None,
                              "reason": str(exc) or "memory allocation failed"}))
            return 3
        result = {"verdict": "KNOTTED" if witness else "INCONCLUSIVE", "witness": witness}
        for field in ("polynomial_identity", "jones_polynomial"):
            if field in statistics:
                result[field] = statistics[field]
        print(json.dumps(result, indent=1))
        return 0
    poly = alexander_polynomial(diagram)
    print(json.dumps({"alexander_polynomial": format_polynomial(poly), "coefficients": poly}))
    return 0


if __name__ == "__main__":
    sys.exit(main())

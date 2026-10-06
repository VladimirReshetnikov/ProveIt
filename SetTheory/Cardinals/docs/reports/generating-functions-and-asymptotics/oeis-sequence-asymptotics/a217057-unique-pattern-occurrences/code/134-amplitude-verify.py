#!/usr/bin/env python3
"""Fail-closed offline verification and deterministic packaging for Report 134."""
import sys
sys.dont_write_bytecode = True

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import os
from pathlib import Path
import stat
import subprocess
import types
import zipfile

PAYLOAD = frozenset({"README.md", "Report134.tex", "Report134.pdf", "certificate.py",
                     "independent.py", "fixtures.json", "verify.py"})
MANIFEST = "manifest.json"
ROOT = Path(__file__).absolute().parent
SCHEMA = "report134-sha256-v1"
EXPECTED_N = 6958884420052382006187220194732220723168380665062
EXPECTED_D = 13915193059764305937984450503671774362956903094027
OEIS_VALUES = (0,0,0,0,1,12,102,770,5545,39220,276144,1948212,
               13817680,98679990,710108396,5150076076)


class Rejected(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def parse_json(data):
    return json.loads(data.decode("utf-8"), object_pairs_hook=no_duplicate_keys)


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True)+"\n").encode("ascii")


def lexical_absolute(value):
    path = Path(value)
    require(".." not in path.parts, "parent traversal is not permitted")
    return path if path.is_absolute() else Path.cwd()/path


def check_ancestors(path, leaf_may_be_absent=False):
    """Check lexical components, without resolve() hiding a symlink."""
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:]):
        current /= part
        leaf = index == len(path.parts)-2
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            require(leaf and leaf_may_be_absent, "missing ancestor: " + str(current))
            return
        require(not stat.S_ISLNK(mode), "symlink component refused: " + str(current))
        if not leaf:
            require(stat.S_ISDIR(mode), "non-directory ancestor: " + str(current))


def read_regular(path):
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, "rb") as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "nonregular file refused")
        return stream.read()


def inventory(root, sealed):
    check_ancestors(root)
    require(root.is_dir(), "bundle root is not a directory")
    expected = PAYLOAD | ({MANIFEST} if sealed else set())
    with os.scandir(root) as entries:
        found = {}
        for entry in entries:
            mode = entry.stat(follow_symlinks=False).st_mode
            require(stat.S_ISREG(mode), "unexpected directory, symlink, or nonregular entry: " + entry.name)
            found[entry.name] = entry
    require(set(found) == expected,
            "closed inventory mismatch; missing="+str(sorted(expected-set(found)))+
            "; extra="+str(sorted(set(found)-expected)))
    return {name: read_regular(root/name) for name in sorted(expected)}


def verify(root=ROOT):
    data = inventory(root, True)
    manifest = parse_json(data[MANIFEST])
    require(set(manifest) == {"schema", "files"}, "manifest keys")
    require(manifest["schema"] == SCHEMA, "manifest schema")
    require(type(manifest["files"]) is dict and set(manifest["files"]) == PAYLOAD,
            "manifest must list exactly the closed payload")
    for name in sorted(PAYLOAD):
        record = manifest["files"][name]
        require(type(record) is dict and set(record) == {"bytes", "sha256"}, "manifest file record")
        require(type(record["bytes"]) is int and record["bytes"] == len(data[name]), "size mismatch: " + name)
        require(record["sha256"] == hashlib.sha256(data[name]).hexdigest(), "SHA256 mismatch: " + name)
    require(data["Report134.pdf"].startswith(b"%PDF-"), "report is not a PDF")
    validate_fixtures(data)
    return data


def preflight_output(value):
    path = lexical_absolute(value)
    check_ancestors(path, leaf_may_be_absent=True)
    require(not path.exists() and not path.is_symlink(), "output already exists: " + str(path))
    require(ROOT != path and ROOT not in path.parents, "output must be outside the bundle")
    require(path.parent.is_dir(), "output parent must already exist")
    return path


def create_output_directory(path):
    # The final mkdir is exclusive. Recheck ancestors immediately before creating.
    check_ancestors(path, leaf_may_be_absent=True)
    os.mkdir(path, mode=0o700)


def create_output_file(path):
    check_ancestors(path, leaf_may_be_absent=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    return os.fdopen(os.open(path, flags, 0o600), "wb")


def load_verified(data, name):
    module = types.ModuleType(name[:-3])
    exec(compile(data[name], name, "exec"), module.__dict__)
    return module


def validate_fixtures(data):
    """Closed, typed fixture schemas: JSON bool/float never count as integers."""
    def keys(value, expected, label):
        require(type(value) is dict and set(value) == set(expected), label + " keys/type")
    def string(value, expected, label):
        require(type(value) is str and value == expected, label + " string/value")
    def integer(value, expected, label):
        require(type(value) is int and value == expected, label + " integer/value")
    fixture = parse_json(data["fixtures.json"])
    keys(fixture, ("schema", "oeis", "certificate", "positive_series_first_term"), "fixture")
    string(fixture["schema"], "report134-fixtures-v1", "fixture schema")
    oeis = fixture["oeis"]
    keys(oeis, ("sequence", "source_url", "retrieved", "description", "offset", "values"), "OEIS")
    string(oeis["sequence"], "A217057", "OEIS sequence")
    string(oeis["source_url"], "https://oeis.org/A217057", "OEIS source URL")
    string(oeis["retrieved"], "2026-10-02", "OEIS retrieval date")
    string(oeis["description"],
           "Number of permutations in S_n containing exactly one increasing subsequence of length 4",
           "OEIS description")
    integer(oeis["offset"], 0, "OEIS offset")
    require(type(oeis["values"]) is list and len(oeis["values"]) == len(OEIS_VALUES), "OEIS values list/length")
    for index, expected in enumerate(OEIS_VALUES):
        integer(oeis["values"][index], expected, "OEIS count n=" + str(index))
    c = fixture["certificate"]
    keys(c, ("T", "I", "numerator", "denominator", "strict_threshold_numerator", "strict_threshold_denominator"),
         "certificate")
    for key, expected in (("T", 40), ("I", 10), ("strict_threshold_numerator", 50009),
                          ("strict_threshold_denominator", 100000)):
        integer(c[key], expected, "certificate " + key)
    string(c["numerator"], str(EXPECTED_N), "certificate numerator")
    string(c["denominator"], str(EXPECTED_D), "certificate denominator")
    string(fixture["positive_series_first_term"], "35/324", "first-term fixture")
    return fixture


def standardize(values):
    rank = {value: i+1 for i, value in enumerate(sorted(values))}
    return tuple(rank[value] for value in values)


def direct_permutations(primary, max_n):
    """Literal 4-position subsets, independent of RSK and the convolution."""
    north_cells = {(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)}
    south_cells = {(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)}
    all_halves, fibers, rows = {}, {}, []
    for n in range(max_n+1):
        quads = list(itertools.combinations(range(n), 4))
        avoidance_histogram = Counter()
        northern = Counter()
        pairs = Counter()
        unique = 0
        for p in itertools.permutations(range(1,n+1)):
            count, chain = 0, None
            for a,b,c,d in quads:
                if p[a] < p[b] < p[c] < p[d]:
                    count += 1
                    chain = (a,b,c,d)
                    if count == 2:
                        break
            if count == 0:
                inv = [0]*n
                for pos, value in enumerate(p):
                    inv[value-1] = pos
                rp = rq = int(n > 0)
                while rp < n and p[n-rp-1] > p[n-rp]:
                    rp += 1
                while rq < n and inv[rq-1] > inv[rq]:
                    rq += 1
                avoidance_histogram[rp,rq] += 1
            elif count == 1:
                unique += 1
                chain_values = tuple(p[pos] for pos in chain)
                chain_set = set(chain)
                north, south, nc = [], [], Counter()
                cell_points = {}
                for pos, value in enumerate(p):
                    if pos in chain_set:
                        continue
                    cell = (sum(x < pos for x in chain), sum(x < value for x in chain_values))
                    require(cell in north_cells | south_cells, "direct twelve-cell restriction")
                    cell_points.setdefault(cell, []).append(value)
                    if cell in north_cells:
                        north.append(pos)
                        nc[cell] += 1
                    else:
                        south.append(pos)
                for cell in ((2,4),(0,2),(2,0),(4,2)):
                    values = cell_points.get(cell, [])
                    require(all(x > y for x,y in zip(values, values[1:])), "direct central-cell descent")
                pn = standardize([p[pos] for pos in sorted(chain_set | set(north))])
                ps = standardize([p[pos] for pos in sorted(chain_set | set(south))])
                ps = tuple(len(ps)+1-value for value in reversed(ps))
                pairs[pn,ps] += 1
                if not south:
                    northern[nc[(2,4)], nc[(0,2)]] += 1
                    all_halves[p] = (nc[(2,4)], nc[(0,2)])
        brute_F = [[sum(value for (a,b),value in avoidance_histogram.items() if a >= i and b >= j)
                    for j in range(n+1)] for i in range(n+1)]
        require(brute_F == primary.boundary(n), "direct boundary matrix mismatch n="+str(n))
        require(unique == primary.exact_count(n), "direct unique-count mismatch n="+str(n))
        if n >= 4:
            expected_H = {key:value for key,value in primary.halves(n-4).items() if value}
            require(dict(northern) == expected_H, "direct northern-half mismatch")
            fibers[n] = pairs
        rows.append({"n":n, "avoiders":sum(avoidance_histogram.values()), "unique_1234":unique,
                     "F_entries_checked":(n+1)**2})
    fiber_rows = []
    for n, pairs in fibers.items():
        expected = {}
        for a, (i,j) in all_halves.items():
            for b, (k,l) in all_halves.items():
                if len(a)+len(b) == n+4:
                    expected[a,b] = __import__("math").comb(i+k,i)*__import__("math").comb(j+l,j)
        require(dict(pairs) == expected, "direct gluing-fiber mismatch")
        fiber_rows.append({"n":n, "ordered_half_pairs":len(expected), "gluings":sum(expected.values())})
    return rows, fiber_rows


def mutation_checks(primary, independent, layers):
    detected = []
    def mismatch(label, actual, expected):
        require(actual != expected, "mutation went undetected: " + label)
        detected.append(label)
    # Remove both shuffle factors from the complete n=8 convolution.
    mutated = sum(sum(layers[s].values())*sum(layers[4-s].values()) for s in range(5))
    mismatch("omit_binomial_shuffles", mutated, OEIS_VALUES[8])
    # Change the H subtraction to addition at the smallest half.
    mismatch("half_subtraction_to_addition", (primary.boundary(2)[1][1]+primary.boundary(1)[0][0])**2, 1)
    # Replace horizontal strips by mere containment at shape (1,1,0).
    outer, inner = (1,1,0), (0,0,0)
    mismatch("containment_instead_of_horizontal_strip", all(a >= b for a,b in zip(outer,inner)), independent.is_horizontal(outer,inner))
    reconstructed, _ = primary.finite_certificate(layers, 10)
    mismatch("drop_endpoint_factor_two", reconstructed/2, Fraction(EXPECTED_N,EXPECTED_D))
    _, series_terms = primary.positive_series(layers)
    mismatch("double_series_denominator", Fraction(38**2-18**2,20736), series_terms[0])
    S = sum((primary.d(i) for i in range(11)), Fraction())
    P = sum((primary.d(i+1) for i in range(11)), Fraction())
    mismatch("shift_boundary_index", 81*S*S-9*S*S, 81*P*P-9*S*S)
    return detected


def replay(data, max_n):
    validate_fixtures(data)
    primary = load_verified(data, "certificate.py")
    independent = load_verified(data, "independent.py")
    print("Reconstructing every boundary matrix through size 42 by two algorithms", flush=True)
    matrices, dimensions = independent.boundary_layers(42)
    for n, matrix in enumerate(matrices):
        require(matrix == primary.boundary(n), "independent F mismatch n="+str(n))
        require(dimensions[n] == {s:primary.dimension(s) for s in primary.partitions3(n)},
                "recursive/hook dimensions disagree")
    H = independent.half_layers(matrices, 40)
    require(H == [primary.halves(t) for t in range(41)], "independent H mismatch")
    value, partials = primary.finite_certificate(H, 10)
    other, other_partials = independent.direct_kernel_certificate(H, 10)
    expected = Fraction(EXPECTED_N, EXPECTED_D)
    require(value == other == expected and partials == other_partials, "finite certificate mismatch")
    require(value > Fraction(50009,100000) > Fraction(1,2), "strict rational threshold failure")
    for k in range(50):
        D, E = independent.generating_function_boundary(k)
        require(D == Fraction(3,16)*(k*k+11*k+18)*Fraction(3,2)**k, "D coefficient mismatch")
        require(E == Fraction(1,16)*(k*k+15*k+38)*Fraction(3,2)**k, "E coefficient mismatch")
    positive_partial, positive_terms = primary.positive_series(H)
    require(positive_terms[0] == Fraction(35,324), "positive-series first term")
    require(positive_partial > value, "infinite-boundary partial sum must exceed finite-I truncation")
    computed = [primary.exact_count(n, H) for n in range(16)]
    require(tuple(computed) == OEIS_VALUES, "OEIS n=0..15 mismatch")
    print("Exact certificate agrees; checking literal permutations and gluing fibers", flush=True)
    permutation_rows, fiber_rows = direct_permutations(primary, max_n)
    mutations = mutation_checks(primary, independent, H)
    return {"schema":"report134-replay-v1", "status":"PASS", "T":40, "I":10,
            "certificate":str(value), "gap_over_one_half":str(value-Fraction(1,2)),
            "gap_over_50009_100000":str(value-Fraction(50009,100000)),
            "primary_and_independent_certificates_equal":True,
            "finite_certificate_partials":list(map(str,partials)),
            "boundary_matrix_sizes_checked":list(range(43)),
            "recursive_dimensions_checked":sum(len(layer) for layer in dimensions),
            "boundary_closed_forms_checked_k":list(range(50)),
            "positive_series_first_term":str(positive_terms[0]),
            "positive_series_partial_through_40":str(positive_partial),
            "positive_series_partial_is_only_a_lower_bound":True,
            "oeis_n0_through_15":computed, "direct_permutations":permutation_rows,
            "direct_gluing_fibers":fiber_rows, "arithmetic_mutations_detected":mutations}


def seal():
    data = inventory(ROOT, False)
    validate_fixtures(data)
    require(data["Report134.pdf"].startswith(b"%PDF-"), "report is not a PDF")
    record = {"schema":SCHEMA, "files":{name:{"bytes":len(data[name]), "sha256":hashlib.sha256(data[name]).hexdigest()}
                                       for name in sorted(PAYLOAD)}}
    # This explicit maintainer command is the ONLY command that writes in ROOT.
    with create_output_file(ROOT/MANIFEST) as stream:
        stream.write(json_bytes(record))
    verify()
    print("Sealed exact payload inventory; manifest.json created exclusively")


def pack(data, destination):
    with create_output_file(destination) as stream:
        # ZIP_STORED avoids zlib-version-dependent output. All metadata is fixed.
        with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_STORED) as archive:
            for name in sorted(data):
                info = zipfile.ZipInfo("Report134/"+name, date_time=(1980,1,1,0,0,0))
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.compress_type = zipfile.ZIP_STORED
                info.flag_bits = 0
                archive.writestr(info, data[name])
    print("Packed deterministic ZIP: " + str(destination))
    print("SHA256 " + hashlib.sha256(read_regular(destination)).hexdigest())


def build(data, destination):
    # Frozen sources are copied externally; TeX never writes into the bundle.
    create_output_directory(destination)
    tex = destination/"Report134.tex"
    with create_output_file(tex) as stream:
        stream.write(data["Report134.tex"])
    environment = os.environ.copy()
    environment.update({"SOURCE_DATE_EPOCH":"1790899200", "FORCE_SOURCE_DATE":"1", "TZ":"UTC", "LC_ALL":"C"})
    for variable, folder in (("TEXMFVAR", "texmf-var"), ("TEXMFCONFIG", "texmf-config"),
                             ("TEXMFCACHE", "texmf-cache"), ("XDG_CACHE_HOME", "xdg-cache")):
        directory = destination/folder
        directory.mkdir()
        environment[variable] = str(directory)
    if Path("/usr/share/texlive/texmf-dist").is_dir():
        # Search real system trees even when TeX's filename database is absent.
        environment["TEXMF"] = "{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
    environment["TEXFORMATS"] = str(destination)+"//:"
    format_command = ["pdftex", "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
                      "-halt-on-error", "-jobname=pdflatex", "pdflatex.ini"]
    source = r"\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report134.tex}"
    command = ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", source]
    with create_output_file(destination/"build-console.txt") as log:
        subprocess.run(format_command, cwd=destination, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)
        for _ in range(2):
            subprocess.run(command, cwd=destination, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)
    tex_log = read_regular(destination/"Report134.log").decode("utf-8", errors="replace")
    for warning in (r"Overfull \hbox", r"Overfull \vbox", "undefined references", "multiply defined",
                    "undefined citations", "Missing character:", "Label(s) may have changed"):
        require(warning not in tex_log, "TeX QA warning: " + warning)
    result = read_regular(destination/"Report134.pdf")
    with create_output_file(destination/"build-result.json") as stream:
        stream.write(json_bytes({"pdf_sha256":hashlib.sha256(result).hexdigest(),
                                 "matches_frozen_pdf_bytes":result == data["Report134.pdf"],
                                 "source_date_epoch":1790899200}))
    print("Built PDF externally; see build-result.json for byte comparison")


def selftest(data, destination):
    """All corruption and rejection trials operate on external copies."""
    create_output_directory(destination)
    passed = []
    def copied(name):
        path = destination/name
        path.mkdir()
        for filename, value in data.items():
            with create_output_file(path/filename) as stream:
                stream.write(value)
        return path
    def invoke(root, arguments, expect_success):
        command = [sys.executable, "-I", "-B", "-O", str(root/"verify.py")] + arguments
        run = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require((run.returncode == 0) == expect_success,
                "selftest unexpected exit: " + " ".join(arguments) + " " + run.stderr.decode(errors="replace"))
    clean = copied("clean")
    invoke(clean, ["check"], True)
    passed.append("clean_copy_under_python_O")
    source_link = destination/"linked_bundle"
    source_link.symlink_to(clean, target_is_directory=True)
    invoke(source_link, ["check"], False)
    passed.append("symlink_bundle_ancestor")
    tests = [
        ("extra_file", lambda p: (p/"extra").write_text("x")),
        ("extra_directory", lambda p: (p/"extra").mkdir()),
        ("symlink_file", lambda p: (p/"extra").symlink_to(p/"README.md")),
        ("broken_symlink", lambda p: (p/"extra").symlink_to(p/"absent")),
        ("changed_fixture", lambda p: (p/"fixtures.json").write_bytes(data["fixtures.json"]+b" ")),
        ("missing_pdf", lambda p: (p/"Report134.pdf").unlink()),
    ]
    if hasattr(os, "mkfifo"):
        tests.append(("nonregular_fifo", lambda p: os.mkfifo(p/"extra")))
    for name, mutate in tests:
        target = copied(name)
        mutate(target)
        invoke(target, ["check"], False)
        passed.append(name)
    # Recompute the local test manifest so these failures exercise fixture
    # semantics rather than merely detect changed bytes.
    typed_fixture_tests = [
        ("fixture_oeis_extra_key", lambda f: f["oeis"].update({"extra": 1})),
        ("fixture_certificate_extra_key", lambda f: f["certificate"].update({"extra": 1})),
        ("fixture_wrong_description", lambda f: f["oeis"].update({"description": "wrong"})),
        ("fixture_wrong_source", lambda f: f["oeis"].update({"source_url": "https://example.invalid"})),
        ("fixture_boolean_offset", lambda f: f["oeis"].update({"offset": False})),
        ("fixture_float_offset", lambda f: f["oeis"].update({"offset": 0.0})),
        ("fixture_boolean_count", lambda f: f["oeis"]["values"].__setitem__(0, False)),
        ("fixture_float_count", lambda f: f["oeis"]["values"].__setitem__(15, 5150076076.0)),
        ("fixture_float_cutoff_T", lambda f: f["certificate"].update({"T": 40.0})),
        ("fixture_float_cutoff_I", lambda f: f["certificate"].update({"I": 10.0})),
        ("fixture_float_threshold", lambda f: f["certificate"].update({"strict_threshold_numerator": 50009.0})),
        ("fixture_float_threshold_denominator", lambda f: f["certificate"].update({"strict_threshold_denominator": 100000.0})),
    ]
    for label, transform in typed_fixture_tests:
        target = copied(label)
        fixture = parse_json(data["fixtures.json"])
        transform(fixture)
        fixture_bytes = json_bytes(fixture)
        (target/"fixtures.json").write_bytes(fixture_bytes)
        manifest = parse_json(data[MANIFEST])
        manifest["files"]["fixtures.json"] = {"bytes":len(fixture_bytes), "sha256":hashlib.sha256(fixture_bytes).hexdigest()}
        (target/MANIFEST).write_bytes(json_bytes(manifest))
        invoke(target, ["check"], False)
        passed.append(label)
    for label, transform in [
        ("manifest_extra_record", lambda m: m["files"].update({"extra":{"bytes":0,"sha256":"0"*64}})),
        ("manifest_missing_record", lambda m: m["files"].pop("README.md")),
    ]:
        target = copied(label)
        manifest = parse_json(data[MANIFEST])
        transform(manifest)
        (target/MANIFEST).write_bytes(json_bytes(manifest))
        invoke(target, ["check"], False)
        passed.append(label)
    target = copied("manifest_duplicate_key")
    (target/MANIFEST).write_bytes(data[MANIFEST].replace(b'{', b'{"schema":"duplicate",', 1))
    invoke(target, ["check"], False)
    passed.append("manifest_duplicate_key")
    # Output failures are checked before any costly replay and create no files.
    existing = destination/"existing"
    existing.mkdir()
    link = destination/"linked_parent"
    link.symlink_to(existing, target_is_directory=True)
    existing_file = destination/"existing-file"
    existing_file.write_text("preserve this exact content", encoding="utf-8")
    for label, output in [("existing_output",existing), ("existing_file_output",existing_file),
                          ("inside_bundle_output",clean/"generated"), ("symlink_leaf_output",link),
                          ("parent_traversal_output",existing/".."/"traversed"),
                          ("symlink_ancestor_output",link/"generated")]:
        invoke(clean, ["replay", "--output", str(output)], False)
        require(not (clean/"generated").exists() and not (existing/"generated").exists(), "preflight created output")
        passed.append(label)
    require(existing_file.read_text(encoding="utf-8") == "preserve this exact content", "existing output changed")
    packed = destination/"first.zip"
    invoke(clean, ["pack","--output",str(packed)], True)
    unpack = destination/"fresh_extraction"
    unpack.mkdir()
    with zipfile.ZipFile(packed) as archive:
        archive.extractall(unpack)
    second = destination/"second.zip"
    invoke(unpack/"Report134", ["pack","--output",str(second)], True)
    require(read_regular(packed) == read_regular(second), "ZIP repack not byte-identical")
    passed.append("fresh_extraction_byte_identical_zip")
    with create_output_file(destination/"selftest-result.json") as stream:
        stream.write(json_bytes({"status":"PASS","tests":passed}))
    print("Selftest PASS: " + str(len(passed)) + " rejection/repack checks")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check", help="verify closed inventory and SHA256, read-only")
    sub.add_parser("seal", help="MAINTAINER ONLY: create absent manifest.json intentionally")
    for name in ("replay", "pack", "build", "selftest"):
        command = sub.add_parser(name)
        command.add_argument("--output", required=True, help="new external path; existing parent required")
        if name == "replay":
            command.add_argument("--max-permutation-n", type=int, choices=(8,9), default=8)
    args = parser.parse_args()
    if args.command == "seal":
        seal()
        return
    output = preflight_output(args.output) if hasattr(args, "output") else None
    data = verify()
    if args.command == "check":
        print("PASS: closed inventory, regular files, all SHA256 digests, and typed fixtures")
    elif args.command == "replay":
        create_output_directory(output)
        result = replay(data, args.max_permutation_n)
        with create_output_file(output/"replay-result.json") as stream:
            stream.write(json_bytes(result))
        print("PASS: " + str(output/"replay-result.json"))
    elif args.command == "pack":
        pack(data, output)
    elif args.command == "build":
        build(data, output)
    elif args.command == "selftest":
        selftest(data, output)


if __name__ == "__main__":
    try:
        main()
    except (Rejected, ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        print("REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)

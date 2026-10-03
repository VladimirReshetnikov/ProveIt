#!/usr/bin/env python3
"""Pinned, read-only publication audit for signal Parts V/VI at ef114b0bb.

Only Git blobs and ZIP members are read. No report code is imported/executed.
Normalizations and allowed proof/display deduplications are explicit below.
"""
from __future__ import annotations
import argparse, collections, difflib, hashlib, io, json, pathlib, re
import stat, subprocess, tempfile, zipfile

if not __debug__:
    raise RuntimeError("Run without -O: audit assertions are required")

HERE = pathlib.Path(__file__).resolve().parent
COMMIT = "ef114b0bb400c2f21e1885dd16cc90a0e346b3f4"
BEFORE = "ecc9185aaba684dfa80c804511537cbea4738f3b"
ARRIVAL = "4e270aa4648c5fd7e18626507531046715976535"
REPORT = "SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/"
PACKAGES = [
    ("tm", "Three_Mass_Reversible_Computation.zip", "three-mass-release/three-mass-report.tex"),
    ("ct", "Exact_Targets_Three_Mass_Units.zip", "clean-target-release/clean-target-report.tex"),
    ("su", "Single_Unit_Three_Mass_Decidability (1).zip", "single-unit-three-mass/single-unit-mass-three.tex"),
    ("fm", "Four_Mass_Decidability_Package.zip", "four-mass-bound/four-mass-decidability.tex"),
]
PINS = {'ecc9185aaba684dfa80c804511537cbea4738f3b': {'article.tex': '6108d3228e19510ad3fcaea2dbeaec65a5f6dbf3c97530470834ce511035fe93', 'README.md': '75a120a08d92bab1b5477492cab50fd93a3f6154ef787bc5cf30e3d99a76e505', 'article.pdf': '6f5f5aae58a4ceb6914bd98701e75f1554096072d84983d2f6492977becbc53f'}, 'ef114b0bb400c2f21e1885dd16cc90a0e346b3f4': {'article.tex': '87c3cf471ae550b521c6a2166c3d1725fd840c36710628e37f870087544fe89b', 'README.md': '0ac9d473fee0f20de1f6cf1addf4c86bd5096f44dda509718daf0818db9da8a0', 'article.pdf': 'a30742f01a3bc560f35777999b7402939b3bed32348571e97adaad9465e9b895'}}
EXPECTED = {'tm': {'archive_sha256': 'fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de', 'member': 'three-mass-release/three-mass-report.tex', 'member_sha256': '8bfdbf66399fa40bd4219497abb11c78cfece41b0a4270d9d742ad7111f7930b', 'formal': {'source': 23, 'target': 23, 'matches': 22, 'missing': [[22, 702, '39fe1430178d8e0f1e06ee642dc2639b3b4ec12e9a1eaa2a41252c0fc75a5c5d']], 'extra': [22]}, 'display': {'source': 45, 'target': 40, 'matches': 40, 'missing': [[35, 636, '86a45e1dd264fb42b58ee3c64bc4bbda4c6fc1df4272a287262c299d9bd5b035'], [36, 644, 'e0504b8db7e429cf70a1c648d877828d70062cf93a639abda149388200d17356'], [37, 649, '26f991b5206da27c07bfe420b700c32b0e7605b76919cc7528e9af5e4191fbee'], [38, 657, '59c4162a4037a64bc81b1d9fdbe5f28f33fff62068276a85e5a3eed3a01db919'], [39, 665, 'b86332420c969b61f3765c9076f18c92cfd0a90ea493cabdc2e8ce49e89c461d']], 'extra': []}}, 'ct': {'archive_sha256': 'd69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc', 'member': 'clean-target-release/clean-target-report.tex', 'member_sha256': '363b4bd750a7cec9500273921f6a946844341d40fe9153d03dc7824788881f3a', 'formal': {'source': 15, 'target': 15, 'matches': 14, 'missing': [[12, 349, '1d9b523a4ceb5e70a7d323d5a5463c71d06ab5fdc90e533f469dd64834c54f07']], 'extra': [12]}, 'display': {'source': 28, 'target': 26, 'matches': 26, 'missing': [[11, 225, '3f15e5e9d712007b815c1b01b506ea07775dace21f2d15bcc932a29155458335'], [12, 231, 'fe564399e6f6440c1d27a23154a399369ecfaae4b648d23c074711e9a34b299d']], 'extra': []}}, 'su': {'archive_sha256': '299fef3508423dfe1fc88dc3473a39a40eac7cbfaf5d53c16dc26b9a3d119b12', 'member': 'single-unit-three-mass/single-unit-mass-three.tex', 'member_sha256': 'c02ff18f9ea5133884dc569bdce85aa7c53c9893e23f14efee56556fa45d5063', 'formal': {'source': 16, 'target': 16, 'matches': 16, 'missing': [], 'extra': []}, 'display': {'source': 13, 'target': 13, 'matches': 13, 'missing': [], 'extra': []}}, 'fm': {'archive_sha256': '0bcc026a8ca7bd4745b82e6f9c2841073e5fb8c639970105690fc40803a780fe', 'member': 'four-mass-bound/four-mass-decidability.tex', 'member_sha256': '803bf0c4194bb9d0f1942e6ad3eb762c79d7a811bd785742ee63f0c46a775595', 'formal': {'source': 21, 'target': 21, 'matches': 19, 'missing': [[4, 108, '06933d06808a500129124d75386b16eb05a03bfb25de7d1fad9c98706a8e70cd'], [6, 144, '507fc4e2d74bbf140a14e1a72261555facfc5837a3e866d805898e68a2448d97']], 'extra': [4, 6]}, 'display': {'source': 19, 'target': 19, 'matches': 19, 'missing': [], 'extra': []}}}
POINTER_PINS = {
    "tm": {22: "e1c976f9f4afb469368c6ef27d924041cd806c65223cd008251836d9dd71ba53"},
    "ct": {12: "3a003f57e621efbda57f91b96fdf88960bf1226277f4acb6949e4e3a5fcbc205"},
    "su": {},
    "fm": {4: "3f8a4aa08aed08d40e20513b462a5ca94081308b9e1630bda895bf8a7d552f12", 6: "c014150bfa8fe1d1c03bc9b6799881cb4474b73ea9c0a9f22c1fe09e93f67a51"},
}

REPAIRS = {
    "README.md": (
        """alphabet of Boolean channels, weight = cardinality), a fixed globally
reversible, mass-conserving cellular automaton of forward and inverse radius
at most four (radius one by four-site blocking at the same clock, or by
four-phase dilation at four times the time) simulates every separated
reversible two-counter machine at total mass exactly three, with gap
`12·2^a·3^b` and a clean halt symbol, so three is the least mass with
fixed-rule undecidable pattern occurrence there""",
        """alphabet of Boolean channels, weight = cardinality), every finite separated
reversible two-counter machine M compiles to a globally reversible,
mass-conserving cellular automaton F_M of forward and inverse radius at most
four (radius one by four-site blocking at the same clock, or by four-phase
dilation at four times the time). Its canonical simulation has total mass
exactly three, gap `12·2^a·3^b` and a clean halt symbol. Fixing a universal
source machine gives one fixed rule, so three is the least mass with
fixed-rule undecidable pattern occurrence there"""),
    "article.tex": (
        "not reversible, full paper not checked", 
        "reversibility not asserted, full paper not checked"),
}

def sha(value):
    return hashlib.sha256(value if isinstance(value, bytes) else value.encode()).hexdigest()

def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], timeout=300)

def blob(repo, commit, path):
    return git(repo, "show", commit + ":" + path)

def safe_archive(data):
    z = zipfile.ZipFile(io.BytesIO(data))
    names = z.namelist()
    assert len(names) == len(set(names)), "Duplicate archive names"
    for info in z.infolist():
        name = info.filename
        p = pathlib.PurePosixPath(name)
        assert name and not p.is_absolute() and ".." not in p.parts
        assert "\\" not in name and not re.match(r"^[A-Za-z]:", name)
        assert not stat.S_ISLNK(info.external_attr >> 16)
        assert not info.flag_bits & 1, "Encrypted member"
    return z

def clean(s):
    s = re.sub(r"(?m)(?<!\\)%.*$", "", s)
    s = re.sub(r"\\label\{[^}]*\}|\\tag\{[^}]*\}", "", s)
    s = re.sub(r"smc:(?:tm|ct|su|fm):", "", s)
    s = re.sub(r"\\N\b", r"\\NN", s)
    s = s.replace(r"\begin{equation}", r"\[").replace(r"\end{equation}", r"\]")
    s = s.replace("constant $K$ in (2),", r"constant $K$ in~\eqref{eq:counts},")
    while True:
        m = re.search(r"\\wtag\\?\s*\[", s)
        if not m:
            break
        i, depth = m.end(), 1
        while i < len(s) and depth:
            if s[i] == "[": depth += 1
            if s[i] == "]": depth -= 1
            i += 1
        assert depth == 0, "Unclosed editorial bracket"
        s = s[:m.start()] + s[i:]
    return re.sub(r"\s+", "", s)

def blocks(s, mode):
    if mode == "formal":
        kinds = "theorem|lemma|proposition|corollary|definition|remark|example|proof"
        pattern = r"\\begin\{(" + kinds + r")\}.*?\\end\{\1\}"
        starts = re.findall(r"\\begin\{(?:" + kinds + r")\}", s)
        ends = re.findall(r"\\end\{(?:" + kinds + r")\}", s)
    else:
        kinds = r"equation\*?|align\*?|gather\*?|multline\*?|displaymath"
        pattern = r"(?<!\\)\\\[.*?(?<!\\)\\\]|\\begin\{(" + kinds + r")\}.*?\\end\{\1\}"
        starts = re.findall(r"(?<!\\)\\\[|\\begin\{(?:" + kinds + r")\}", s)
        ends = re.findall(r"(?<!\\)\\\]|\\end\{(?:" + kinds + r")\}", s)
    result = [(m.start(), m.group()) for m in re.finditer(pattern, s, re.S)]
    assert len(starts) == len(ends) == len(result), "Unsupported nested or unbalanced environment"
    return result

def occurrence_census(source, target, key, mode, base_line):
    old, new = blocks(source, mode), blocks(target, mode)
    pool = collections.defaultdict(list)
    for j, (_, b) in enumerate(new): pool[clean(b)].append(j)
    matches, omitted = [], []
    for i, (offset, b) in enumerate(old):
        available = pool[clean(b)]
        if available:
            j = available.pop(0)
            matches.append({"source_index": i, "target_index": j,
                            "source_line": source[:offset].count("\n") + 1,
                            "target_line": base_line + target[:new[j][0]].count("\n"),
                            "normalized_sha256": sha(clean(b))})
        else:
            omitted.append([i, source[:offset].count("\n") + 1, sha(b)])
    extras = sorted(j for remaining in pool.values() for j in remaining)
    expected = EXPECTED[key][mode]
    assert (len(old), len(new), len(matches), omitted, extras) == (
        expected["source"], expected["target"], expected["matches"], expected["missing"], expected["extra"])
    indices = [p["target_index"] for p in matches]
    assert indices == sorted(set(indices)), "Out-of-order/reused source occurrence"
    pointers = []
    if mode == "formal":
        assert set(extras) == set(POINTER_PINS[key])
        for j in extras:
            assert sha(new[j][1]) == POINTER_PINS[key][j]
            pointers.append({"target_index": j, "sha256": sha(new[j][1]), "text": new[j][1]})
    else:
        assert not extras
    return {"source_count": len(old), "target_count": len(new), "retained_count": len(matches),
            "matches": matches, "declared_omissions": omitted, "replacement_pointers": pointers}

def braces(s, start):
    assert s[start] == "{"
    depth, i = 1, start + 1
    while depth:
        assert i < len(s)
        if s[i] == "{": depth += 1
        elif s[i] == "}": depth -= 1
        i += 1
    return s[start + 1:i - 1], i

def macros(s, *, source=False):
    result = {}
    for m in re.finditer(r"\\newcommand\{(\\[A-Za-z]+)\}(\[[0-9]+\])?", s):
        body, _ = braces(s, m.end())
        name = r"\NN" if source and m[1] == r"\N" else m[1]
        body = body.replace(r"\mathbb{N}", r"\mathbb N").replace(r"\mathbb{Z}", r"\mathbb Z")
        assert name not in result or result[name] == [m[2], clean(body)]
        result[name] = [m[2], clean(body)]
    return result

def exact_json(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)

def verify(repo):
    repo = pathlib.Path(repo).resolve()
    assert git(repo, "rev-parse", COMMIT + "^").decode().strip() == BEFORE
    changed = git(repo, "diff", "--name-only", BEFORE, COMMIT).decode().splitlines()
    assert sorted(changed) == sorted(REPORT + f for f in PINS[COMMIT])
    raw = {}
    for commit in (BEFORE, COMMIT):
        raw[commit] = {}
        for file, pin in PINS[commit].items():
            data = blob(repo, commit, REPORT + file)
            assert sha(data) == pin, (commit, file)
            raw[commit][file] = data
    article = raw[COMMIT]["article.tex"].decode()
    readme = raw[COMMIT]["README.md"].decode()
    target_macros = macros(article)
    starts = [article.index(r"\noindent{\large\bfseries Source " + str(i)) for i in range(14, 18)]
    starts += [article.index(r"\appendix")]
    packages, archives = {}, {}
    for n, (key, archive, member) in enumerate(PACKAGES):
        data = blob(repo, ARRIVAL, "docs/incoming/" + archive)
        assert sha(data) == EXPECTED[key]["archive_sha256"]
        z = safe_archive(data)
        source_bytes = z.read(member)
        assert sha(source_bytes) == EXPECTED[key]["member_sha256"]
        source = source_bytes.decode()
        target = article[starts[n]:starts[n + 1]]
        definitions = macros(source, source=True)
        for name, definition in definitions.items():
            assert target_macros[name] == definition, (key, name)
        base_line = article[:starts[n]].count("\n") + 1
        packages[key] = {"archive": archive, "archive_sha256": sha(data), "archive_bytes": len(data),
            "member": member, "member_sha256": sha(source_bytes), "macro_definitions_matched": definitions,
            "formal": occurrence_census(source, target, key, "formal", base_line),
            "display": occurrence_census(source, target, key, "display", base_line)}
        archives[key] = z
    # Authenticate the separate bounded quantifier/degree-classification read.
    challenge_pins = {
        "review_signal_batch80_quantifiers_ef114b0bb.md": "8c8da24c530858cd7125f03c1f1a79c18e19685282ff91e6b8470e8f11a6e829",
        "review_signal_batch80_quantifiers_ef114b0bb.json": "ebc448df1f277bdd13cdd356d0ecffc54aa91e9b29a0aecdbb7d9dccec616590",
    }
    for name, pin in challenge_pins.items():
        assert sha((HERE / name).read_bytes()) == pin
    challenge = json.loads((HERE / "review_signal_batch80_quantifiers_ef114b0bb.json").read_text())
    assert challenge["publication"] == COMMIT
    for info in challenge["publication_files"]:
        data = blob(repo, COMMIT, info["path"])
        assert sha(data) == info["sha256"]
        assert git(repo, "rev-parse", COMMIT + ":" + info["path"]).decode().strip() == info["blob"]
        text_lines = data.decode().splitlines()
        for anchor, expected_lines in info["anchors"].items():
            assert [i + 1 for i, line in enumerate(text_lines) if anchor in line] == expected_lines
    for info in challenge["original_sources"]:
        data = blob(repo, info["commit"], "docs/incoming/" + info["archive"])
        assert sha(data) == info["archive_sha256"]
        with safe_archive(data) as z:
            assert sha(z.read(info["member"])) == info["member_sha256"]
    # Exact companion tree identity: this commit changed only the three publication files.
    paths = git(repo, "ls-tree", "-r", "--name-only", COMMIT, "--", REPORT).decode().splitlines()
    before_paths = git(repo, "ls-tree", "-r", "--name-only", BEFORE, "--", REPORT).decode().splitlines()
    assert paths == before_paths
    listing = re.search(r"(?ms)^```\n(article\.tex.*?)(?=^```)", readme)[1]
    listed = [line.split()[0] for line in listing.splitlines() if line.strip()]
    assert sorted(listed) == sorted(path[len(REPORT):] for path in paths)
    labels = re.findall(r"\\label\{([^}]+)\}", article)
    before_labels = re.findall(r"\\label\{([^}]+)\}", raw[BEFORE]["article.tex"].decode())
    assert len(labels) == len(set(labels)) == 417 and len(before_labels) == 252
    assert [label for label in labels if label in before_labels] == before_labels
    refs = re.findall(r"\\(?:ref|eqref|pageref)\{([^}]+)\}", article)
    assert all(ref in labels for ref in refs)
    bib = re.findall(r"\\bibitem\{([^}]+)\}", article)
    old_bib = re.findall(r"\\bibitem\{([^}]+)\}", raw[BEFORE]["article.tex"].decode())
    assert len(bib) == len(set(bib)) == 48 and len(old_bib) == 36
    assert [key for key in bib if key in old_bib] == old_bib
    citations = [k.strip() for group in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", article) for k in group.split(",")]
    assert all(k in bib for k in citations)
    excluded = {}
    for name in ("cycle_rule.json", "merge_rule.json", "trap_rule.json", "mixed_certificate.json", "mixed_radius_one_certificate.json"):
        data = archives["tm"].read("three-mass-release/examples/" + name)
        excluded[name] = {"bytes": len(data), "sha256": sha(data)}
        assert not any(path.endswith(name) for path in paths)
    assert sum(p["bytes"] for p in excluded.values()) == 20752637
    fig = archives["fm"].read("four-mass-bound/figures/binary-four-particle-shuttle.pdf")
    figure_path = REPORT + "figures/17-four-mass-binary-four-particle-shuttle.pdf"
    assert blob(repo, COMMIT, figure_path) == fig
    patch = ""
    patched = {}
    for file, (old, new) in REPAIRS.items():
        text = raw[COMMIT][file].decode()
        assert text.count(old) == 1
        replaced = text.replace(old, new)
        patch += "".join(difflib.unified_diff(text.splitlines(True), replaced.splitlines(True),
                          fromfile="a/" + REPORT + file, tofile="b/" + REPORT + file))
        patched[file] = {"before_sha256": sha(text), "after_sha256": sha(replaced),
                         "source_line": text[:text.index(old)].count("\n") + 1}
    # Apply only to a private tree; no Git index/worktree mutation.
    with tempfile.TemporaryDirectory(prefix="signal-ef114-patch-") as td:
        base = pathlib.Path(td)
        for file in REPAIRS:
            path = base / REPORT / file
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw[COMMIT][file])
        subprocess.run(["git", "apply", "--check", "-"], cwd=base, input=patch.encode(), check=True, timeout=300)
        subprocess.run(["git", "apply", "-"], cwd=base, input=patch.encode(), check=True, timeout=300)
        for file, info in patched.items():
            assert sha((base / REPORT / file).read_bytes()) == info["after_sha256"]
    totals = {"formal_source": 75, "formal_retained": 71, "replacement_proof_pointers": 4,
              "display_source": 105, "display_retained": 98, "deduplicated_displays": 7}
    assert sum(p["formal"]["source_count"] for p in packages.values()) == totals["formal_source"]
    assert sum(p["formal"]["retained_count"] for p in packages.values()) == totals["formal_retained"]
    assert sum(p["display"]["source_count"] for p in packages.values()) == totals["display_source"]
    assert sum(p["display"]["retained_count"] for p in packages.values()) == totals["display_retained"]
    for z in archives.values(): z.close()
    return {"status": "PASS with two proposed presentation corrections", "commit": COMMIT,
            "parent": BEFORE, "arrival": ARRIVAL, "publication_pins": PINS,
            "changed_paths": changed, "packages": packages, "totals": totals,
            "report_file_count": len(paths), "unchanged_companion_file_count": len(paths) - 3,
            "labels": {"before": len(before_labels), "after": len(labels), "resolved_ref_occurrences": len(refs)},
            "bibliography": {"before": len(old_bib), "after": len(bib), "resolved_cite_occurrences": len(citations)},
            "excluded_exports": excluded, "unchanged_figure_sha256": sha(fig),
            "independent_challenge_pins": challenge_pins,
            "patch_sha256": sha(patch), "private_patch_application": patched,
            "scope": "Read-only publication/source transfer; no author suites, PDF build or visual QA",
            "checker_sha256": sha(pathlib.Path(__file__).read_bytes())}, patch

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--expect", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--patch-output", type=pathlib.Path)
    args = parser.parse_args()
    receipt, patch = verify(args.repo)
    if args.expect:
        assert exact_json(json.loads(args.expect.read_text())) == exact_json(receipt), "Saved receipt mismatch"
    if args.output: args.output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    if args.patch_output: args.patch_output.write_text(patch)
    print(json.dumps({"status": receipt["status"], **receipt["totals"]}, sort_keys=True))

if __name__ == "__main__":
    main()

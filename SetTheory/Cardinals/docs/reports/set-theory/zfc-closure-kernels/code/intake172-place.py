"""Batch 172 placement: three 239-state packages -> Sources 101-103 of zfc-closure-kernels.

Rules (docs/incoming/README.md sections 1-3, batch 170/171 practice):
  * archive-only (not staged): the main manuscript report.tex, every PDF, the delivery README.md;
  * exact alias: a file whose blob is already tracked anywhere in the repository is not
    duplicated; the placement map records the existing path;
  * otherwise staged byte-identical as NN-slug-<path, '/' -> '-'>:
      audit/provenance markdown, notices and licences -> host root,
      scripts and build files -> code/, everything else -> data/;
  * if the shipped path (prefixed by C:\\ProveIt\\) exceeds 200 characters, the flattened
    path is replaced by a four-digit member index plus basename (as Source 100 did).
Usage: place172.py EXTRACT_ROOT REPO [--apply]
"""
import json, os, shutil, subprocess, sys

EXTRACT, REPO = sys.argv[1], sys.argv[2]
APPLY = "--apply" in sys.argv
HOST = "SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels"
SOURCES = [  # arrival order (archive mtimes 08:30, 08:30, 08:31 in 83fd358548's checkout)
    (101, "coord239", "BusyBeaver239_Research_2026-10-19"),
    (102, "delay239", "ZFC239_Companion_2026-10-19"),
    (103, "bound239", "ZFC_239_State_Construction_2026-10-19"),
]
CODE = {".py", ".sh", ".ps1", ".wl", ".wls", ".lean", ".cpp", ".hpp", ".h", ".c", ".mk", ".toml"}
CODE_NAMES = {"Makefile", "makefile", "lakefile.lean", "lean-toolchain"}
ROOT_MD = ("ATTRIBUTION", "PROVENANCE", "NOTICE", "LICENSE", "AUDIT", "REVIEW", "README",
           "STATUS", "DELTA", "CONTRACT", "FINDINGS", "SEARCH_PROVENANCE", "OBLIGATIONS")


def git(*args, inp=None):
    return subprocess.run(["git", "-C", REPO, *args], input=inp, capture_output=True,
                          text=True, check=True).stdout


tracked = {}
for line in git("ls-files", "-s").splitlines():
    meta, path = line.split("\t", 1)
    tracked.setdefault(meta.split()[1], path)


def blob(path):
    return git("hash-object", "--no-filters", path).strip()


def role(rel):
    base = os.path.basename(rel)
    stem, ext = os.path.splitext(base)
    if rel in ("report.tex", "README.md") or ext.lower() == ".pdf":
        return "archive-only"
    if ext in CODE or base in CODE_NAMES:
        return "code"
    if ext.lower() in (".md", ".txt") and (rel.count("/") <= 1 and (stem.upper().startswith(ROOT_MD)
                                                                   or "licen" in rel.lower())):
        return "root"
    if base.startswith(("LICENSE", "NOTICE")):
        return "root"
    return "data"


plan = {"batch": 172, "host": HOST, "pin": "13ec39ed43148b1807f51ed6e6528e1c84659562",
        "arrival": "83fd358548", "sources": []}
for num, slug, arch in SOURCES:
    top = os.path.join(EXTRACT, arch)
    (inner,) = os.listdir(top)  # single wrapper directory
    base = os.path.join(top, inner)
    members = []
    for i, (dp, _, fs) in enumerate(sorted(os.walk(base))):
        pass
    files = sorted(os.path.relpath(os.path.join(dp, f), base).replace("\\", "/")
                   for dp, _, fs in os.walk(base) for f in fs)
    for idx, rel in enumerate(files, 1):
        r = role(rel)
        h = blob(os.path.join(base, rel))
        entry = {"member": f"{inner}/{rel}", "blob": h, "role": r}
        if r != "archive-only":
            if h in tracked:
                entry.update(role="alias", alias=tracked[h])
            else:
                flat = f"{num}-{slug}-" + rel.replace("/", "-")
                sub = "" if r == "root" else r + "/"
                dest = f"{HOST}/{sub}{flat}"
                if len("C:\\ProveIt\\" + dest) > 200:
                    flat = f"{num}-{slug}-{idx:04d}-" + os.path.basename(rel)
                    dest = f"{HOST}/{sub}{flat}"
                assert len("C:\\ProveIt\\" + dest) <= 200, dest
                entry["path"] = dest
                tracked[h] = dest  # later duplicates within the batch become aliases
        members.append(entry)
    plan["sources"].append({"source": num, "slug": slug, "archive": arch + ".zip",
                            "wrapper": inner, "members": members})

paths = [m["path"] for s in plan["sources"] for m in s["members"] if "path" in m]
assert len(paths) == len(set(paths)), "path collision"
for s in plan["sources"]:
    c = {}
    for m in s["members"]:
        c[m["role"]] = c.get(m["role"], 0) + 1
    print(s["source"], s["archive"], len(s["members"]), c)
print("staged", len(paths), "max path", max(len("C:\\ProveIt\\" + p) for p in paths))

if APPLY:
    for s in plan["sources"]:
        base = os.path.join(EXTRACT, s["archive"][:-4], s["wrapper"])
        for m in s["members"]:
            if "path" in m:
                src = os.path.join(base, m["member"].split("/", 1)[1])
                dst = os.path.join(REPO, m["path"])
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copyfile(src, dst)
    out = os.path.join(REPO, HOST, "data", "intake172-placement.json")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        json.dump(plan, f, indent=1)
        f.write("\n")
    print("wrote", out)

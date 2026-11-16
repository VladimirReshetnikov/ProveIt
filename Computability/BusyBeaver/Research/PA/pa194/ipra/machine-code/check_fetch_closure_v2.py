#!/usr/bin/env python3
"""Compile PA194ModelFairness.lean and every standalone module it imports.

usage: check_bridge.py [--out DIR] [--top FILE.lean] [--reports N]

Without --top the module is PA194ModelFairness.lean of this directory and three axiom reports
are expected. With --top FILE.lean another standalone module of Research/PA is checked the
same way, its directory takes the place of "this directory" below, and --reports gives the
expected number of axiom reports.

The modules of the root Lake workspace (DiophantineConsistency, Foundation, BusyBeaver, ...)
are taken as built in .lake/build. Every other module of the import closure is a standalone
file below Computability/BusyBeaver/Research/PA, or one of the generated inputs

  PA194Rows, PA194Literal          pa194/ipra/generate.py
  PA194SourceTree                  pa194-source-tree/generate.py
  PA194AXBatch*, PA194AXPlan       pa194-ax-core/generate.py

which are written to DIR/generated. All of them are compiled into DIR, one `lean` process at
a time, in dependency order. DIR is a fresh temporary directory by default; with an existing
DIR, modules whose .olean is already there are skipped, except the modules of this directory,
which are always recompiled. A fresh run compiles about three hundred modules.

A bare module name is resolved in the directory of the importing file first, then in
DIR/generated, then as the unique file of that name below Research/PA outside
jamesyc-upstream and docs; M6.*, PA196.*, M6PA.*, Cert.* come from jamesyc-upstream/pa196.

The script prints the axiom reports of PA194ModelFairness and fails if `sorryAx` occurs in a
log. No child process opens a console window.
"""
import collections, os, re, subprocess, sys, tempfile, hashlib, json

NW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
here = os.path.dirname(os.path.abspath(__file__))
repo = os.getcwd()
PA = os.path.join(repo, "Computability", "BusyBeaver", "Research", "PA")
UP = os.path.join(PA, "other-machines", "jamesyc-upstream", "pa196")
WORKSPACE = ("DiophantineConsistency", "Foundation", "BusyBeaver", "FirstOrder", "Mathlib", "Std",
             "Lean", "Init", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph",
             "LeanSearchClient", "ProofWidgets", "Cli")
UPROOTS = ("M6", "PA196", "M6PA", "Cert")
top = os.path.join(here, "PA194ModelFairness.lean")
reports = 3
if "--top" in sys.argv:
    top = os.path.abspath(sys.argv[sys.argv.index("--top") + 1])
if "--reports" in sys.argv:
    reports = int(sys.argv[sys.argv.index("--reports") + 1])
topmod = os.path.basename(top)[:-5]
mydir = os.path.dirname(top)
if "--out" in sys.argv:
    out = os.path.abspath(sys.argv[sys.argv.index("--out") + 1])
    os.makedirs(out, exist_ok=True)
else:
    out = tempfile.mkdtemp(prefix="pa194-model-fairness-")
gen = os.path.join(out, "generated")
os.makedirs(gen, exist_ok=True)


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=repo, stdin=subprocess.DEVNULL, creationflags=NW, **kw)


if not os.path.exists(os.path.join(gen, "PA194AXPlan.lean")):
    py = [sys.executable, "-X", "utf8", "-B"]
    run(py + [os.path.join(PA, "pa194", "ipra", "generate.py"), repo, gen], check=True,
        stdout=subprocess.DEVNULL)
    run(py + [os.path.join(PA, "pa194-work", "pa194-source-tree", "generate.py"),
              os.path.join(gen, "PA194SourceTree.lean")], check=True, stdout=subprocess.DEVNULL)
    run(py + [os.path.join(PA, "pa194-work", "pa194-ax-core", "generate.py"), gen], check=True,
        stdout=subprocess.DEVNULL)

flat = collections.defaultdict(list)
for root, dirs, files in os.walk(PA):
    rel = os.path.relpath(root, PA).replace("\\", "/")
    if rel.startswith(("docs", "other-machines/jamesyc-upstream")):
        dirs[:] = []
        continue
    for f in files:
        if f.endswith(".lean"):
            flat[f[:-5]].append(os.path.join(root, f))


def resolve(mod, frm):
    top = mod.split(".")[0]
    if "." in mod:
        if top in UPROOTS:
            p = os.path.join(UP, *mod.split(".")) + ".lean"
            return p if os.path.exists(p) else None
        return None
    if top in WORKSPACE:
        return None
    for d in ([os.path.dirname(frm)] if frm else []) + [gen]:
        p = os.path.join(d, mod + ".lean")
        if os.path.exists(p):
            return p
    c = flat.get(mod, [])
    if len(c) == 1 or (c and len({open(p, "rb").read() for p in c}) == 1):
        return sorted(c)[0]
    if c:
        sys.exit("ambiguous module %s imported by %s: %s" % (mod, frm, c))
    sys.exit("module %s imported by %s has no source" % (mod, frm))


order, seen = [], set()


def visit(mod, frm):
    if mod in seen:
        return
    seen.add(mod)
    p = resolve(mod, frm)
    if p is None:
        return
    for line in open(p, encoding="utf-8", errors="replace"):
        m = re.match(r"\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", line)
        if m:
            visit(m.group(1), p)
        elif re.match(r"\s*(theorem|def|lemma|namespace|open|set_option|noncomputable|inductive|"
                      r"structure|instance|abbrev|universe|variable|section|attribute)\b", line):
            break
    order.append((mod, p))


sys.setrecursionlimit(10000)
visit(topmod, top)
source_hashes = {src:hashlib.sha256(open(src, "rb").read()).hexdigest() for _,src in order}
with open(os.path.join(out, "source-closure.json"), "w") as f:
    json.dump([{"module":m,"source":p,"sha256":source_hashes[p]} for m,p in order], f, indent=2)
tree = os.path.join(gen, "PA194SourceTree.lean")
if source_hashes.get(tree) != "69f6dee4807f25ed36923a86b87c20bc23432bdaf43bf8a41148f76f05540ca1":
    sys.exit("generated source tree hash mismatch")
lean_path = run(["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                check=True).stdout.strip()
env = dict(os.environ)
foundations = [os.environ["PA194_FETCH_PROJECT_FOUNDATION"], os.environ["PA194_FETCH_PACKAGE_FOUNDATION"]]
for root in foundations + lean_path.split(os.pathsep):
    if not root or not os.path.isdir(root):
        continue
    names = os.listdir(root)
    if any((n.startswith(("PA194", "PA195", "PA196", "Packed", "BinaryTape", "TableDispatch", "Configuration")) and n.endswith(".olean")) or n in ("M6", "PA196", "M6PA", "Cert") for n in names):
        sys.exit("machine-specific fallback in foundation root: " + root)
graph = os.environ["PA194_FETCH_GRAPH_NAMESPACE"]
if os.path.basename(graph) != "DiophantineConsistency":
    sys.exit("graph namespace must be DiophantineConsistency")
view = os.path.join(out,"foundation-view")
os.makedirs(view,exist_ok=False)
os.symlink(graph,os.path.join(view,"DiophantineConsistency"))
env["LEAN_PATH"] = os.pathsep.join([out,view] + foundations + [lean_path])
env["LEAN_NUM_THREADS"] = "1"
version = run(["lean", "--version"], capture_output=True, text=True).stdout
if "version 4.32.0" not in version:
    sys.exit("expected Lean 4.32.0, found: " + version.strip())
compiled = 0
for k, (mod, src) in enumerate(order, 1):
    target = os.path.join(out, *mod.split("."))
    os.makedirs(os.path.dirname(target), exist_ok=True)
    log = target + ".log"
    mine = os.path.dirname(os.path.abspath(src)) == mydir
    if os.path.exists(target + ".olean") and not mine:
        continue
    inside = os.path.abspath(src).lower().startswith(os.path.abspath(repo).lower() + os.sep)
    rootopt = [] if inside else ["-R", os.path.dirname(os.path.abspath(src))]
    with open(log, "w", encoding="utf-8") as f:
        r = run(["lean"] + rootopt + ["-j1", "-M", "7000", "-o", target + ".olean", src], env=env,
                stdout=f, stderr=subprocess.STDOUT)
    text = open(log, encoding="utf-8", errors="replace").read()
    ok = r.returncode == 0 and "sorryAx" not in text and "declaration uses 'sorry'" not in text
    compiled += 1
    print("%3d/%d %s %s" % (k, len(order), "ok  " if ok else "FAIL", mod), flush=True)
    if not ok:
        if os.path.exists(target + ".olean"):
            os.remove(target + ".olean")
        print(text[:3000])
        sys.exit(1)
for mod, _ in order:
    log = os.path.join(out, *mod.split(".")) + ".log"
    if os.path.exists(log) and "sorryAx" in open(log, encoding="utf-8", errors="replace").read():
        sys.exit("sorryAx in the log of " + mod)
report = open(os.path.join(out, topmod + ".log"), encoding="utf-8", errors="replace").read()
lines = [l for l in report.splitlines() if "depends on axioms" in l]
print("\n".join(lines))
if len(lines) != reports:
    sys.exit("expected %d axiom reports, found %d" % (reports, len(lines)))
for src,expected in source_hashes.items():
    if hashlib.sha256(open(src,"rb").read()).hexdigest() != expected:
        sys.exit("source changed during build: " + src)
print("Source closure unchanged during build.")
print("%s: checked (%d standalone modules, %d compiled now, objects in %s)" % (
    topmod, len(order), compiled, out))

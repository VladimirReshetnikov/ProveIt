#!/usr/bin/env python3
"""Compile ConPAUnconditional.lean and everything it imports outside the root Lake libraries.

usage: check_unconditional.py [--out DIR]

The modules of the root Lake workspace (DiophantineConsistency, Foundation, BusyBeaver, ...)
are taken as built in .lake/build, or from IPRA_LEAN_OVERLAY and IPRA_FOUNDATION_OVERLAY when
set. The standalone modules are compiled one `lean` process at a
time, in dependency order, into DIR (a fresh temporary directory by default; an existing DIR is
reused and modules already compiled there are skipped):

  M6.Zip, PA196.Literal                 from jamesyc-upstream/pa196
  PA196*.lean                           from pa196-vs-u208/ipra (the PA witness certificate)
  ConPAISigma1Transfer, ConPAISigma1Models   from isigma1-transfer
  ConPAMachine, ConPAMachineEndpoint, ConPAUnconditional   from this directory

It prints the axiom reports of ConPAUnconditional and fails if `sorryAx` occurs in any log.
A fresh run compiles about a hundred modules.
"""
import os, re, subprocess, sys, tempfile

here = os.path.dirname(os.path.abspath(__file__))
repo = subprocess.run(["git", "-C", here, "rev-parse", "--show-toplevel"], capture_output=True,
                      text=True, check=True).stdout.strip()
PA = os.path.join(repo, "Computability", "BusyBeaver", "Research", "PA")
FLAT = [here, os.path.join(PA, "isigma1-transfer"), os.path.join(PA, "pa196-vs-u208", "ipra")]
UP = os.path.join(PA, "jamesyc-upstream", "pa196")
out = None
if "--out" in sys.argv:
    out = os.path.abspath(sys.argv[sys.argv.index("--out") + 1])
    os.makedirs(out, exist_ok=True)
else:
    out = tempfile.mkdtemp(prefix="conpa-unconditional-")


def source(mod):
    if mod.split(".")[0] in ("M6", "PA196"):
        p = os.path.join(UP, *mod.split(".")) + ".lean"
        return p if os.path.exists(p) else None
    if "." not in mod:
        for d in FLAT:
            p = os.path.join(d, mod + ".lean")
            if os.path.exists(p):
                return p
    return None


order, seen = [], set()


def visit(mod):
    if mod in seen:
        return
    seen.add(mod)
    p = source(mod)
    if p is None:
        return
    for line in open(p, encoding="utf-8", errors="replace"):
        m = re.match(r"\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", line)
        if m:
            visit(m.group(1))
        elif re.match(r"\s*(theorem|def|lemma|namespace|open|set_option|noncomputable|inductive|structure|instance|abbrev)\b", line):
            break
    order.append((mod, p))


visit("ConPAUnconditional")
lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, capture_output=True,
                           text=True, check=True).stdout.strip()
env = dict(os.environ)
overlays = [os.path.realpath(os.environ[k]) for k in ("IPRA_LEAN_OVERLAY", "IPRA_FOUNDATION_OVERLAY")
            if os.environ.get(k)]
env["LEAN_PATH"] = os.pathsep.join([out, *overlays, lean_path])
version = subprocess.run(["lean", "--version"], cwd=repo, capture_output=True, text=True).stdout
if "version 4.32.0" not in version:
    sys.exit("expected Lean 4.32.0, found: " + version.strip())
bad = False
for k, (mod, src) in enumerate(order, 1):
    target = os.path.join(out, *mod.split("."))
    os.makedirs(os.path.dirname(target), exist_ok=True)
    log = target + ".log"
    if os.path.exists(target + ".olean") and os.path.exists(log) and mod != "ConPAUnconditional":
        continue
    with open(log, "w", encoding="utf-8") as f:
        r = subprocess.run(["lean", "-M", "7000", "-j", "1", "-o", target + ".olean", src],
                           cwd=repo, env=env, stdout=f, stderr=subprocess.STDOUT)
    text = open(log, encoding="utf-8", errors="replace").read()
    ok = r.returncode == 0 and "sorryAx" not in text and "declaration uses 'sorry'" not in text
    print("%3d/%d %s %s" % (k, len(order), "ok  " if ok else "FAIL", mod), flush=True)
    if not ok:
        if os.path.exists(target + ".olean"):
            os.remove(target + ".olean")
        print(text[:3000])
        bad = True
        break
if bad:
    sys.exit(1)
for mod, _ in order:
    text = open(os.path.join(out, *mod.split(".")) + ".log", encoding="utf-8", errors="replace").read()
    if "sorryAx" in text:
        sys.exit("sorryAx in the log of " + mod)
report = open(os.path.join(out, "ConPAUnconditional.log"), encoding="utf-8", errors="replace").read()
lines = [l for l in report.splitlines() if "depends on axioms" in l]
print("\n".join(lines))
if len(lines) != 3:
    sys.exit("expected three axiom reports")
print("ConPAUnconditional: checked (%d standalone modules, objects in %s)" % (len(order), out))

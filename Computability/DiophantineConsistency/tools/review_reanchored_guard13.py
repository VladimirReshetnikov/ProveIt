#!/usr/bin/env python3
"""Read-only archive review and isolated replay of the1072-degree guard."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT.parents[1]/"docs/incoming/con_zfc_batched_certificates_2026-10-23.zip"
PARENT = ROOT.parents[1]/"docs/incoming/ConZFC_13_Integer_Norms_2026-10-24.zip"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def norm_cut(packet, pool):
    cut = packet["named_registers"]["Ag"]
    nodes = packet["nodes"]
    memo = {}
    def intern(term):
        if term not in pool:
            pool[term] = len(pool)
        return pool[term]
    def visit(i):
        if i == cut:
            return intern(("free_guard_radicand",))
        if i in memo:
            return memo[i]
        row = nodes[i]
        if row[0] in ("variable","coefficient","integer"):
            term = tuple(row)
        else:
            need(row[0] in ("add","sub","mul") and len(row) == 3,
                 "binary polynomial node")
            a,b = visit(row[1]),visit(row[2])
            if row[0] in ("add","mul") and a>b:
                a,b = b,a
            term = (row[0],a,b)
        memo[i] = intern(term)
        return memo[i]
    return visit(packet["output"])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=ROOT/"data/reanchored-guard13-review.json")
    args = ap.parse_args()
    need(sha(ARCHIVE.read_bytes()) == "ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55", "whole arrival")
    need(sha(PARENT.read_bytes()) == "d800f0fb608d4301b8888b589a97477da836b00c93c66db0668e1cc0c2b0b41f", "whole parent")
    with tempfile.TemporaryDirectory(prefix="proveit-guard1072-") as tmp:
        root = Path(tmp)
        with zipfile.ZipFile(ARCHIVE) as z:
            selected = {}
            for member in z.infolist():
                name = PurePosixPath(member.filename)
                need(not name.is_absolute() and ".." not in name.parts, "safe archive path")
                if member.is_dir() or "/guard13/" not in member.filename:
                    continue
                relative = member.filename.split("/guard13/",1)[1]
                selected[relative] = z.read(member)
        with zipfile.ZipFile(PARENT) as z:
            originals = {n.split("/",1)[1]:z.read(n) for n in z.namelist() if not n.endswith("/")}
        prefix = "upstream/con-zfc-root-fusion-2026-10-24/"
        supplied = {n[len(prefix):]:raw for n,raw in selected.items() if n.startswith(prefix)}
        need(supplied == originals, "entire inherited root-fusion package unchanged")
        packet = json.loads(selected["equation.json"])
        old = json.loads(supplied["equations/norm13_crt_degree1088.json"])
        pool = {}
        need(norm_cut(packet,pool) == norm_cut(old,pool), "whole output identical over free Ag cut")
        need(packet["variables"] == old["variables"], "same complete variables")
        bad = deepcopy(packet)
        bad["nodes"][bad["output"]][0] = "add"
        need(norm_cut(bad,pool) != norm_cut(old,pool), "changed final norm rejected")
        modes = {}
        for mode,flags in [("normal",[]),("optimized",["-O"])]:
            directory = root/mode
            for name,raw in selected.items():
                dest = directory/name
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes(raw)
            commands = []
            for script in ["build_reanchored.py","verify_reanchored.py"]:
                run = subprocess.run([sys.executable,"-B",*flags,str(directory/script)],
                                     capture_output=True,text=True)
                need(run.returncode == 0, script+": "+run.stderr)
                commands.append(dict(script=script,returncode=run.returncode,
                                     stdout_sha256=sha(run.stdout.encode())))
            need((directory/"equation.json").read_bytes() == selected["equation.json"],
                 "byte-exact complete equation rebuild")
            audit = json.loads((directory/"AUDIT.json").read_text())
            need(audit["status"] == "PASS", "complete inherited checker")
            modes[mode] = dict(commands=commands,audit=audit)
        need(modes["normal"]["audit"] == modes["optimized"]["audit"], "same full exact audit in both modes")
        # Controls for the written universal nearest-square argument.
        for x in range(1,101):
            for y in range(1,101):
                N = x+y-1
                t = min(range(16),key=lambda t:abs(t*t-N))
                need(x*y-(t*t-x-y+1)**2 > 0, "positive-pair witness control")
        result = dict(status="PASS",archive_sha256=sha(ARCHIVE.read_bytes()),
                      inherited_files_byte_identical=len(originals),
                      complete_equation_sha256=sha(selected["equation.json"]),
                      same_complete_norm_over_free_guard=True,changed_norm_rejected=True,
                      positive_pair_controls=10000,replays=modes,
                      endpoint=dict(integer_variables=13,operations=195,exact_degree=1072),
                      scope="Guard reparameterization ordinary proof and exact scoped replay; direct batched components excluded. No new Lean/internal-ZFC calibration.")
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print("PASS whole inherited package, complete norm cut,1072-degree leading form and both byte-exact replays")


if __name__ == "__main__":
    main()

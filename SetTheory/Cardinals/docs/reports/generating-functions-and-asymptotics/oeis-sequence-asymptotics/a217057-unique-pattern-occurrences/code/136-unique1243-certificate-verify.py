#!/usr/bin/env python3
"""Closed-inventory, exact, offline Report136 certificate verifier.

Required checks use explicit exceptions, never Python assert statements.
Use Python 3.9 or newer. No third-party dependency or network operation.
"""
import sys
if not sys.flags.isolated:
    raise SystemExit("REJECTED: isolated Python is required; run python3 -I -B verify.py COMMAND")
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tempfile
import subprocess
import types

ROOT=Path(__file__).absolute().parent
PAYLOAD=frozenset(("README.md","verify.py","tableaux.py","objects.py","bundle.py","fixtures.json","expected.json"))
INVENTORY=PAYLOAD|{"manifest.json"}
VALUES=(0,0,0,0,1,11,88,638,4478,31199,218033,1535207,10910759,
        78310579,567588264,4152765025,30656248812,228215224472,
        1712296117750,12941799657414,98486737654025,754273093950128,
        5811161481943201,45020589539040033,350604675228411590,2743720335733822423)
LOWER="55999844944982350869187286355724963/90113598179756697647360591499090564"


class Rejected(Exception):
    pass


def need(condition,message):
    if not condition:
        raise Rejected(message)


def canonical(value):
    return (json.dumps(value,sort_keys=True,indent=2,ensure_ascii=True)+"\n").encode("ascii")


def pairs_hook(pairs):
    result={}
    for key,value in pairs:
        need(key not in result,"duplicate JSON key: "+key)
        result[key]=value
    return result


def parse(data):
    def invalid(value):
        raise Rejected("nonstandard JSON number: "+value)
    return json.loads(data.decode("utf-8"),object_pairs_hook=pairs_hook,parse_constant=invalid)


def strict_equal(actual,expected,path="root"):
    need(type(actual) is type(expected),"exact type mismatch at "+path)
    if type(expected) is dict:
        need(set(actual)==set(expected),"keys mismatch at "+path)
        for key in expected:
            strict_equal(actual[key],expected[key],path+"."+key)
    elif type(expected) is list:
        need(len(actual)==len(expected),"length mismatch at "+path)
        for i,(a,e) in enumerate(zip(actual,expected)):
            strict_equal(a,e,path+"["+str(i)+"]")
    else:
        need(actual==expected,"value mismatch at "+path)


def exact_tree(value,path="output"):
    """Output grammar has no bool, float, null, or nonstring object keys."""
    if type(value) is dict:
        for key,item in value.items():
            need(type(key) is str,"nonstring JSON key")
            exact_tree(item,path+"."+key)
    elif type(value) is list:
        for i,item in enumerate(value):
            exact_tree(item,path+"["+str(i)+"]")
    else:
        need(type(value) in (int,str),"nonexact output scalar at "+path)


def fixture_oracle():
    return {"schema":"report136-fixtures-v1",
            "published":{"sequence":"A224179","url":"https://oeis.org/A224179",
                         "accessed":"2026-10-02","source_offset":1,
                         "source_values":list(VALUES[1:]),
                         "n0_convention":0,
                         "definition":"Permutations of length n with exactly one classical 1243 occurrence"},
            "scope":{"object_max_n":8,"published_max_n":25,"algebra_max_n":10,
                     "tableau_max_size":37,"incidence_max_size":12,"partial_cutoff":35},
            "positive_partial":{"lower_fraction":LOWER,"first_term":"4/81","summands":666}}


def absolute(value):
    p=Path(value)
    need(".." not in p.parts,"parent traversal refused")
    return p if p.is_absolute() else Path.cwd()/p


def ancestors(path,missing_leaf=False):
    need(path.is_absolute(),"path must be absolute")
    current=Path(path.anchor)
    for i,part in enumerate(path.parts[1:]):
        current/=part
        leaf=i==len(path.parts)-2
        try:
            mode=current.lstat().st_mode
        except FileNotFoundError:
            need(leaf and missing_leaf,"missing ancestor: "+str(current))
            return
        need(not stat.S_ISLNK(mode),"symlink component refused: "+str(current))
        if not leaf:
            need(stat.S_ISDIR(mode),"nondirectory ancestor: "+str(current))


def regular_bytes(path):
    flags=os.O_RDONLY|getattr(os,"O_NOFOLLOW",0)|getattr(os,"O_NONBLOCK",0)
    fd=os.open(path,flags)
    with os.fdopen(fd,"rb") as f:
        need(stat.S_ISREG(os.fstat(f.fileno()).st_mode),"nonregular file")
        return f.read()


def verify(root=ROOT):
    root=absolute(root)
    ancestors(root)
    need(root.is_dir(),"certificate root is not a directory")
    names=set()
    for entry in os.scandir(root):
        need(stat.S_ISREG(entry.stat(follow_symlinks=False).st_mode),
             "nonregular inventory entry: "+entry.name)
        names.add(entry.name)
    need(names==INVENTORY,"closed inventory mismatch; missing="+str(sorted(INVENTORY-names))+"; extra="+str(sorted(names-INVENTORY)))
    data={name:regular_bytes(root/name) for name in sorted(INVENTORY)}
    manifest=parse(data["manifest.json"])
    need(type(manifest) is dict and set(manifest)=={"schema","files"},"manifest keys/type")
    need(type(manifest["schema"]) is str and manifest["schema"]=="report136-sha256-v1","manifest schema")
    need(type(manifest["files"]) is dict and set(manifest["files"])==PAYLOAD,"manifest exact payload")
    for name in sorted(PAYLOAD):
        record=manifest["files"][name]
        need(type(record) is dict and set(record)=={"bytes","sha256"},"manifest record keys/type")
        need(type(record["bytes"]) is int and record["bytes"]==len(data[name]),"manifest byte size: "+name)
        need(type(record["sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}",record["sha256"]) is not None,"digest type/format")
        need(record["sha256"]==hashlib.sha256(data[name]).hexdigest(),"digest mismatch: "+name)
    fixture=parse(data["fixtures.json"])
    strict_equal(fixture,fixture_oracle(),"fixtures")
    expected=parse(data["expected.json"])
    exact_tree(expected)
    need(type(expected) is dict and set(expected)=={"schema","published_coefficients","objects","algebra","positive_partial","finite_diagnostics"},"expected output keys")
    need(expected["schema"]=="report136-replay-v1","expected schema")
    need(data["fixtures.json"]==canonical(fixture),"fixtures must be canonical JSON")
    need(data["expected.json"]==canonical(expected),"expected output must be canonical JSON")
    return data


def module(data,name):
    result=types.ModuleType(name[:-3])
    exec(compile(data[name],name,"exec"),result.__dict__)
    return result


def compute(data):
    t=module(data,"tableaux.py")
    o=module(data,"objects.py")
    published=[[n,t.spine(n)] for n in range(len(VALUES))]
    strict_equal([v for _,v in published],list(VALUES),"published A224179")
    partial=t.triangular_partial(35)
    need(partial["lower_fraction"]==LOWER,"positive partial fixture")
    need(partial["rows"][0]["lower_fraction"]=="4/81","amplitude first term")
    algebra=t.algebra_checks(10)
    algebra["ct_exponent_ledger"]=t.ct_exponent_checks()
    result={"schema":"report136-replay-v1","published_coefficients":published,
            "objects":o.run(t.F,t.J,8),"algebra":algebra,
            "positive_partial":partial,"finite_diagnostics":t.finite_diagnostics(37,12)}
    result["finite_diagnostics"]["profile_rational_constants"]=t.profile_constant_checks()
    exact_tree(result)
    return result


def output_preflight(value,root):
    path=absolute(value)
    ancestors(path,True)
    need(not path.exists() and not path.is_symlink(),"output already exists")
    need(path!=root and root not in path.parents,"output must be outside certificate directory")
    need(path.parent.is_dir(),"output parent does not exist")
    return path


def write_output(path,data):
    ancestors(path,True)
    flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,"O_NOFOLLOW",0)
    fd=os.open(path,flags,0o600)
    with os.fdopen(fd,"wb") as f:
        f.write(data)


def guards(data):
    """Negative tests use disposable copies, never mutate the certificate."""
    cases=[]
    def rejected(label,operation):
        try:
            operation()
        except (Rejected,ValueError,OSError,UnicodeError):
            cases.append(label)
        else:
            raise Rejected("guard failed to reject "+label)
    def reseal(root):
        manifest={"schema":"report136-sha256-v1","files":{
            name:{"bytes":len((root/name).read_bytes()),"sha256":hashlib.sha256((root/name).read_bytes()).hexdigest()}
            for name in sorted(PAYLOAD)}}
        (root/"manifest.json").write_bytes(canonical(manifest))
    with tempfile.TemporaryDirectory(prefix="report136-guards-") as folder:
        parent=Path(folder)
        counter=0
        def fresh():
            nonlocal counter
            counter+=1
            root=parent/("case"+str(counter))
            root.mkdir()
            for name,value in data.items():
                (root/name).write_bytes(value)
            return root
        root=fresh(); (root/"extra.txt").write_text("x"); rejected("extra inventory",lambda:verify(root))
        root=fresh(); (root/"fixtures.json").unlink(); rejected("missing inventory",lambda:verify(root))
        root=fresh(); (root/"extra").mkdir(); rejected("directory inventory",lambda:verify(root))
        root=fresh(); (root/"fixtures.json").unlink(); (root/"fixtures.json").symlink_to(ROOT/"fixtures.json"); rejected("symlink inventory",lambda:verify(root))
        root=fresh(); (root/"tableaux.py").write_bytes(data["tableaux.py"]+b"\n"); rejected("changed payload digest",lambda:verify(root))
        root=fresh(); (root/"fixtures.json").write_bytes(b'{"schema":"one","schema":"two"}'); reseal(root); rejected("duplicate JSON key",lambda:verify(root))
        for value,label in ((True,"boolean integer fixture"),(8.0,"float integer fixture")):
            root=fresh(); fixture=fixture_oracle(); fixture["scope"]["object_max_n"]=value
            (root/"fixtures.json").write_bytes(canonical(fixture)); reseal(root)
            rejected(label,lambda:verify(root))
        root=fresh(); fixture=fixture_oracle(); fixture["unknown"]=0; (root/"fixtures.json").write_bytes(canonical(fixture)); reseal(root); rejected("extra fixture key",lambda:verify(root))
        root=fresh(); manifest=parse(data["manifest.json"]); manifest["files"]["README.md"]["bytes"]=True; (root/"manifest.json").write_bytes(canonical(manifest)); rejected("boolean manifest size",lambda:verify(root))
        root=fresh(); expected=parse(data["expected.json"]); expected["published_coefficients"][0][1]=False
        (root/"expected.json").write_bytes(canonical(expected)); reseal(root); rejected("boolean deterministic output",lambda:verify(root))
        rejected("nonstandard JSON infinity",lambda:parse(b'{"a":Infinity}'))
        rejected("typed equality bool/int",lambda:strict_equal(True,1))
        rejected("typed equality float/int",lambda:strict_equal(1.0,1))
        rejected("existing output",lambda:output_preflight(ROOT/"README.md",ROOT))
        rejected("output inside certificate",lambda:output_preflight(ROOT/"new.json",ROOT))
        rejected("output parent traversal",lambda:output_preflight(parent/".."/"x",ROOT))
        (parent/"link").symlink_to(parent,target_is_directory=True)
        rejected("symlink output ancestor",lambda:output_preflight(parent/"link"/"x",ROOT))
        rejected("missing output parent",lambda:output_preflight(parent/"absent"/"x",ROOT))
        destination=output_preflight(parent/"result.json",ROOT)
        write_output(destination,b"one")
        rejected("exclusive output overwrite",lambda:write_output(destination,b"two"))
        need(destination.read_bytes()==b"one","existing output was modified")
        root=fresh(); alias=parent/"root-link"; alias.symlink_to(root,target_is_directory=True)
        rejected("symlink certificate root",lambda:verify(alias))
        # Negative bootstrap tests deliberately omit -I: they must stop after
        # built-in sys, BEFORE an unsealed shadow argparse can execute.
        shadow=fresh()
        marker=parent/"shadow-argparse-executed"
        (shadow/"argparse.py").write_text(
            "with open("+repr(str(marker))+", 'w') as stream: stream.write('executed')\n",
            encoding="utf-8")
        for optimized in (False,True):
            mode="optimized" if optimized else "normal"
            options=["-B"]+(["-O"] if optimized else [])
            command=[sys.executable,*options,str(shadow/"verify.py"),"check"]
            run=subprocess.run(command,cwd=shadow,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
            need(run.returncode!=0 and b"isolated Python is required" in run.stderr,
                 "nonisolated bootstrap did not reject before imports")
            need(not marker.exists(),"unsealed argparse executed before bootstrap rejection")
            cases.append("nonisolated shadow-argparse bootstrap rejected "+mode)
            command=[sys.executable,"-I",*options,str(shadow/"verify.py"),"check"]
            run=subprocess.run(command,cwd=shadow,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
            need(run.returncode!=0 and b"closed inventory mismatch" in run.stderr,
                 "isolated shadow module was not refused by inventory")
            need(not marker.exists(),"unsealed argparse executed despite isolated launch")
            cases.append("isolated shadow-argparse inventory rejected "+mode)
    return cases


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=("check","replay","guard-test","bundle-stage","bundle-check","bundle-build","bundle-pack","bundle-selftest"))
    parser.add_argument("--output",help="replay JSON to a new external file; never overwrites")
    parser.add_argument("--report-root",help="source report directory for bundle-stage")
    parser.add_argument("--bundle",help="closed integrated bundle directory")
    args=parser.parse_args()
    if args.command.startswith("bundle-"):
        data=verify()
        module(data,"bundle.py").execute(sys.modules[__name__],args,data)
        return 0
    need(args.report_root is None and args.bundle is None,"bundle flags require a bundle command")
    need(args.output is None or args.command=="replay","--output is only valid with replay")
    data=verify()
    destination=output_preflight(args.output,ROOT) if args.output else None
    if args.command=="check":
        print("PASS: closed inventory, SHA-256, exact typed fixtures, deterministic output syntax")
    elif args.command=="replay":
        result=compute(data)
        strict_equal(result,parse(data["expected.json"]),"replay")
        encoded=canonical(result)
        need(encoded==data["expected.json"],"deterministic replay bytes")
        if destination is not None:
            write_output(destination,encoded)
        print("PASS: exact replay matches expected.json; SHA-256 "+hashlib.sha256(encoded).hexdigest())
    else:
        cases=guards(data)
        print("PASS: "+str(len(cases))+" fail-closed guard tests")
        for label in cases:
            print("  "+label)
    return 0


if __name__=="__main__":
    try:
        sys.exit(main())
    except (Rejected,ValueError,OSError,UnicodeError,KeyError,IndexError,TypeError,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
        print("REJECTED: "+str(error),file=sys.stderr)
        sys.exit(1)

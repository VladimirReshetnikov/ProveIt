#!/usr/bin/env python3
"""Fresh-compile the bundled direct rho8 proof, then check it with coqchk.

Ordinary installation:
  python3 build_rocq.py --coqc coqc --coqchk coqchk

An unpacked Debian installation can instead use --coq-root PACKAGE_ROOT.
All three source files are bundled and are copied unchanged into an isolated
build directory. No pre-existing compiled object is reused.
"""
import argparse,datetime,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument("--coqc",default=os.environ.get("COQC","coqc"))
ap.add_argument("--coqchk",default=os.environ.get("COQCHK","coqchk"))
ap.add_argument("--coqlib",type=Path)
ap.add_argument("--coq-root",type=Path)
args=ap.parse_args()
r=Path(__file__).resolve().parent
out=r/"verification";out.mkdir(exist_ok=True)
src=r/"rocq"
build=out/"rocq-build"
if build.exists():shutil.rmtree(build)
build.mkdir()
env=os.environ.copy()
if args.coq_root:
    toolroot=args.coq_root.resolve()
    args.coqc=str(toolroot/"usr/bin/coqc")
    args.coqchk=str(toolroot/"usr/bin/coqchk")
    args.coqlib=toolroot/"usr/lib/ocaml/coq"
    env["OCAMLFIND_CONF"]=str(toolroot/"etc/ocamlfind.conf")
    env["OCAMLPATH"]=str(toolroot/"usr/lib/ocaml")
if args.coqlib:env["COQLIB"]=str(args.coqlib.resolve())
coqlib=["-coqlib",str(args.coqlib.resolve())] if args.coqlib else []
maps=[*coqlib,"-Q",str(build/"direct"),"K215Direct",
      "-Q",str(build/"settheory"),"K230S","-Q",str(build/"logic"),"K230L"]
receipt={"timestamp_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":"RUNNING",
 "scope":"Fresh three-module closure of direct rho8 proof, followed by coqchk; not an end-to-end machine theorem build.",
 "modules":[]}
receipt["toolchain"]=subprocess.run([args.coqc,*coqlib,"--version"],env=env,text=True,capture_output=True,check=True).stdout.strip()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for source,destination in [("settheory/KCode230.v","settheory/KCode230.v"),
                           ("logic/Codes230.v","logic/Codes230.v"),
                           ("DirectDomRho8.v","direct/DirectDomRho8.v")]:
    dest=build/destination;dest.parent.mkdir(exist_ok=True)
    shutil.copyfile(src/source,dest)
    receipt["modules"].append({"file":source,"build_file":destination,"sha256":sha(dest),
      "source_kind":"new generated direct proof" if source=="DirectDomRho8.v" else "Pinned K230 dependency, copied unchanged"})
for row in receipt["modules"]:
    file=build/row["build_file"]
    start=time.monotonic()
    cmd=[args.coqc,*maps,str(file)]
    p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=300)
    row.update(command=cmd,returncode=p.returncode,seconds=round(time.monotonic()-start,3))
    log=out/("coq-"+file.stem+".log")
    log.write_text(p.stdout+p.stderr)
    row.update(log=str(log.relative_to(r)),log_sha256=sha(log))
    print(file.name,p.returncode,flush=True)
    if p.returncode:
        receipt["status"]="FAILED"
        (out/"coq_kernel_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
        print(p.stdout,p.stderr)
        raise SystemExit(p.returncode)
    row["object_sha256"]=sha(file.with_suffix(".vo"))
cmd=[args.coqchk,*maps,"K215Direct.DirectDomRho8"]
start=time.monotonic()
p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=300)
log=out/"coqchk-direct.log";log.write_text(p.stdout+p.stderr)
receipt["coqchk"]={"command":cmd,"returncode":p.returncode,"seconds":round(time.monotonic()-start,3),
 "log":str(log.relative_to(r)),"log_sha256":sha(log)}
receipt["status"]="PASS_FRESH_COQC_AND_COQCHK" if p.returncode==0 else "FAILED_COQCHK"
(out/"coq_kernel_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(receipt["status"],flush=True)
if p.returncode:print(p.stdout[-4000:],p.stderr[-4000:])
raise SystemExit(p.returncode)

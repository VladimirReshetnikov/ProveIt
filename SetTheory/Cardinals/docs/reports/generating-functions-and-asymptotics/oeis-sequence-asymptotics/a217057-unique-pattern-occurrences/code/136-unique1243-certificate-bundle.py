"""Optional integrated Report136 bundle operations; standard library only.

The mathematical certificate remains usable without a TeX installation.
Only bundle-build invokes the local TeX distribution, with shell escape off.
"""
import hashlib
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import zipfile

REPORT_FILES=frozenset(("Report136.tex","Report136.pdf","README.md"))
BUNDLE_SCHEMA="report136-integrated-sha256-v1"
EPOCH=1790899200


def file_names(v):
    return REPORT_FILES|{"certificate/"+name for name in v.INVENTORY}


def record(v,data):
    return {"schema":BUNDLE_SCHEMA,"files":{
        name:{"bytes":len(value),"sha256":hashlib.sha256(value).hexdigest()}
        for name,value in sorted(data.items())}}


def write_file(v,path,data):
    v.write_output(path,data)


def new_dir(v,path):
    v.ancestors(path,True)
    os.mkdir(path,mode=0o700)


def check(v,root):
    root=v.absolute(root)
    v.ancestors(root)
    v.need(root.is_dir(),"integrated root is not a directory")
    entries={entry.name:entry.stat(follow_symlinks=False).st_mode for entry in os.scandir(root)}
    v.need(set(entries)==REPORT_FILES|{"certificate","bundle-manifest.json"},"integrated root inventory")
    for name,mode in entries.items():
        v.need(stat.S_ISDIR(mode) if name=="certificate" else stat.S_ISREG(mode),"integrated nonregular entry: "+name)
    certificate=v.verify(root/"certificate")
    data={name:v.regular_bytes(root/name) for name in REPORT_FILES}
    data.update({"certificate/"+name:value for name,value in certificate.items()})
    v.need(data["Report136.pdf"].startswith(b"%PDF-"),"Report136.pdf is not a PDF")
    v.need(b"\\documentclass" in data["Report136.tex"],"Report136.tex lacks document class")
    raw=v.regular_bytes(root/"bundle-manifest.json")
    manifest=v.parse(raw)
    v.strict_equal(manifest,record(v,data),"integrated manifest")
    v.need(raw==v.canonical(manifest),"integrated manifest must be canonical")
    data["bundle-manifest.json"]=raw
    return data


def stage(v,certificate,source,destination):
    source=v.absolute(source)
    v.ancestors(source)
    reports={}
    for name in sorted(REPORT_FILES):
        v.ancestors(source/name)
        reports[name]=v.regular_bytes(source/name)
    v.need(reports["Report136.pdf"].startswith(b"%PDF-"),"stage PDF header")
    v.need(b"\\documentclass" in reports["Report136.tex"],"stage TeX document")
    data=reports|{"certificate/"+name:value for name,value in certificate.items()}
    new_dir(v,destination)
    new_dir(v,destination/"certificate")
    for name,value in sorted(data.items()):
        write_file(v,destination/name,value)
    write_file(v,destination/"bundle-manifest.json",v.canonical(record(v,data)))
    check(v,destination)
    print("PASS: staged closed integrated bundle at "+str(destination))


def pack(v,data,destination):
    v.ancestors(destination,True)
    flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,"O_NOFOLLOW",0)
    fd=os.open(destination,flags,0o600)
    with os.fdopen(fd,"wb") as stream:
        with zipfile.ZipFile(stream,"w",compression=zipfile.ZIP_STORED) as archive:
            for name,value in sorted(data.items()):
                info=zipfile.ZipInfo("Report136/"+name,date_time=(1980,1,1,0,0,0))
                info.create_system=3
                info.external_attr=(stat.S_IFREG|0o644)<<16
                info.compress_type=zipfile.ZIP_STORED
                info.flag_bits=0
                archive.writestr(info,value)
    return hashlib.sha256(v.regular_bytes(destination)).hexdigest()


def build(v,data,destination):
    new_dir(v,destination)
    write_file(v,destination/"Report136.tex",data["Report136.tex"])
    env=os.environ.copy()
    env.update({"SOURCE_DATE_EPOCH":str(EPOCH),"FORCE_SOURCE_DATE":"1","TZ":"UTC","LC_ALL":"C"})
    for variable,folder in (("TEXMFVAR","texmf-var"),("TEXMFCONFIG","texmf-config"),
                            ("TEXMFCACHE","texmf-cache"),("XDG_CACHE_HOME","xdg-cache")):
        new_dir(v,destination/folder)
        env[variable]=str(destination/folder)
    if Path("/usr/share/texlive/texmf-dist").is_dir():
        env["TEXMF"]="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
    env["TEXFORMATS"]=str(destination)+"//:"
    format_command=["pdftex","-ini","-etex","-no-shell-escape","-interaction=nonstopmode",
                    "-halt-on-error","-jobname=pdflatex","pdflatex.ini"]
    source=r"\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report136.tex}"
    command=["pdflatex","-no-shell-escape","-interaction=nonstopmode","-halt-on-error","-file-line-error",source]
    flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,"O_NOFOLLOW",0)
    with os.fdopen(os.open(destination/"build-console.txt",flags,0o600),"wb") as log:
        subprocess.run(format_command,cwd=destination,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
        for _ in range(2):
            subprocess.run(command,cwd=destination,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
    log=v.regular_bytes(destination/"Report136.log").decode("utf-8",errors="replace")
    for warning in (r"Overfull \hbox",r"Overfull \vbox","undefined references","multiply defined",
                    "undefined citations","Missing character:","Label(s) may have changed"):
        v.need(warning not in log,"TeX QA warning: "+warning)
    pdf=v.regular_bytes(destination/"Report136.pdf")
    result={"schema":"report136-clean-build-v1","pdf_sha256":hashlib.sha256(pdf).hexdigest(),
            "frozen_pdf_sha256":hashlib.sha256(data["Report136.pdf"]).hexdigest(),
            "matches_frozen_pdf":"yes" if pdf==data["Report136.pdf"] else "no",
            "source_date_epoch":EPOCH,"latex_passes":2}
    write_file(v,destination/"build-result.json",v.canonical(result))
    v.need(pdf==data["Report136.pdf"],"clean build differs from frozen PDF; see build-result.json")
    print("PASS: clean PDF build is byte-identical; SHA-256 "+result["pdf_sha256"])


def selftest(v,data):
    passed=[]
    with tempfile.TemporaryDirectory(prefix="report136-integrated-") as folder:
        base=Path(folder)
        def copied(name):
            root=base/name
            root.mkdir()
            (root/"certificate").mkdir()
            for filename,value in data.items():
                (root/filename).write_bytes(value)
            return root
        def reject(label,operation):
            try:
                operation()
            except (v.Rejected,ValueError,OSError):
                passed.append(label)
            else:
                raise v.Rejected("integrated guard accepted "+label)
        clean=copied("clean")
        check(v,clean)
        for label,mutator in (
            ("extra root file",lambda p:(p/"extra").write_text("x")),
            ("missing report PDF",lambda p:(p/"Report136.pdf").unlink()),
            ("modified report",lambda p:(p/"Report136.tex").write_bytes(data["Report136.tex"]+b"\n")),
            ("nested extra file",lambda p:(p/"certificate"/"extra").write_text("x")),
            ("report symlink",lambda p:((p/"Report136.pdf").unlink(),(p/"Report136.pdf").symlink_to(clean/"Report136.pdf"))),
        ):
            root=copied("case"+str(len(passed)))
            mutator(root)
            reject(label,lambda:check(v,root))
        alias=base/"root-link"; alias.symlink_to(clean,target_is_directory=True)
        reject("integrated root symlink",lambda:check(v,alias))
        reject("bundle output within source",lambda:v.output_preflight(clean/"x",clean))
        first,second=base/"first.zip",base/"second.zip"
        pack(v,check(v,clean),first)
        extract=base/"extraction"; extract.mkdir()
        # Only extract our freshly created archive, and check its exact members first.
        with zipfile.ZipFile(first) as archive:
            v.need(set(archive.namelist())=={"Report136/"+name for name in data},"ZIP member inventory")
            archive.extractall(extract)
        unpacked=extract/"Report136"
        unpacked_data=check(v,unpacked)
        pack(v,unpacked_data,second)
        v.need(first.read_bytes()==second.read_bytes(),"ZIP repack must be byte-identical")
        passed.append("fresh extraction deterministic ZIP repack")
        # The delivered runner itself is replayed in both normal and optimized modes.
        for optimize in (False,True):
            command=[sys.executable,"-I","-B"]+(["-O"] if optimize else [])+[str(unpacked/"certificate"/"verify.py"),"replay"]
            result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
            v.need(result.returncode==0,"extracted replay failed: "+result.stderr.decode(errors="replace"))
            passed.append("extracted replay "+("optimized" if optimize else "normal"))
    print("PASS: "+str(len(passed))+" integrated guards/repack/replay checks")
    for label in passed:
        print("  "+label)


def execute(v,args,certificate):
    if args.command=="bundle-stage":
        v.need(args.report_root is not None and args.output is not None,"bundle-stage needs --report-root and --output")
        v.need(args.bundle is None,"bundle-stage does not use --bundle")
        destination=v.output_preflight(args.output,v.ROOT)
        stage(v,certificate,args.report_root,destination)
        return
    v.need(args.bundle is not None,"integrated command needs --bundle")
    v.need(args.report_root is None,"--report-root is only for bundle-stage")
    root=v.absolute(args.bundle)
    data=check(v,root)
    needs_output=args.command in ("bundle-pack","bundle-build")
    v.need((args.output is not None)==needs_output,"--output is required only for bundle-stage, bundle-pack, and bundle-build")
    destination=v.output_preflight(args.output,root) if needs_output else None
    if args.command=="bundle-check":
        print("PASS: integrated closed inventory and all digests")
    elif args.command=="bundle-pack":
        print("PASS: deterministic ZIP SHA-256 "+pack(v,data,destination))
    elif args.command=="bundle-build":
        build(v,data,destination)
    elif args.command=="bundle-selftest":
        selftest(v,data)
    else:
        raise v.Rejected("unknown integrated command")

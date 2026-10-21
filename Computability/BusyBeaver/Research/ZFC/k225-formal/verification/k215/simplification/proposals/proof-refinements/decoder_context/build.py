#!/usr/bin/env python3
"""Fresh, serial standalone Lean build. Does not reuse project proof objects."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, time
p=argparse.ArgumentParser()
p.add_argument('--lean',required=True,type=Path)
p.add_argument('--out',required=True,type=Path)
a=p.parse_args(); src=Path(__file__).resolve().parent
out=a.out.resolve(); out.mkdir(parents=True,exist_ok=True)
if any(out.glob('*.olean')): raise SystemExit('output directory must not contain proof objects')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=os.environ.copy(); env['LEAN_PATH']=str(out)
version=subprocess.check_output([str(a.lean.resolve()),'--version'],text=True).strip()
receipt={'status':'IN_PROGRESS','toolchain':version,'modules':[],'scope':'New decoder-context and internal-source-path theorems, including inherited standalone decoder foundations; not a rebuilt ZFC endpoint.'}
for name in ['FramedWindow','DecoderCertificate','K215Decoder','DecoderContext','K215Context','Audit']:
    source=src/(name+'.lean'); target=out/(name+'.olean'); log=out/(name+'.log')
    if re.search(r'\b(sorry|admit|native_decide)\b',source.read_text()):
        raise SystemExit('forbidden proof placeholder/evaluator in '+name)
    cmd=[str(a.lean.resolve()),'-o',str(target),source.name]
    started=time.monotonic()
    cp=subprocess.run(cmd,cwd=src,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-started; log.write_text(cp.stdout)
    item={'name':name,'returncode':cp.returncode,'seconds':elapsed,'source_sha256':sha(source),'log_sha256':sha(log),'warnings':len(re.findall(r'warning:',cp.stdout)),'axiom_reports':re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",cp.stdout)}
    if target.exists():item['object_sha256']=sha(target)
    receipt['modules'].append(item)
    if cp.returncode or 'sorryAx' in cp.stdout or item['warnings']:
        receipt['status']='FAIL'; (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(cp.stdout);raise SystemExit(1)
receipt['status']='PASS_FRESH_KERNEL'
receipt['total_seconds']=sum(x['seconds']for x in receipt['modules'])
receipt['all_sources_sha256']={f.name:sha(f)for f in sorted(src.glob('*.lean')) if f.name!='Probe.lean'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

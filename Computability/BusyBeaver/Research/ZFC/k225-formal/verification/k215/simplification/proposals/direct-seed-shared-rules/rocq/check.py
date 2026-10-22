#!/usr/bin/env python3
"""Compile the exact-name facades and the existing downstream metatheory.

Runs with Coq 8.18.0. The sole compatibility edit to preserved consumers is
'From Stdlib Require' -> 'From Coq Require'. This is not a Rocq 9.1 endpoint
build. Proof objects go in build/, never into the ProveIt checkout.
"""
from pathlib import Path
import hashlib, json, shutil, subprocess, time

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'build'
ORDER=[
 ('K215Common','PropositionalCore','proof/PropositionalCore.v'),
 ('ZF','Logic','upstream/ZF/Logic.v'),
 ('ZF','L1_LDef','upstream/ZF/L1_LDef.v'),
 ('ZF','L1_LProp','proof/L1_LProp.v'),
 ('ZF','L1_LMeta','upstream/ZF/L1_LMeta.v'),
 ('K230S','KCode230','upstream/K230S/KCode230.v'),
 ('K215F','L224Def','upstream/K215F/L224Def.v'),
 ('K215F','L224Prop','proof/L224Prop.v'),
 ('K215F','L224Meta','upstream/K215F/L224Meta.v'),
 ('K215Common','PropositionalAPIAudit','proof/PropositionalAPIAudit.v'),
]
flags=[]
for ns in ('ZF','K230S','K215F','K215Common'):
    (OUT/ns).mkdir(parents=True,exist_ok=True)
    flags += ['-Q',str(OUT/ns),ns]
ledger=[]
for ns,name,source in ORDER:
    raw=(ROOT/source).read_bytes()
    s=raw.decode().replace('From Stdlib Require','From Coq Require')
    dest=OUT/ns/(name+'.v')
    dest.write_text(s)
    t=time.monotonic()
    p=subprocess.run(['coqc','-q',*flags,str(dest)],capture_output=True,text=True)
    log=(ROOT/'evidence'/f'{ns}.{name}.log')
    log.write_text(p.stdout+p.stderr)
    item=dict(module=ns+'.'+name,source=source,
        source_sha256=hashlib.sha256(raw).hexdigest(),
        compiled_source_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),
        compatibility_edit=(s!=raw.decode()),seconds=round(time.monotonic()-t,4),
        exit_code=p.returncode,log=str(log.relative_to(ROOT)))
    if p.returncode==0:
        item['object_sha256']=hashlib.sha256(dest.with_suffix('.vo').read_bytes()).hexdigest()
    ledger.append(item)
    print(json.dumps(item),flush=True)
    if p.returncode:
        print(p.stdout+p.stderr,flush=True)
        break
if all(i['exit_code']==0 for i in ledger) and len(ledger)==len(ORDER):
    t=time.monotonic()
    p=subprocess.run(['coqchk','-silent',*flags,'K215Common.PropositionalAPIAudit',
                      'K215F.L224Meta','ZF.L1_LMeta'],capture_output=True,text=True)
    (ROOT/'evidence/coqchk.log').write_text(p.stdout+p.stderr)
    kernel=dict(exit_code=p.returncode,seconds=round(time.monotonic()-t,4),
                log='evidence/coqchk.log')
else:
    kernel=None
summary=dict(compiler=subprocess.check_output(['coqc','--version'],text=True).strip(),
             modules=ledger,kernel=kernel,
             status='PASS' if kernel and kernel['exit_code']==0 else 'FAIL')
(ROOT/'evidence/check.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='modules'},indent=2))
raise SystemExit(0 if summary['status']=='PASS' else 1)

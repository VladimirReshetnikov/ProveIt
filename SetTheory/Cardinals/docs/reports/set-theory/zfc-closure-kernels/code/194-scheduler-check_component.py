#!/usr/bin/env python3
"""Build the scheduler and current EnumPerm/SeedPerm clients in a fresh tree."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--coqc',default='coqc')
p.add_argument('--coqchk',default='coqchk')
a=p.parse_args()
here=Path(__file__).resolve().parent
repo=a.repo.resolve(); out=a.out.resolve()
if out.exists() and any(out.iterdir()): raise SystemExit('--out must be empty or absent')
out.mkdir(parents=True,exist_ok=True); (out/'logs').mkdir()
base=repo/'Computability/BusyBeaver/Research/ZFC/k225-formal'
actual=base/'rocq/rocq-extension/coq/215'
deps=base/'verification/k215/simplification/proposals/checked-transport/rocq_seed_rank/source'
sha=lambda b: hashlib.sha256(b).hexdigest()
version=subprocess.check_output([a.coqc,'--version'],text=True)
compat='version 8.' in version
receipt={'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'version':version,'stdlib_namespace_compatibility':compat,'sources':[],'checks':[],'full_tm_endpoint_rebuilt':False}
order=[('K230S','KCode230',deps/'K230S/KCode230.v'),('K230L','Codes230',deps/'K230L/Codes230.v')]
for name in ('Codes222','Thm222','DomRho8','ThmDom','EnumPerm','L1_SoundPerm'):
    order.append(('K215F',name,actual/(name+'.v')))
for name in ('CandidateScheduler','L1_CompPerm','SeedPerm'):
    order.append(('K215F',name,here/(name+'.v')))
for ns,name,src in order:
    data=src.read_bytes(); compiled=data.replace(b'From Stdlib ',b'From Coq ') if compat else data
    dest=out/ns/(name+'.v'); dest.parent.mkdir(exist_ok=True); dest.write_bytes(compiled)
    receipt['sources'].append({'module':ns+'.'+name,'source':str(src),'sha256':sha(data),'compiled_sha256':sha(compiled),'namespace_alias_count':data.count(b'From Stdlib ') if compat else 0})
flags=['-Q','K230S','K230S','-Q','K230L','K230L','-Q','K215F','K215F']
def save(): (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
def run(name,cmd):
    started=time.monotonic();r=subprocess.run(cmd,cwd=out,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=out/'logs'/(name+'.log');log.write_bytes(r.stdout)
    receipt['checks'].append({'name':name,'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-started,'log_sha256':sha(r.stdout)})
    save();print(name,r.returncode,flush=True)
    if r.returncode:
        print(r.stdout.decode(errors='replace'));raise SystemExit(r.returncode)
for ns,name,src in order:
    run(ns+'.'+name,[a.coqc,*flags,ns+'/'+name+'.v'])
client='''From K215F Require Import CandidateScheduler Codes222 Thm222 EnumPerm L1_SoundPerm L1_CompPerm SeedPerm.
Check (enum_complete : thm222 1 -> enum_halts).
Check (seedPerm_complete : thm222 1 -> halts_from seedPerm).
Check (seedPerm_sound : halts_from seedPerm -> thm222 1).
Check (seedPerm_iff_thm : halts_from seedPerm <-> thm222 1).
Check (enum_complete_from : forall s, thm222 1 -> halts_from s).
Check (enum_from_iff : forall s, Inv s -> (halts_from s <-> thm222 1)).
Print Assumptions CandidateScheduler.seek.
Print Assumptions CandidateScheduler.complete_at.
Print Assumptions CandidateScheduler.cofinal_complete.
Print Assumptions enum_complete_from.
Print Assumptions enum_from_iff.
Print Assumptions seedPerm_iff_thm.
'''
(out/'Client.v').write_text(client)
run('Client',[a.coqc,*flags,'Client.v'])
run('coqchk',[a.coqchk,*flags,'K215F.CandidateScheduler','K215F.SeedPerm','Client'])
receipt['status']='PASS';save()

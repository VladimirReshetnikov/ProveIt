#!/usr/bin/env python3
"""Lightweight integrity, measurement and source-to-receipt binding audit.
This checks recorded evidence, not the proof kernels or full search anew.
Run the explicit component replay commands for independent proof checking.
"""
from pathlib import Path
import hashlib, json, re, subprocess, sys
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads((ROOT/p).read_text())
def require(ok,msg):
    if not ok:raise SystemExit('FAIL: '+msg)
def main():
    manifest=read('MANIFEST.json')
    for row in manifest['files']:
        p=ROOT/row['path']
        require(p.is_file(), 'missing '+row['path'])
        require(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'], 'hash '+row['path'])
    for name,count in [('lean-receipt.json',28),('four-calculus-lean-receipt.json',13)]:
        receipt=read('proofs/verification/'+name)
        require(receipt['status']=='PASS' and receipt['fresh_modules']==count,name)
        require(len(receipt['records'])==count,name+' count')
        for row in receipt['records']:
            p=ROOT/'proofs/formal'/(row['module'].replace('.','/')+'.lean')
            require(row['exit_code']==0 and sha(p)==row['source_sha256'],row['module'])
    for name,module in [('rocq-receipt.json','DominatedImplication'),('four-shape-rocq-receipt.json','FourShapeImplication')]:
        receipt=read('proofs/verification/'+name)
        require(receipt['status']=='PASS' and receipt['source_sha256']==sha(ROOT/'proofs/rocq'/(module+'.v')),name)
        require({r['tool'] for r in receipt['records']}=={'coqc','coqchk'},name+' tools')
        require(all(r['exit_code']==0 for r in receipt['records']),name+' return codes')
        compiler=next(r for r in receipt['records'] if r['tool']=='coqc')
        require(compiler['stdout'].count('Closed under the global context')==3,module+' assumptions')
    receipt=read('source_checker/verification/result.json')
    require(receipt['complete'] and receipt['recursive_kernel_check']=='passed','source checker result')
    for row in receipt['sources']:
        name=row['name'];path='deps/K230/RMEquiv.rocq91.v' if name=='deps/K230/RMEquiv.v' else name
        b=(ROOT/'source_checker'/path).read_bytes()
        require(hashlib.sha256(b).hexdigest()==row['delivered_sha256'],'source delivered '+name)
        if name=='deps/K230/RMEquiv.v':
            needle=b'From K230 Require Import RM.'
            require(b.count(needle)==1,'compatibility anchor')
            b=b.replace(needle,needle+b'\nRequire Import Compat818.')
        require(hashlib.sha256(b).hexdigest()==row['compiled_sha256'],'source compiled '+name)
    for row in receipt['checks']:
        require(row['exit_code']==0,'source check '+row['name'])
        require(sha(ROOT/'source_checker/verification/logs'/(row['name']+'.log'))==row['log_sha256'],'source log '+row['name'])
    for row in read('source_checker/source_bindings.json')['files']:
        b=(ROOT/'source_checker'/row['local_path']).read_bytes()
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==row['git_blob_sha1'] and hashlib.sha256(b).hexdigest()==row['sha256'],'pinned '+row['local_path'])
    metrics={}
    for name,p in [('baseline',ROOT/'proofs/reference/DomRho8.before.lean'),('core',ROOT/'proofs/formal/BusyBeaver/ZFC/DominatedImplication.lean'),('adapter',ROOT/'proofs/formal/BusyBeaver/ZFC/DomRho8.lean')]:
        b=p.read_bytes();metrics[name]={'bytes':len(b),'lines':len(b.splitlines())}
    require(metrics=={'baseline':{'bytes':30114,'lines':517},'core':{'bytes':19752,'lines':388},'adapter':{'bytes':2526,'lines':70}},'source measurements')
    require((ROOT/'proofs/verification/ksim-api-before.log').read_bytes()==(ROOT/'proofs/verification/ksim-api-after.log').read_bytes(),'KSim API comparison')
    generated=ROOT/'generation/generation'
    for src,dst in [('DominatedImplication.lean','DominatedImplication.lean'),('DomRho8.adapter.lean','DomRho8.lean'),('FourShapeImplication.lean','FourShapeImplication.lean')]:
        require((generated/src).read_bytes()==(ROOT/'proofs/formal/BusyBeaver/ZFC'/dst).read_bytes(),'generated proof '+src)
    ft=ROOT/'machine_research/ft-frontier'
    result=json.loads((ft/'result.json').read_text())
    require(result['modified_table_sha256']==sha(ft/'machine.native.tm'),'FT table')
    require(result['certificate_sha256']==sha(ft/'join-certificate.json'),'FT certificate')
    require(len(json.loads((ft/'join-certificate.json').read_text()))==4736,'FT join count')
    for q in [38,134]:
        d=json.loads((ft/f'allocation-{q}/result.json').read_text())
        require(d['status']=='NO_ALLOCATION','allocation status')
        w=d['hall_witness'];union=set()
        for r in w['roles']:union.update(r['domain_states'])
        slots=w['slots']
        require(w['role_count']==115 and len(w['roles'])==115 and len({r['path'] for r in w['roles']})==115,'Hall role count')
        require(w['slot_count']==114 and len(slots)==114,'Hall slot count')
        require(all(slot[1]==0 for slot in slots),'Hall unit capacity')
        require(union=={slot[0] for slot in slots},'Hall full allowed union')
        require(len(union)<len(w['roles']),'Hall strict deficit')
    subprocess.run([sys.executable,str(ROOT/'source_checker/lookup_metrics.py'),'--check'],check=True)
    print(json.dumps({'status':'PASS','manifest_files':len(manifest['files']),
        'formal_receipts_bound':5,'source_measurements':metrics,
        'hall_witnesses_checked':2,
        'scope':'Integrity and recorded-evidence audit; not a proof-kernel or full-search replay.'},indent=2))
if __name__=='__main__':main()

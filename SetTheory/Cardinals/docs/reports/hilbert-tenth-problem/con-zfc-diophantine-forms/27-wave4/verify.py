#!/usr/bin/env python3
"""Verify the sealed release, then replay finite checks in a temporary copy.

No search for a solution or a K215 halt is performed. Passing this program
does not replace any universal mathematical proof or a proof-assistant build.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
REPLAYS=[
 'coefficients/build_mixed.py',
 'coefficients/audit_independent.py',
 'root/check_mixed_independent.py',
 'norms/build_two_weight_norm12.py',
 'norms/check_separation.py',
 'integers/build_integer24.py',
 'integers/build_low_degree.py',
 'operations/build_operations.py',
 'nine/build_improved.py',
 'nine/verify_improved.py',
 'nine/verify_fixed_binding.py',
 'review/check_novel_norms_independent.py',
 'review/check_nine_improvements_independent.py',
 'review/check_low_degree_new_independent.py',
]

def require(p,message):
    if not p:raise ValueError(message)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    return json.loads(p.read_text())

def check_manifest(root):
    manifest=read(root/'SHA256SUMS.json')
    for rel,want in manifest.items():
        p=Path(rel)
        require(not p.is_absolute() and '..' not in p.parts,'Unsafe manifest path')
        target=root/p
        require(target.is_file() and not target.is_symlink(),'Missing/nonregular sealed file: '+rel)
        require(digest(target)==want,'Sealed hash mismatch: '+rel)
    return len(manifest)

def check_instance(root):
    instance=read(root/'INSTANCE.json')
    binding=read(root/'coefficients/COEFFICIENT_BINDING.json')
    require(instance['tuple_id']==binding['tuple_id']=='wang943-mixed-radix4-zero-fields-5pow9','Wrong tuple')
    aggregate=hashlib.sha256()
    for port in ['beta','K','MC','MF_source']:
        p=root/'coefficients/expanded'/f'{port}.bin'
        aggregate.update(p.read_bytes())
        require(digest(p)==instance['ports'][port]['sha256']==binding['ports'][port]['sha256'],'Wrong port '+port)
    require(aggregate.hexdigest()==instance['tuple_sha256'],'Wrong ordered tuple hash')
    for name in ['norms','integers','operations']:
        b=read(root/name/'COEFFICIENT_BINDING.json')
        require(b['tuple_id']==instance['tuple_id'] and b['tuple_sha256']==instance['tuple_sha256'],'Partial binding '+name)
        require(b['aliases']=={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'Port alias mismatch')
    n=0
    for name,pattern in [('norms','two_weight_norm12_*.json'),('integers','integer*.json')]:
        for p in (root/name).glob(pattern):
            obj=read(p)
            require(obj['coefficient_binding']['tuple_id']==instance['tuple_id'],'Stale packet '+str(p))
            require(obj['coefficient_binding']['tuple_sha256']==instance['tuple_sha256'],'Stale packet hash')
            n+=1
    for p in (root/'operations').glob('*.json'):
        obj=read(p)
        if isinstance(obj,dict) and 'source' in obj:
            require(obj['coefficient_binding']=='COEFFICIENT_BINDING.json','Stale system binding')
            require(obj['selected_coefficient_variant']==instance['tuple_id'],'Stale system tuple')
            n+=1
    tm=root/'coefficients/sources/k215.tm'
    require(digest(tm)=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','Wrong literal machine')
    rows=[]
    for line in tm.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        q,b,w,m,t=line.split()
        rows.append([int(q),int(b),int(w),{'L':-1,'R':1}[m],int(t)])
    require(rows==read(root/'coefficients/sources/k215_transitions.json')['transitions'],'Transition export mismatch')
    require(len(rows)==430 and {(r[0],r[1]) for r in rows}=={(q,b) for q in range(215) for b in (0,1)},'Transition coverage')
    expected=[('norms/two_weight_norm12_product.json',12,120,1081),
      ('integers/integer24_original_product.json',24,163,2432),
      ('integers/integer24_split2_product.json',24,164,2256),
      ('integers/integer24_ratio_product.json',24,168,1936)]
    for rel,u,g,d in expected:
        p=read(root/rel)
        require(len(p['witnesses'])==u and len(p['source'])==g and p['exact_degree']==d,'Headline metrics '+rel)
    for p in (root/'nine/generated').glob('nine_*_dag.json'):
        b=read(p)['coefficient_binding']
        require(b['tuple_id']==instance['tuple_id'] and b['tuple_sha256']==instance['tuple_sha256'],'Stale Jones binding')
        n+=1
    ledger=read(root/'nine/generated/ledger.json')
    require(ledger['majorant_specialized']['operations']==1485,'Nine old-polynomial count')
    for key,g in [('natural-majorant_specialized',1542),('natural-majorant_specialized_positive',1537)]:
        require(ledger[key]['operations']==g and ledger[key]['degree']==120764*5**33+368,'Nine new metrics')
    return {'tuple_id':instance['tuple_id'],'tuple_sha256':instance['tuple_sha256'],
            'explicitly_bound_new_packets':n,'literal_transitions':430,'headline_metrics':'PASS'}

def replay(root):
    result=[];all_rebuilt=set()
    with tempfile.TemporaryDirectory(prefix='con_zfc_wave4_') as td:
        work=Path(td)/'release'
        shutil.copytree(root,work)
        for script in REPLAYS:
            before={p.relative_to(work).as_posix():p.stat().st_mtime_ns for p in work.rglob('*') if p.is_file()}
            proc=subprocess.run([sys.executable,'-B',str(work/script)],cwd=work,
                 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
            require(proc.returncode==0,script+' failed:\n'+proc.stdout[-2000:]+proc.stderr[-2000:])
            changed=[]
            for p in work.rglob('*'):
                if not p.is_file():continue
                rel=p.relative_to(work).as_posix()
                if before.get(rel)!=p.stat().st_mtime_ns:
                    require((root/rel).is_file(),'Unexpected replay output '+rel)
                    require(digest(p)==digest(root/rel),'Rebuilt bytes differ: '+rel)
                    changed.append(rel)
            require(changed,'Stage wrote no checked output: '+script)
            all_rebuilt.update(changed)
            result.append({'script':script,'status':'PASS','byte_identical_outputs':sorted(changed)})
    return result,len(all_rebuilt)

def main():
    require(__debug__,'Do not run with Python -O')
    parser=argparse.ArgumentParser()
    parser.add_argument('--quick',action='store_true',help='Hashes and instance only, without replay')
    parser.add_argument('--out',type=Path,help='Optional receipt outside the release directory')
    a=parser.parse_args()
    if a.out:
        require(not a.out.resolve().is_relative_to(ROOT),'Write receipts outside the sealed release')
    count=check_manifest(ROOT);instance=check_instance(ROOT)
    stages,rebuilt=([],0) if a.quick else replay(ROOT)
    require(check_manifest(ROOT)==count,'Original release changed')
    receipt={'status':'PASS','mode':'quick' if a.quick else 'full','sealed_files_checked':count,
      'instance':instance,'replay_stage_count':len(stages),'distinct_byte_identical_rebuilt_files':rebuilt,
      'stages':stages,'scope':'Finite reproducibility and integrity, not a kernel proof or a solvability test.'}
    encoded=json.dumps(receipt,indent=2)+'\n'
    if a.out:a.out.write_text(encoded)
    print(encoded)

if __name__=='__main__':main()

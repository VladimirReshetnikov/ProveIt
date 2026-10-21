#!/usr/bin/env python3
"""Reconstruct and check the exact candidate; optionally replay all runtime cases.

Python 3 standard library only. Run without -O. Fresh outputs stay under
reproduced/ and never replace delivered machine files or saved evidence.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, shutil, subprocess, sys, time

ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write_json(p,x):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(x,indent=2)+'\n')
def read_table(p):
    table={};starts=[]
    for line in p.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();key=(int(q),int(b))
        assert key not in table and d in ('L','R')
        table[key]=(int(w),d,int(z))
    assert starts==[0]
    return table
def table_bytes(t):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'
            for (q,b),(w,d,z) in sorted(t.items()))).encode('ascii')

def main():
    assert __debug__ and not sys.flags.optimize, 'Assertions must be enabled.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full-runtime',action='store_true')
    args=ap.parse_args();beg=time.monotonic();out=ROOT/'reproduced';out.mkdir(exist_ok=True)
    manifest=ROOT/'manifest.json';verified=0
    if manifest.exists():
        for rec in json.loads(manifest.read_text())['files']:
            p=ROOT/rec['path'];assert p.is_file() and sha(p)==rec['sha256'],rec['path']
            verified+=1
        print(f'MANIFEST PASS: {verified} exact files',flush=True)
    parent=ROOT/'inputs/upstream216';machine=ROOT/'machine'
    assert sha(parent/'k216.native.tm')=='2efb7adf9cfcbea58197a2bde2610b22f58b647f05385bc716b036242be6fa6c'
    assert sha(parent/'sites216.compact.json')=='7f9d4f321b7a7d56013056b1ad6be2723538c43ea2d73548bcd0e35f0381bde0'
    t=read_table(parent/'k216.native.tm')
    for key,old,new in [((199,1),(1,'R',166),(1,'R',12)),((206,0),(0,'R',186),(0,'R',76))]:
        assert t[key]==old;t[key]=new
    rebuilt=table_bytes(t);assert rebuilt==(machine/'k216-rho6.native.tm').read_bytes()
    rows=json.loads((parent/'sites216.compact.json').read_text())
    for i in range(902,1185):
        if rows[i][1] in ('CI','CD'):rows[i][2]={3:5,5:3}.get(rows[i][2],rows[i][2])
    source=(json.dumps(rows,separators=(',',':'))+'\n').encode('ascii')
    assert source==(machine/'sites216.json').read_bytes()
    stage=out/'audit_root'
    (stage/'machine').mkdir(parents=True,exist_ok=True)
    (stage/'inputs/upstream216').mkdir(parents=True,exist_ok=True)
    (stage/'machine/k216-rho6.native.tm').write_bytes(rebuilt)
    (stage/'machine/sites216.json').write_bytes(source)
    shutil.copy2(machine/'k216-rho6.tm',stage/'machine/k216-rho6.tm')
    for name in ('k216.native.tm','sites216.compact.json','canonicalization.json'):
        shutil.copy2(parent/name,stage/'inputs/upstream216'/name)
    run=subprocess.run([sys.executable,'-B',str(ROOT/'code/audit.py'),'--root',str(stage)],
                       text=True,capture_output=True)
    (out/'source_blank.log').write_text(run.stdout+run.stderr)
    assert run.returncode==0, 'Source/startup audit failed: see reproduced/source_blank.log'
    shutil.copy2(stage/'evidence/source_blank.json',out/'source_blank.json')
    blank=json.loads((out/'source_blank.json').read_text())
    assert blank['startup']['steps']==313133 and blank['working_states']==216
    print('CONSTRUCTION, SOURCE, CANONICALIZATION, COMPLETE BLANK: PASS',flush=True)
    sys.path.insert(0,str(ROOT/'code/theory'))
    import check_pairing,check_diagonal_matrix
    pairing=check_pairing.check();matrix=check_diagonal_matrix.check()
    write_json(out/'pairing_certificate.json',pairing);write_json(out/'diagonal_matrix.json',matrix)
    print('DOMINATED CERTIFICATE, PAIRING PREMISE, THREE-VALUED MATRIX: PASS',flush=True)
    run=subprocess.run([sys.executable,'-B',str(ROOT/'code/theory/protected_credit.py')],
                       text=True,capture_output=True)
    assert run.returncode==0,run.stderr
    credit=json.loads(run.stdout);write_json(out/'protected_credit.json',credit)
    print('FINITE PROTECTED-CREDIT SUPPORT CHECK: PASS (separate all-natural proof required)',flush=True)
    receipt=json.loads((ROOT/'evidence/runtime.json').read_text())
    assert receipt['table_sha256']==sha(machine/'k216-rho6.native.tm')
    assert receipt['source_sha256']==sha(machine/'sites216.json')
    assert receipt['engine_sha256']==sha(ROOT/'code/runtime/symbolic_runtime.py')
    assert receipt['helper_sha256']==sha(ROOT/'code/runtime/independent_runtime.py')
    assert receipt['status']=='ALL_PRIMITIVE_INTERFACES_PROVED'
    with gzip.open(ROOT/'evidence/runtime.cases.json.gz','rt') as f:cases=json.load(f)
    assert len(cases)==6176 and sum(c['symbolic_steps'] for c in cases)==1711040
    assert min(c['duration'][0] for c in cases)==13
    print('SAVED RUNTIME INPUT BINDING AND ORDERED-CASE RECEIPTS: PASS',flush=True)
    if args.full_runtime:
        subprocess.run([sys.executable,'-B',str(ROOT/'code/runtime/run_candidate.py'),
                        '--table',str(machine/'k216-rho6.native.tm'),
                        '--sites',str(machine/'sites216.json'),
                        '--output',str(out/'runtime.json')],check=True)
        fresh=json.loads((out/'runtime.json').read_text())
        assert {k:v for k,v in fresh.items() if k!='seconds'}=={k:v for k,v in receipt.items() if k!='seconds'}
        with gzip.open(out/'runtime.cases.json.gz','rt') as f:assert json.load(f)==cases
        print('FULL FRESH SYMBOLIC RUNTIME AND ALL ORDERED CASES: PASS',flush=True)
    result={'status':'FULL_REPRODUCTION_PASS' if args.full_runtime else 'FINITE_REPRODUCTION_PASS',
            'manifest_files_verified':verified,'full_runtime_replayed':args.full_runtime,
            'working_states':216,'rows':432,'startup_steps':313133,
            'runtime_saved_cases':6176,'seconds':time.monotonic()-beg,
            'scope':'Finite exact construction/startup and logical certificate checks; --full-runtime additionally reruns the universal symbolic primitive contracts. Inherited calculus calibration and ordinary proofs remain explicit premises.'}
    write_json(out/'reproduction_summary.json',result);print(json.dumps(result,indent=2))

if __name__=='__main__':main()

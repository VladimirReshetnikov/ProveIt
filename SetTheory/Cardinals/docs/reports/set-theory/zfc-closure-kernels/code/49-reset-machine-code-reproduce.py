#!/usr/bin/env python3
"""Reproduce the finite census on the exact permutation252 input.

Python 3.11+ and a C++17 compiler suffice. Temporary executables and window
sets are created outside the package. Use --radius 6 8 for both full runs.
"""
from pathlib import Path
import argparse, collections, hashlib, json, shutil, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
EXPECTED='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'

def table_input(path):
    raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==EXPECTED
    rows={};start=None
    for line in raw.decode().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,t=line.split();key=int(q),int(b)
            assert key not in rows and d in ('L','R')
            rows[key]=int(w),1 if d=='R' else -1,int(t)
    states={q for q,b in rows};halt,={t for w,d,t in rows.values()}-states
    assert start in states and len(states)==252 and len(rows)==504
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    labels=[start]+sorted(states-{start});mapping={q:i for i,q in enumerate(labels)};mapping[halt]=252
    return {(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in rows.items()}

def python_windows(rows,radius):
    # Independent sparse-set reference for the native dense-array calculation.
    mask=(1<<(2*radius+1))-1;todo=collections.deque([(0,0)]);seen={(0,0)}
    while todo:
        q,p=todo.popleft()
        if q==252:continue
        w,d,t=rows[q,(p>>radius)&1];p=(p&~(1<<radius))|(w<<radius)
        base,extra=(p>>1,1<<(2*radius)) if d==1 else ((p<<1)&mask,1)
        for x in (base,base|extra):
            if (t,x) not in seen:seen.add((t,x));todo.append((t,x))
    return seen

def read_windows(path):
    with path.open() as f:
        n,r,k=map(int,f.readline().split());assert n==252
        for _ in range(2*n):f.readline()
        groups=[]
        for q in range(n+1):
            count,*values=map(int,f.readline().split());assert count==len(values)
            assert values==sorted(set(values));groups.append(values)
        assert not f.read().strip()
    return r,k,groups

def functional(summary):return {k:v for k,v in summary.items() if k!='elapsed_seconds'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--radius',nargs='+',type=int,default=[6]);ap.add_argument('--compiler',default='g++');ap.add_argument('--compare-eager',action='store_true');ap.add_argument('--quick',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
    assert __debug__ and all(r in (6,8) for r in args.radius)
    rows=table_input(PACKAGE/'inputs/permutation252_old.tm')
    import joint_rotation_search as joint
    base=joint.emit(joint.NODES,joint.ROOT_NODE);assert base==joint.read_table(PACKAGE/'inputs/permutation252_old.tm')
    cert,_=joint.certify(base,joint.NODES,joint.ROOT_NODE);assert cert['passed'] and cert['cases']==8391
    boot,_=joint.boot(base,82552);assert boot['outcome']=='zero_root' and boot['steps']==82552
    saved=json.loads((PACKAGE/'results/joint_rotation0.json').read_text());assert boot==saved['baseline']['boot']
    out={'baseline_affine_cases':8391,'baseline_boot_steps':82552,'baseline_full_frame_matches':True,'censuses':[]}
    if not args.quick:
        with tempfile.TemporaryDirectory(prefix='zfc252-census-') as td:
            work=Path(td);inp=work/'table.input'
            with inp.open('w') as f:
                print(252,6,64,file=f)
                for q in range(252):
                    for b in (0,1):print(*rows[q,b],file=f)
            for stem in ['abstract_windows','exhaustive_fusions_lazy']+(['exhaustive_fusions'] if args.compare_eager else []):
                subprocess.run([args.compiler,'-O3','-std=c++17','-Wall','-Wextra',str(HERE/(stem+'.cpp')),'-o',str(work/stem)],check=True)
            for radius in args.radius:
                native=work/f'radius{radius}.input'
                abstract=json.loads(subprocess.check_output([str(work/'abstract_windows'),str(inp),str(native),str(radius)],text=True))
                if radius==6:
                    r,k,g=read_windows(native);reference=python_windows(rows,6)
                    assert sum(map(len,g))==len(reference)
                    assert all((q,p) in reference for q,v in enumerate(g) for p in v)
                prefix=work/f'census_r{radius}'
                summary=json.loads(subprocess.check_output([str(work/'exhaustive_fusions_lazy'),str(native),str(prefix)],text=True))
                expected=json.loads((PACKAGE/f'results/fusion_radius{radius}_summary.json').read_text())
                assert functional(summary)==functional(expected)
                for suffix in ('.tsv','_certificates.tsv'):
                    assert Path(str(prefix)+suffix).read_bytes()==(PACKAGE/f'results/fusion_radius{radius}{suffix}').read_bytes()
                if args.compare_eager:
                    ep=work/f'eager_r{radius}'
                    eager=json.loads(subprocess.check_output([str(work/'exhaustive_fusions'),str(native),str(ep)],text=True))
                    assert functional(eager)==functional(summary)
                    assert Path(str(ep)+'.tsv').read_bytes()==Path(str(prefix)+'.tsv').read_bytes()
                out['censuses'].append({'radius':radius,'abstract':abstract,'summary':summary,'saved_ledger_exact':True})
    if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()

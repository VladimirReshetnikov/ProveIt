#!/usr/bin/env python3
"""Offline release verification. Python 3.10+, standard library only.

Checks hashes, deterministic reconstruction, independent literal certificates,
and exact structural novelty. Does not claim a proof-assistant kernel build.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, subprocess, sys, tempfile
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise RuntimeError(message)

def load_module(name,path):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,help='optional JSON receipt outside the release tree')
    args=ap.parse_args()
    need(sys.version_info >= (3,10),'Python 3.10 or later required')
    need(not sys.flags.optimize,'Run without -O: the inherited exact matcher uses assertions')
    manifest=ROOT/'SHA256SUMS'
    need(manifest.exists(),'missing release integrity manifest')
    checked=0
    for line in manifest.read_text().splitlines():
        if not line:continue
        h,name=line.split('  ',1);p=ROOT/name
        need(p.is_file() and ROOT in p.resolve().parents,'invalid manifest path: '+name)
        need(hashlib.sha256(p.read_bytes()).hexdigest()==h,'hash mismatch: '+name)
        checked+=1
    print(f'Integrity: {checked} files PASS',flush=True)
    specs=json.loads((ROOT/'inputs/specifications.json').read_text())
    with tempfile.TemporaryDirectory(prefix='pa194-mf-verify-') as tmp:
        work=Path(tmp);env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
        for label,cmd in [
            ('build',[sys.executable,'-B',str(ROOT/'build.py'),'--output',str(work/'machines')]),
            ('independent',[sys.executable,'-B',str(ROOT/'verify_independent.py'),'--root',str(ROOT),'--output',str(work/'independent.json')])]:
            with (work/(label+'.log')).open('w') as log:
                p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,env=env,cwd=ROOT)
            if p.returncode:
                print((work/(label+'.log')).read_text(),file=sys.stderr)
                raise RuntimeError(label+' failed')
        frozen=sorted(p.relative_to(ROOT/'machines') for p in (ROOT/'machines').rglob('*') if p.is_file())
        rebuilt=sorted(p.relative_to(work/'machines') for p in (work/'machines').rglob('*') if p.is_file())
        need(frozen==rebuilt,'rebuild output file list differs')
        for p in frozen:need((ROOT/'machines'/p).read_bytes()==(work/'machines'/p).read_bytes(),'rebuild differs: '+str(p))
        audit=json.loads((work/'independent.json').read_text())
        need(audit['status']=='PASS','independent verification status')
        need(audit==json.loads((ROOT/'verification/independent.json').read_text()),'independent receipt differs')
        print(f'Reconstruction: {len(frozen)} byte-identical files PASS',flush=True)
        print('Independent literal rows, induction, complete startup and continuing synchronization: PASS',flush=True)

        nv=load_module('pa194_exact_novelty',ROOT/'comparison/novelty.py')
        corpus_dir=ROOT/'comparison/current_194_representatives'
        index=json.loads((corpus_dir/'index.json').read_text())
        need(len(index)==530,'current corpus size')
        corpus=[]
        for row in index:
            p=corpus_dir/row['representative']
            need(hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],'corpus representative hash')
            corpus.append(nv.parse(p)[0])
        a=corpus[0];n=len(a);permutation=[(137*q+19)%n for q in range(n)]
        need(len(set(permutation))==n,'positive control permutation')
        b=[None]*n
        for q,edges in enumerate(a):
            b[permutation[q]]=tuple((w,d,-1 if r<0 else permutation[r]) for w,d,r in edges)
        need(nv.isomorphic(a,b) is not None,'renamed positive control rejected')
        parent_matches=[];attempts=0
        for s in specs:
            parent=ROOT/'inputs'/s['parent']/'machine.tm'
            found=False
            for mirror in (False,True):
                for swap in (False,True):
                    pt=nv.parse(parent,mirror=mirror,swap=swap)[0]
                    if any(nv.isomorphic(pt,t) is not None for t in corpus):found=True;break
                if found:break
            need(found,'known parent missing from comparison corpus')
            parent_matches.append(s['parent'])
            child=ROOT/'machines'/s['name']/'machine.tm'
            for mirror in (False,True):
                for swap in (False,True):
                    ct=nv.parse(child,mirror=mirror,swap=swap)[0]
                    for t in corpus:
                        attempts+=1
                        need(nv.isomorphic(ct,t) is None,'child matches a supplied corpus table')
            print(s['name']+': distinct from all 530 inherited graphs under all four global symmetries PASS',flush=True)
        other=nv.parse(ROOT/'machines'/specs[1]['name']/'machine.tm')[0]
        for mirror in (False,True):
            for swap in (False,True):
                first=nv.parse(ROOT/'machines'/specs[0]['name']/'machine.tm',mirror=mirror,swap=swap)[0]
                need(nv.isomorphic(first,other) is None,'new children are isomorphic')
        result={'status':'PASS','manifest_files':checked,'reconstructed_files':len(frozen),
                'independent_audit':'PASS','corpus_graphs':len(corpus),'child_corpus_isomorphism_attempts':attempts,
                'renamed_positive_control':'PASS','known_parents_matched':parent_matches,'children_pairwise_distinct':True,
                'proof_boundary':'Finite exact certificates for the written relative iPRA proof. The absolute calibration is inherited and no new end-to-end Lean/Rocq theorem is claimed.'}
    if args.output:
        need(ROOT not in args.output.resolve().parents,'write the final receipt outside the immutable release tree')
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

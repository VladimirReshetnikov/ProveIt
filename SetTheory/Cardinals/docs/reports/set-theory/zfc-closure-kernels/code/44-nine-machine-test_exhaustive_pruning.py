#!/usr/bin/env python3
"""Differential check: C++ pruning versus independent full Python enumeration."""
import argparse, csv, itertools, json, random, subprocess, tempfile
from pathlib import Path
from synthesize_local_rows import abstract_windows, certificate, fused


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('executable',type=Path);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); rng=random.Random(20261017); fixtures=[]
    fixtures.append((3,{(0,0):(0,1,1),(0,1):(1,1,2),(1,0):(0,1,3),(1,1):(1,-1,3),(2,0):(0,1,3),(2,1):(1,-1,3)}))
    for n in (3,4,4,5):
        rows={(q,b):(rng.randrange(2),rng.choice((-1,1)),rng.randrange(n+1)) for q in range(n) for b in (0,1)}
        rows[n-1,1]=(1,1,n);fixtures.append((n,rows))
    results=[]
    with tempfile.TemporaryDirectory(prefix='fusion-regression-') as tmp:
        root=Path(tmp)
        for i,(n,rows) in enumerate(fixtures):
            radius=2;bound=8;windows=abstract_windows(rows,0,n,radius)
            windows={q:windows.get(q,[]) for q in range(n+1)}
            inp=root/f'case{i}.txt'; prefix=root/f'result{i}'
            with inp.open('w') as f:
                print(n,radius,bound,file=f)
                for q in range(n):
                    for b in (0,1):print(*rows[q,b],file=f)
                for q in range(n+1):print(len(windows[q]),*windows[q],file=f)
            cp=subprocess.run([str(args.executable.resolve()),str(inp),str(prefix)],capture_output=True,text=True,check=True)
            actual=set()
            with Path(str(prefix)+'_certificates.tsv').open() as f:
                reader=csv.reader(f,delimiter='\t');next(reader)
                actual={tuple(map(int,row)) for row in reader}
            expected=set();brute=0
            for p,q in itertools.combinations(range(n),2):
                actions=list(itertools.product((0,1),(-1,1),[t for t in range(n+1) if t!=p]))
                for z,o in itertools.product(actions,repeat=2):
                    brute+=1;new,start=fused(rows,0,p,q,z,o)
                    cert,fail=certificate(rows,new,p,q,windows,radius,bound,n)
                    if cert is not None:expected.add((p,q,*z,*o))
            if actual!=expected:
                raise RuntimeError((i,'differential mismatch',len(actual-expected),len(expected-actual)))
            results.append({'fixture':i,'states':n,'brute_force_recipes':brute,'certificates':len(actual),'cpp_summary':json.loads(cp.stdout)})
    if not any(x['certificates']>0 for x in results):raise RuntimeError('no positive coverage')
    report={'status':'PASS','fixtures':results,'total_brute_force_recipes':sum(x['brute_force_recipes'] for x in results),
      'scope':'Every finite certificate recipe from pruned C++ equals complete unpruned Python enumeration on five small fixtures, covering positive certificates, unknown-row pruning, start removal, cycles, and terminal outcomes.'}
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Check a candidate with exact source CFG and inherited symbolic tape contracts."""
from pathlib import Path
import argparse,importlib.util,json,sys,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'comparison'))
import compare_designs as comparison
from hashlib import sha256
BASE=Path(__file__).resolve().parent
SRC=BASE/'symbolic_runtime.py'
spec=importlib.util.spec_from_file_location('s',SRC);s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
s.ROOT=BASE/'reference'
original,labels=s.machine();oldsites,oldins=s.program()
OM={'CI':'inc','CD':'dec','CB':'breakTo','CC':'continueTo','CH':'halt'}

def table(p):
    rows={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
    return rows

def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path)
    ap.add_argument('--shorten',action='store_true');ap.add_argument('--startup',type=int,default=0)
    args=ap.parse_args();rows=table(args.directory/'candidate.native.tm')
    rawsites=json.loads((args.directory/'sites.json').read_text())
    sites=[(tuple(map(int,p)),OM[o],a)for p,o,a in rawsites]
    baseline_sites=comparison.flatten(comparison.lean_tree((BASE/'reference/PA196/Program.lean').read_bytes()))
    assert comparison.ordinal_graph(rawsites)==comparison.ordinal_graph(baseline_sites),'Complete source CFG mismatch'
    s.program=lambda:(sites,oldins)
    unchanged=all(rows.get((q,b))==original[q,b] for q in s.BOXSTATES for b in (0,1))
    assert unchanged,'Required box rows modified'
    if args.shorten:
        assert rows[23,0]==(0,False,34)
        rows[23,0]=(0,False,75)
        assert all(n!=34 for (q,b),(w,d,n) in rows.items()if q!=34)
        rows={k:v for k,v in rows.items()if k[0]!=34}
    start=time.monotonic();runtime=s.validate(rows,s.contracts())
    receipt={'shorten':args.shorten,'states':len(rows)//2,'runtime':runtime,
             'seconds':time.monotonic()-start,'box_rows_unchanged':unchanged,
             'scope':'Executable symbolic contracts, not a Lean kernel proof'}
    if args.startup:
        expected={-3}|{-2+i for i,b in enumerate(sites[25][0])if b}|{46}
        p=47
        for v in [0,0,0,0,0,0,2,0,0]+[1]*26:
            p+=1;expected.update(range(p,p+v+1));p+=v+1
        ones=set();q=74;head=0;seen=False
        for t in range(args.startup):
            if q==84 and head==-2 and ones==expected:
                seen=True;break
            if q==254:break
            w,d,q=rows[q,int(head in ones)]
            (ones.add if w else ones.discard)(head);head+=1 if d else -1
        receipt['startup']={'reached_exact_seed':seen,'steps':t,'bound':args.startup,'halted':q==254}
    (args.directory/('shortened_check.json' if args.shorten else'check.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

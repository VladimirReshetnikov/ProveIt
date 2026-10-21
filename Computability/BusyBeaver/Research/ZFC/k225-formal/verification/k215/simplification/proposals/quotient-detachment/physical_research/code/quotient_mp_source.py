#!/usr/bin/env python3
"""Concrete quotient-MP splice; exact source construction and finite corroboration.
An independent mathematical calibration is required; no binary machine is claimed.
"""
from pathlib import Path
from functools import lru_cache
import argparse,json,sys,hashlib

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--vendor',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();sys.path.insert(0,str(a.vendor));import source_language as s;import source_splice as sp
    raw=a.source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba';rows=json.loads(raw);old=s.tree(rows);a.output.mkdir(exist_ok=False)
    def run(t,regs,limit=2000000):
        ss=s.sites((t,('CH',None)));g=s.graph_intervals(ss);assert g==s.graph_arithmetic(ss)[0];regs=list(regs);pc=0
        for tick in range(limit):
            _,op,r=ss[pc];targets=g[pc][1]
            if op=='CH':return regs,tick
            if op=='CI':regs[r]+=1;pc=targets[0]
            elif op=='CD':positive=int(regs[r]>0);regs[r]-=positive;pc=targets[positive]
            else:pc=targets[0]
        raise RuntimeError('Finite test step limit exceeded')
    @lru_cache(None)
    def trees(x):
        if len(x)==1:return[x[0]]
        return[(u,v)for k in range(1,len(x))for u in trees(x[:k])for v in trees(x[k:])]
    variants=[];transfer=(('CD',7),(('CI',5),('CC',2)))
    for jump in(1,2,3):
        for div in trees((('CD',5),)*4+(('CI',6),('CC',jump))):
            if s.boundary(div)!=(0,0,False):continue
            good=True
            for h in range(100):
                regs=[3,4,5,6,7,h,0,9,11]
                try:got,_=run(div,regs,2000)
                except RuntimeError:good=False;break
                expected=regs[:];expected[5]=0;expected[6]=h//4
                if got!=expected:good=False;break
            if not good:continue
            replacement=(div,transfer);new=sp.apply_closed_splices(old,{(4652,4661):replacement});ss=s.sites(new);g=s.graph_intervals(ss);assert g==s.graph_arithmetic(ss)[0]
            idx=len(variants);out=a.output/f'v{idx:02d}';out.mkdir();payload=s.compact(ss);(out/'sites.json').write_bytes(payload)
            # The original and replacement span have the same nine leaves.
            assert len(ss)==len(rows)
            oldg=s.graph_intervals(rows)
            for i in range(len(rows)):
                if not 4652<=i<4661:assert ss[i][1:]==rows[i][1:] and g[i]==oldg[i]
            # Isolated replacement interface covers every residue and unequal side.
            probes=0
            for p in range(24):
                for h in range(100):
                    regs=[3,0,5,6,7,h,0,p,11];got,_=run(replacement,regs);expected=regs[:];expected[5]=p;expected[6]=h//4;expected[7]=0
                    assert got==expected;probes+=1
            data=dict(name=f'v{idx:02d}',jump=jump,division_tree=div,metrics=s.metrics(new),source_sha256=hashlib.sha256(payload).hexdigest(),splice=[4652,4661],macro_probes=probes,scope='Exact source splice, all outside ordinal edges unchanged, finite interface corroboration. No binary allocation, universal runtime, or new proof-assistant endpoint.')
            variants.append(data);(out/'receipt.json').write_text(json.dumps(data,indent=2)+'\n')
    (a.output/'summary.json').write_text(json.dumps(variants,indent=2)+'\n');print(json.dumps(variants,indent=2))
if __name__=='__main__':main()

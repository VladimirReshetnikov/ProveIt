#!/usr/bin/env python3
"""A concrete literal finite loader example; no full sandpile run is claimed."""
from pathlib import Path
import json,hashlib
from literal_loader import Circuit,tape_pair_loader,background_height,ca
ROOT=Path(__file__).resolve().parents[1]

def require(x,msg):
    if not x:raise AssertionError(msg)
def main():
    ell='00010111100110000110';r='10100111001100001011'
    tape={-i-1:int(v) for i,v in enumerate(ell)};tape.update({i+1:int(v) for i,v in enumerate(r)})
    q='A';p=0;T=0;trace=hashlib.sha256()
    while True:
        trace.update(json.dumps([T,q,p,sorted((x,v) for x,v in tape.items() if v)],separators=(',',':')).encode()+b'\n')
        nxt=ca.tm_step(tape,q,p)
        if nxt is None:break
        q,p=nxt;T+=1
        require(T<=1000,'example exceeded verified limit')
    require((T,p,q)==(75,-13,'J'),'wrong example halting configuration')
    c=Circuit();seeds=tape_pair_loader(ell,r,c);require(all(background_height(v,c)==5 for v in seeds),'bad seed')
    L=min(-3,-len(ell)-1);R=max(3,len(r)+1)
    b=ca.shutdown_bounds(L,R,T,p);H=b['first_all_lazy_time'];xmin=b['min_active_x'];xmax=b['max_active_x']
    prism=[[c.B*(xmin-2),c.B*(xmax+3)],[0,c.B*(H+1)],[0,336*c.M+52]]
    out=dict(ell=ell,r=r,serialized_binary='1'*len(ell)+'0'+ell+r,
      initial_state='A',initial_scanned_bit=0,halting_transitions=T,halting_head_position=p,
      final_state=q,final_scanned_bit=tape.get(p,0),trace_sha256=trace.hexdigest(),
      ca_extinction_and_geometry=b,periods=c.P,seed_count=len(seeds),
      seeds=[{'xyz':v,'added_chips':1,'background_height':5} for v in seeds],
      proved_active_prism=prism,
      claim='TM trace and literal seed coordinates checked; sandpile halting follows from the audited construction theorem. The enormous full sandpile was not simulated.')
    (ROOT/'compiler'/'worked_example.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='seeds'},indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent exact whole-tape startup checks of the three239 candidates."""
import argparse, hashlib, json
from pathlib import Path

def table(path):
    d = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,m,r = line.split()
        q,b,w,r = map(int,(q,b,w,r))
        assert (q,b) not in d and b in (0,1) and w in (0,1) and m in ('L','R')
        d[q,b] = (w,1 if m=='R' else -1,r)
    return d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    rows=table(a.table);qs={q for q,b in rows}
    assert len(qs)==239 and len(rows)==478 and set(rows)=={(q,b)for q in qs for b in (0,1)}
    assert {r for w,m,r in rows.values()}-qs=={254}
    wanted={-6,176};position=177
    for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
        position+=1;wanted.update(range(position,position+value+1));position+=value+1
    q,h,ones=95,0,set();visits={}
    for steps in range(3000001):
        if (q,h)==(96,-5) and ones==wanted:break
        if q==254 or steps==3000000:
            raise AssertionError(('no exact frame',q,h,steps,len(ones)))
        b=int(h in ones);visits[q,b]=visits.get((q,b),0)+1
        w,m,q=rows[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=m
    q,h,lo,dense=95,0,0,bytearray(1)
    for _ in range(steps):
        if h<lo:dense=bytearray(lo-h)+dense;lo=h
        if h>=lo+len(dense):dense.extend(bytearray(h-lo-len(dense)+1))
        w,m,q=rows[q,dense[h-lo]];dense[h-lo]=w;h+=m
    assert(q,h,{lo+i for i,v in enumerate(dense)if v})==(96,-5,wanted)
    record={'status':'EXACT_SPARSE_DENSE_BOOT_PASS','table':a.table.name,
        'sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'working_states':239,'rows':478,
        'steps':steps,'head':h,'dispatcher':q,'marker':-6,'header':176,'ones_count':len(wanted),
        'logical_registers':[3,0,0,0,3,0,0,0,0],'physical_registers':[0,0,0,3,0,0,3,0,0],
        'spares':[1]*167,'one_cells':sorted(wanted),'zero_exterior':True,
        'touched_rows':len(visits),'changed_row_visits':{f'{q}/{b}':visits.get((q,b),0)for q,b in[(80,0),(80,1),(91,1),(147,0)]},
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    a.output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items()if k not in('one_cells','spares')},indent=2))

if __name__=='__main__':main()

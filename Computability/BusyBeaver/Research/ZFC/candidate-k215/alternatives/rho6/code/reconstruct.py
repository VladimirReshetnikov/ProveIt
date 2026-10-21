#!/usr/bin/env python3
"""Rebuild both exact K215-R6 tables and sources, without an optimizer.

Python 3.10+ and the standard library. Output must be a fresh directory.
The two-row machine patch and four-operand source patch are literal data.
Reconstruction is distinct from the mathematical and quantified-runtime proofs.
"""
from pathlib import Path
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
COMMIT='75716498437bfc7291d5900cab2983a11fd54bac'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def table(path):
    out={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,bit,w,d,z=line.split();q,bit,w,z=map(int,(q,bit,w,z))
        need((q,bit)not in out and bit in(0,1)and w in(0,1)and d in('L','R'),'bad transition')
        out[q,bit]=(w,1 if d=='R'else-1,z)
    states={q for q,bit in out}
    need(starts==[0]and len(states)==215 and len(out)==430,'exact state convention')
    need(set(out)=={(q,bit)for q in states for bit in(0,1)},'partial table')
    need({z for w,d,z in out.values()}-states=={254},'unexpected halt')
    return out
def table_bytes(T):
    return ('#! start 0\n'+''.join(f'{q} {bit} {w} {"R"if d==1 else"L"} {z}\n'for(q,bit),(w,d,z)in sorted(T.items()))).encode('ascii')
def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode('ascii')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(__debug__ and not sys.flags.optimize,'Run without -O')
    manifest=json.loads((ROOT/'manifest.json').read_text());a.out.mkdir(parents=True,exist_ok=False);results=[]
    for name,item in manifest['candidates'].items():
        parent=ROOT/item['parent'];o=a.out/name;o.mkdir()
        for f,h in item['parent_hashes'].items():need(digest(parent/f)==h,'parent hash '+f)
        T=table(parent/'k215.native.tm');need(T[199,1]==(1,1,166)and T[206,0]==(0,1,186),'patch precondition')
        T[199,1]=(1,1,12);T[206,0]=(0,1,76)
        rows=json.loads((parent/'sites215.json').read_text());old=[r[:]for r in rows]
        for row in rows[888:1171]:
            if row[1]in('CI','CD')and row[2]in(3,5):row[2]=8-row[2]
        changed=[i for i,(x,y)in enumerate(zip(old,rows))if x!=y]
        need(changed==[959,964,1137,1142],'exact source patch')
        (o/'candidate.native.tm').write_bytes(table_bytes(T));(o/'sites.json').write_bytes(compact(rows))
        states=sorted({q for q,bit in T});ren={q:i for i,q in enumerate(states)};ren[254]=215
        D={(ren[q],bit):(w,d,ren[z])for(q,bit),(w,d,z)in T.items()}
        (o/'candidate.tm').write_bytes(table_bytes(D));reach={0};todo=[0]
        for q in todo:
            for bit in(0,1):
                z=T[q,bit][2]
                if z!=254 and z not in reach:reach.add(z);todo.append(z)
        need(len(reach)==215,'graph-reachable state count')
        cmap={'working_states':215,'rows':430,'graph_reachable_working_states':215,'native_start':0,'native_dispatcher':84,'native_halt':254,'dense_start':0,'dense_dispatcher':ren[84],'dense_halt':215,'native_to_canonical':ren,'native_sha256':digest(o/'candidate.native.tm'),'canonical_sha256':digest(o/'candidate.tm'),'source_sha256':digest(o/'sites.json'),'baseline_commit':COMMIT}
        (o/'canonicalization.json').write_text(json.dumps(cmap,indent=2,sort_keys=True)+'\n')
        hashes={f:digest(o/f)for f in item['output_hashes']}
        need(hashes==item['output_hashes'],'reconstructed artifact hashes')
        results.append({'candidate':name,'status':'EXACT_RECONSTRUCTION_PASS','states':215,'rows':430,'changed_source_ordinals':changed,'hashes':hashes})
    (a.out/'reconstruction.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()

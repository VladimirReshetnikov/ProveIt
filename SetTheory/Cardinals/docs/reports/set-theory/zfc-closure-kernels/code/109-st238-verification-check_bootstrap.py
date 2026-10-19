#!/usr/bin/env python3
"""Independent sparse/inherited and dense/canonical exact blank startup."""
from pathlib import Path
import argparse,hashlib,json,sys

STEPS=409835
OLD_SHA='069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
CANON_SHA='909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'

def require(ok,msg):
    if not ok:raise AssertionError(msg)

def sparse(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),d,int(t))
    q=95;h=0;ones=set();lo=hi=0
    for _ in range(STEPS):
        require(q!=254,'Premature sparse halt')
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1;lo=min(lo,h);hi=max(hi,h)
    return q,h,ones,(lo,hi)

def dense(path):
    # Independent flat transition representation and finite array tape.
    rows=[None]*476
    for line in path.read_text().splitlines():
        fields=line.split()
        if not fields or fields[0].startswith('#'):continue
        q=int(fields[0]);b=int(fields[1]);w=int(fields[2]);motion={'L':-1,'R':1}[fields[3]];n=int(fields[4])
        index=2*q+b;require(0<=index<476 and rows[index] is None,'Bad canonical row')
        rows[index]=(w,motion,n)
    require(all(x is not None for x in rows),'Missing canonical row')
    origin=STEPS+1;tape=bytearray(2*origin+1);q=0;h=origin
    for _ in range(STEPS):
        require(q!=238,'Premature dense halt')
        w,motion,n=rows[2*q+tape[h]];tape[h]=w;h+=motion;q=n
    return q,h-origin,{i-origin for i,b in enumerate(tape) if b}

def main():
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O/-OO.')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--old-labels',type=Path,required=True)
    ap.add_argument('--canonical',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    require(hashlib.sha256(a.old_labels.read_bytes()).hexdigest()==OLD_SHA,'Wrong old-label bytes')
    require(hashlib.sha256(a.canonical.read_bytes()).hexdigest()==CANON_SHA,'Wrong canonical bytes')
    q,h,ones,extent=sparse(a.old_labels);qc,hc,onesc=dense(a.canonical)
    require((q,h)==(96,-5) and (qc,hc)==(84,-5),'Wrong dispatcher or head')
    physical=[0,0,0,3,0,0,3,0,0];spares=[1]*167
    expected={-6,176};position=177
    for v in physical+spares:
        expected.update(range(position+1,position+v+2));position+=v+2
    require(ones==onesc==expected,'Complete startup tape mismatch')
    require(len(ones)==351,'Wrong support size')
    # Parse the observed blocks back to values, independently of their construction.
    observed=[];p=177;last=max(ones)
    while p<=last:
        require(p not in ones and p+1 in ones,'Malformed register block')
        j=p+1
        while j in ones:j+=1
        observed.append(j-p-2);p=j
    require(observed==physical+spares,'Decoded startup values disagree')
    permutation=(6,2,0,4,3,7,8,5,1)
    logical=[observed[j]for j in permutation]
    require(logical==[3,0,0,0,3,0,0,0,0],'Wrong logical seed')
    record={'status':'PASS_EXACT_SPARSE_DENSE_CANONICAL_BOOTSTRAP','steps':STEPS,'start_old':95,'start_canonical':0,'initial_head':0,'initial_tape':'all zero','final_state_old':q,'final_state_canonical':qc,'final_head':h,'marker':-6,'header':176,'header_distance':181,'extra_gap':117,'pc':'','physical_registers':physical,'logical_registers':logical,'logical_registers_above_8':0,'spare_values':spares,'one_count':351,'all_one_positions':sorted(ones),'all_other_cells_zero':True,'head_range':extent,'old_label_sha256':OLD_SHA,'canonical_sha256':CANON_SHA,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact finite initialization and complete tape identity. Infinite continuation is established by the separate unbounded runtime proof.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items()if k not in ('all_one_positions','spare_values')},indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent finite instruction audit of the exact prefix246 table.

Uses literal transitions and a separately parsed register-program tree. This is
finite evidence, not an unbounded machine proof or a Con(ZFC) theorem.
"""
from pathlib import Path
import argparse, hashlib, json, re, time

PHYSICAL = (6,2,0,4,3,7,8,5,1)

def read_table(path):
    table = {}
    for line in Path(path).read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t = line.split()
            key = int(q),int(b)
            assert key not in table
            table[key] = int(w),1 if d == 'R' else -1,int(t)
    return table

def program_sites(path):
    source = Path(path).read_text().split('Definition p254_tab',1)[1]
    source = source.split('[',1)[1].split('].',1)[0]
    token = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    tree = re.findall(r'\(('+token+r'),\s*('+token+r')\)',source)
    assert len(tree) == 6459
    def walk(n,prefix):
        for b,edge in enumerate(tree[n]):
            kind,*arg = edge.split()
            p = prefix+str(b)
            if kind == 'CN': yield from walk(int(arg[0]),p)
            else: yield p,kind,int(arg[0]) if arg else None
    sites = list(walk(0,''))
    assert len(sites) == 6460
    return sites

def paint(pc,header_distance,registers,spares,head):
    assert header_distance >= len(pc)
    ones={head-1,head+header_distance}
    ones.update(head+i for i,b in enumerate(pc) if b == '1')
    pos=head+header_distance+1
    for v in registers+spares:
        assert v >= 0
        ones.update(range(pos+1,pos+v+2))
        pos += v+2
    return ones

def add_one(path):
    bits=list(path)
    i=len(bits)-1
    while i >= 0 and bits[i] == '1':
        bits[i]='0'; i -= 1
    if i < 0: return None
    bits[i]='1'
    return ''.join(bits)

def remove_to(path,symbol,count):
    i=len(path)
    while count and i:
        i -= 1
        if path[i] == symbol: count -= 1
    return path[:i]

def expected(pc,kind,r,regs,spares,head,span):
    regs=regs.copy(); spares=spares.copy(); extra=0
    if kind == 'CI':
        regs[PHYSICAL[r]] += 1
        spares.append(1)
        nxt=add_one(pc)
    elif kind == 'CD':
        if regs[PHYSICAL[r]]:
            regs[PHYSICAL[r]] -= 1
            extra=1
            nxt=add_one(pc)
        else:
            nxt=add_one(remove_to(pc,'0',1))
    elif kind == 'CB': nxt=add_one(remove_to(pc,'0',r))
    elif kind == 'CC': nxt=remove_to(pc,'1',r)
    else: return None
    head -= nxt is None
    span += extra + (nxt is None)
    return head,paint(nxt or '',span,regs,spares,head),nxt or '',span,regs,spares

def run_case(table,pc,kind,r,regs,spares,head,span,fuel=100000):
    target=expected(pc,kind,r,regs,spares,head,span)
    one=paint(pc,span,regs,spares,head)
    state=96; visits=0
    used=set()
    for steps in range(1,fuel+1):
        key=state,int(head in one); used.add(key)
        w,d,state=table[key]
        if w: one.add(head)
        else: one.discard(head)
        head+=d
        if state == 254:
            assert kind == 'CH', (pc,kind,'unexpected halt',steps)
            return steps,used,visits
        if state == 96:
            if target is not None and head == target[0] and one == target[1]:
                return steps,used,visits
            visits += 1
            if visits > 15:
                raise AssertionError(dict(pc=pc,kind=kind,r=r,regs=regs,
                     spares=spares,span=span,head=head,expected_head=target[0] if target else None,
                     wrong_ones=sorted(one-(target[1] if target else set())),
                     missing_ones=sorted((target[1] if target else set())-one)))
    raise AssertionError(('fuel',pc,kind,r,regs,spares,head,span))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--program',type=Path,required=True)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results/literal-instructions.json')
    ap.add_argument('--quick',action='store_true')
    args=ap.parse_args()
    T=read_table(args.table)
    sites=program_sites(args.program)
    tested=0; total_steps=0; used=set(); maxsteps=0; maxvisits=0; began=time.monotonic()
    suites=[(0,0,[0]),(1,1,[1]),(3,7,[2,0,3]),(9,19,[0,1])]
    if args.quick:
        chosen=[]
        for kind in ('CI','CD','CB','CC','CH'):
            chosen.extend([s for s in sites if s[1]==kind][:20])
        sites=chosen
    for seed,slack,spares in suites:
        for pc,kind,r in sites:
            for positive in ((False,True) if kind=='CD' else (None,)):
                regs=[((i*3+seed)%7) for i in range(9)]
                if kind=='CD': regs[PHYSICAL[r]]=(seed+1) if positive else 0
                steps,seen,visits=run_case(T,pc,kind,r,regs,spares,head=-11+seed,span=40+slack)
                tested+=1; total_steps+=steps;used.update(seen)
                maxsteps=max(maxsteps,steps);maxvisits=max(maxvisits,visits)
        print('suite',seed,'cases',tested,'literal_steps',total_steps,flush=True)
    result=dict(status='PASS',finite_only=True,unbounded_proof=False,
        cases=tested,suites=suites,literal_steps=total_steps,maximum_case_steps=maxsteps,
        max_intermediate_dispatch_visits=maxvisits,transition_pairs_used=len(used),
        zero_rollback_positive_shift_increment_tail=True,
        used_97_read1=(97,1) in used,used_initializer_97_read0=(97,0) in used,
        seconds=time.monotonic()-began,
        source_hashes={str(args.program):hashlib.sha256(args.program.read_bytes()).hexdigest()},
        table_source=str(args.table),table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest())
    args.output.parent.mkdir(exist_ok=True,parents=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

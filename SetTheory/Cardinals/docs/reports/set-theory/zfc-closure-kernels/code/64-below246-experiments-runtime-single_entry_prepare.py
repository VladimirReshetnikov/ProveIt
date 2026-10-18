"""Prepare finite literal fixtures for predecessor-action state deletion search.

Only a screening procedure, never an unbounded equivalence certificate.
"""
from pathlib import Path
import os,sys,json,hashlib
HERE=Path(__file__).resolve().parent
BASE=Path(os.environ.get('ZFC246_BASE',str(HERE.parents[1]/'context246/zfc-context246')))
BASE_SHA256='303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
sys.path.insert(0,str(BASE/'code'))
import check_literal_instructions as c

def main():
    assert hashlib.sha256((BASE/'machine/zfc_prefix246_old.tm').read_bytes()).hexdigest()==BASE_SHA256
    T=c.read_table(BASE/'machine/zfc_prefix246_old.tm')
    states={q for q,b in T}
    incoming={q:[] for q in states}
    for k,(_,_,target) in T.items():
        if target in incoming and target!=k[0]:incoming[target].append(k)
    singles={q:ks[0] for q,ks in incoming.items() if len(ks)==1 and q not in (95,96)}
    frames=[];members={q:[] for q in singles};first={q:{} for q in singles}
    for pc,kind,r in c.program_sites(BASE/'sources/Prog254.v'):
        for positive in ((False,True) if kind=='CD' else (None,)):
            regs=[i%4 for i in range(9)]
            if kind=='CD':regs[c.PHYSICAL[r]]=2 if positive else 0
            one=c.paint(pc,48,regs,[0,1],0)
            assert all(-1 <= x <= 160 for x in one), 'C++ initial-support interval'
            target=c.expected(pc,kind,r,regs,[0,1],0,48)
            q=96;h=0;observed={};seen=set();initial=one.copy()
            for step in range(20000):
                key=q,int(h in one)
                if q in singles:observed.setdefault(q,set()).add(key[1])
                w,d,q=T[key]
                if w:one.add(h)
                else:one.discard(h)
                h+=d
                if q==254:
                    assert kind=='CH';break
                if q==96 and target is not None and h==target[0] and one==target[1]:break
            else:raise AssertionError((pc,kind,r,'baseline fuel'))
            assert target is None or (q,h,one)==(96,target[0],target[1])
            i=len(frames)
            frames.append(dict(pc=pc,kind=kind,r=r,positive=positive,initial=sorted(initial),
                target_head=target[0] if target else 0,target=sorted(target[1]) if target else [],steps=step+1))
            for state,bits in observed.items():
                members[state].append(i)
                for bit in bits:first[state].setdefault(bit,i)
    with (HERE/'single-entry-table.txt').open('w') as f:
        f.write(str(len(T))+'\n')
        for (q,b),(w,d,t) in sorted(T.items()):f.write(f'{q} {b} {w} {d} {t}\n')
    with (HERE/'single-entry-cases.txt').open('w') as f:
        f.write(str(len(frames))+'\n')
        for row in frames:
            a,b=row['initial'],row['target']
            f.write(' '.join(map(str,[int(row['kind']=='CH'),row['target_head'],len(a),*a,len(b),*b]))+'\n')
    with (HERE/'single-entry-members.txt').open('w') as f:
        f.write(str(len(singles))+'\n')
        for q,(p,b) in sorted(singles.items()):
            front=list(dict.fromkeys(first[q].values()))
            seq=front+[i for i in members[q] if i not in front]
            f.write(' '.join(map(str,[q,p,b,len(seq),*seq]))+'\n')
    result=dict(status='finite_fixture_corpus',baseline_sha256=BASE_SHA256,cases=len(frames),single_external_entry_states=len(singles),
        eligible_states=sorted(singles),all_have_both_read_bits=all(len(v)==2 for v in first.values()),
        one_fixture_covers_multiple_instruction_visits=True,all_baseline_cases_pass=True,
        rows=frames)
    (HERE/'single-entry-fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}))

if __name__=='__main__':main()

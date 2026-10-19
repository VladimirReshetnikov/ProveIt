#!/usr/bin/env python3
"""Guarded exact-step entry/restore identifications: 29->28 and 27->24."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import compare_biased_counter as C
import compare_biased_counter27 as D
import itertools,json,hashlib,random
OUT=Path(__file__).resolve().parent

def compile_compare(minimum_gap=2):
    if minimum_gap==2:
        T,s,P,ids,_,_=C.compile_compare();guardfile='compare_biased_counter_guards.json'
        aliases={'init':'restore_counter'}
    elif minimum_gap==3:
        T,s,P,ids=D.compile_compare();guardfile='compare_biased_counter27_results.json'
        aliases={'init':'restore_counter','failed_restore_left':'restore_left','restore_right':'failed_find_first'}
    else:raise ValueError(minimum_gap)
    guards=json.loads((OUT/guardfile).read_text())['valid_reads_by_name']
    dead={ids[q]:ids[k]for q,k in aliases.items()}
    def f(q):return dead.get(q,q)
    certificate=[]
    for name,keep in aliases.items():
        q,k=ids[name],ids[keep]
        for b in guards[name]:
            a,z=T[q,b],T[k,b]
            assert(a[0],a[1],f(a[2]))==(z[0],z[1],f(z[2])),(name,keep,b,a,z)
        certificate.append(dict(removed=name,retained=keep,removed_guard=guards[name],retained_guard=guards[keep],row_agreement=True))
    order=sorted({q for q,b in T}-set(dead));ren={q:i for i,q in enumerate(order)}|{p:len(order)+j for j,p in enumerate(P.values())}
    NT={(ren[q],b):(w,d,ren[f(t)])for(q,b),(w,d,t)in T.items()if q not in dead}
    NI={q:ren[k]for q,k in ids.items()if k not in dead};NP={name:ren[q]for name,q in P.items()};NG={q:guards[q]for q in NI}
    projection={q:ren[f(q)]for q in set(ids.values())|set(P.values())}
    return NT,ren[f(s)],NP,NI,NG,certificate,(T,s,P,projection)

def project_run(old,start,ports,projection,new,newstart,newports,ones,h,limit=10000000):
    one=set(ones);q=start;nq=newstart;steps=0
    while q not in ports.values():
        assert steps<limit;assert nq==projection[q]
        b=int(h in one);w,d,t=old[q,b];nw,nd,nt=new[nq,b]
        assert(nw,nd,nt)==(w,d,projection[t]),('projection',q,nq,b,steps)
        if w:one.add(h)
        else:one.discard(h)
        h+=1 if d=='R'else-1;q=t;nq=nt;steps+=1
    assert nq==projection[q]
    return steps

def main():
    results=[]
    for gapmin in (2,3):
        T,s,P,ids,G,certificate,(old,os,OP,projection)=compile_compare(gapmin)
        count=steps=0;rng=random.Random(24618+gapmin)
        fixtures=[]
        for a,b,i,k in itertools.product(range(6),range(6),range(3),range(1,5)):
            fixtures.append((a,b,[1,4],i,gapmin,0,k,()))
        for _ in range(500):
            a=rng.randrange(80);b=rng.randrange(80);other=[rng.randrange(1,20)for _ in range(rng.randrange(12))];i=rng.randrange(len(other)+1)
            gap=rng.randrange(gapmin,30);c=rng.randrange(-30,31);k=rng.randrange(1,5)
            _,_,end,_=C.frame(a,b,other,i,gap,c,k)
            ext=[c-j for j in range(2,12)if rng.randrange(2)]+[end+j for j in range(12)if rng.randrange(2)]
            fixtures.append((a,b,other,i,gap,c,k,ext))
        for a,b,other,i,gap,c,k,ext in fixtures:
            one,head,_,_=C.frame(a,b,other,i,gap,c,k);one|=set(ext)
            steps+=project_run(old,os,OP,projection,T,s,P,one,head)
            C.check(T,s,P,a,b,other,i,gap,c,k,ext);count+=1
        size=len(T)//2;text=f'# Minimum loaded-counter gap={gapmin}; ports '+json.dumps(P)+f'\n#! start {s}\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(T.items()))
        (OUT/f'compare_biased_counter_{size}.tm').write_text(text)
        result=dict(status='PASS',states=size,operational_states=size-1,minimum_loaded_counter_gap=gapmin,ports=P,start=s,names=ids,valid_reads_by_name=G,valid_reads_by_state={str(ids[q]):bs for q,bs in G.items()},fold_certificate=certificate,tests=count,literal_step_projections_checked=steps,table_sha256=hashlib.sha256(text.encode()).hexdigest(),scope='Guarded stepwise quotient of comparator29/27; inherits precise prepared-frame theorem and gap premise')
        (OUT/f'compare_biased_counter{size}_results.json').write_text(json.dumps(result,indent=2)+'\n');results.append({k:v for k,v in result.items()if k not in['names','valid_reads_by_name','valid_reads_by_state']})
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()

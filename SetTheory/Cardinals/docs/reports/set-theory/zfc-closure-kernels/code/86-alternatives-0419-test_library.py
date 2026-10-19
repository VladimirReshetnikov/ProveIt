#!/usr/bin/env python3
"""Parse emitted tables, check row projections, then exact paired traces.
The proof is local row projection plus reviewed inductive read guards; finite
traces are regressions and do not replace the guard proofs.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import sys,json,itertools,random,hashlib,argparse
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE))
import build_library as B
import retained_template_query as Q
import compare_biased_counter as K


def parse(path):
    result={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert(q,b)not in result
        result[q,b]=(w,d,t)
    return result

def audit(directory, *,reverse_guards=True):
    manifest=json.loads((directory/'manifest.json').read_text());opts=manifest.get('build_options',{})
    d=B.build_retained(reverse_guards=opts.get('reverse_guards',reverse_guards),selector_guards=opts.get('selector_guards',False),comparator27=opts.get('comparator27',False),include_compare=opts.get('include_compare',True),omit_unreachable_query=opts.get('omit_unreachable_query',False));r=manifest;T=parse(directory/'library.tm')
    assert d['domains']==r['domains'];assert len(T)==2*r['working_states']
    assert set(r['projection'])==set(d['domains'])|set(d['ports'])
    assert len(set(r['ports'].values()))==len(d['ports'])
    assert all(v>=r['working_states']for v in r['ports'].values())
    assert r['entries']=={k:r['projection'][q]for k,q in d['entries'].items()}
    projection=r['projection'];calls={k:0 for k in ('query','native','writer','compare')};maxsteps={k:0 for k in calls};total=0;used=set()
    for(q,b),(w,m,t)in d['rows'].items():
        if b in d['domains'][q]:assert T[projection[q],b]==(w,m,projection[t])
    def run(prefix,entry,ones,h):
        nonlocal total
        ones=set(ones);q=d['entries'][f'{prefix}.{entry}'];p=projection[q];n=0
        while q not in d['ports'] and q not in d['protected']:
            b=int(h in ones);assert b in d['domains'][q],(q,b,h)
            old=d['rows'][q,b];new=T[p,b];assert new==(old[0],old[1],projection[old[2]])
            used.add(q);w,m,q=old;p=new[2]
            if w:ones.add(h)
            else:ones.discard(h)
            h+=1 if m=='R'else-1;n+=1;assert n<2000000
        assert p==projection[q];calls[prefix]+=1;maxsteps[prefix]=max(maxsteps[prefix],n);total+=n
        return q,ones,h,n
    o=d['oracle']
    for rule in o['roots']:
        for path,expected,leaf in B.O.enumerate_leaf_paths(o,rule):
            bits=list(map(int,format(rule,'04b')))+path
            for c,extra in itertools.product((-19,0,17),(2,7)):
                initial,cursor,anchor,end,_=B.R.frame(bits,len(bits)+extra,c);initial[c-5]=1;initial[end+7]=1
                want=set(initial);want.add(cursor)
                for j,b in enumerate(reversed(bits)):
                    if b:want.add(c+j)
                    else:want.discard(c+j)
                want.add(c+len(bits))
                word=expected+list(map(int,format(leaf,'03b')))
                for j,b in enumerate(word):
                    p=c+len(path)-1-j
                    if b:want.add(p)
                    else:want.discard(p)
                q,t,h,n=run('query','start',initial,cursor)
                assert q==f'query:{133}' and t==want and h==c-4
    for old,new,c,left,right in itertools.product(range(1,5),range(1,5),(-9,0,11),range(4),range(4)):
        initial={c+i for i,b in enumerate(B.W.header(old))if b}
        initial|={c-1-j for j in range(2)if left>>j&1}|{c+7+j for j in range(2)if right>>j&1}
        want=(initial-set(range(c,c+7)))|{c+i for i,b in enumerate(B.W.header(new))if b}
        q,t,h,n=run('writer',f'mode_{new}',initial,c)
        assert q=='writer:11' and t==want and h==c+7 and n==7
    rng=random.Random(224246)
    for size in range(1,9):
        for trial in range(25):
            records=[(rng.randrange(4),rng.randrange(size),rng.randrange(size))for j in range(size)];s=rng.randrange(size)
            for branch,expected,c in itertools.product(range(2),range(2),(-7,13)):
                gap=records[s][1+branch]+2;anchor=c+gap+1;k=1+2*branch+expected
                tape={c}|set(range(anchor,anchor+k))|set(range(anchor+k+1,anchor+6));p=anchor+7;starts=[]
                for tag,left,right in records:
                    starts.append(p)
                    for length in(tag+1,left+3,right+3):tape.update(range(p,p+length));p+=length+1
                tape.remove(starts[s]);tape|={c-2,c-7,p+4}
                q,t,h,n=run('native','fetch',tape,starts[s]);good=(records[s][0]>>branch)&1==expected
                want=tape|{starts[s]}
                if good:want.discard(starts[records[s][1+branch]]);assert h==starts[records[s][1+branch]]
                assert(q=='native:68')==good and t==want
    for a,b,k,i,c in (itertools.product(range(9),range(9),range(1,5),range(3),(-11,7))if opts.get('include_compare',True)else []):
        initial,s,e,anchor=K.frame(a,b,[1,5],i,3 if opts.get('comparator27')else 2,c,k);initial|={c-2,e+3}
        want=(initial-set(range(c+1,c+a+1)))|{s}
        q,t,h,n=run('compare','start',initial,s)
        assert q==f'compare:{(27 if a==b else 28)if opts.get("comparator27")else(29 if a==b else 30)}' and t==want and h==c
    report={'status':'PASS','library_sha256':hashlib.sha256((directory/'library.tm').read_bytes()).hexdigest(),'working_states':len(r['classes']),'rows':len(T),'external_ports':r['ports'],'calls':calls,'total_calls':sum(calls.values()),'literal_step_comparisons':total,'max_steps':maxsteps,'original_working_roles_exercised':len(used),'guard_proof_basis':'Reviewed universal component invariants and exact sixteen-case finite writer contract; trace coverage is supplementary only.','all_allowed_rows_project':True,'no_global_machine_claim':True}
    (directory/'tests.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory',nargs='?',type=Path,default=HERE/'retained_guarded');a=p.parse_args();print(json.dumps(audit(a.directory),indent=2))

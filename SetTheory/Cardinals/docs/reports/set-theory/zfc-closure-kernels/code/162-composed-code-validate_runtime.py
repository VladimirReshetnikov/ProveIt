#!/usr/bin/env python3
"""Fresh whole-tape induction and blank initialization for an exact native table.

This is a wrapper for the inherited literal-row symbolic induction rules. It
stores large receipts compressed and never relies on an allocator or solver.
A finite startup is kept distinct from the all-natural primitive contracts.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, sys, time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'runtime'))
import symbolic_runtime as s

def require(b,m):
    if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_json(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def write_gz(p,x):
    with p.open('wb') as f:
        with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0,compresslevel=9) as g:
            g.write((json.dumps(x,separators=(',',':'))+'\n').encode())

def startup(T,limit=2000000):
    q=0;h=0;ones=set();trace=[];lowest=highest=0
    for tick in range(limit+1):
        if q==84 and ones and min(ones)==h-1:
            right=sorted(x for x in ones if x>h-1)
            if right and right[0]>=h+64:
                header=right[0];p=header+1;last=max(ones);v=[];good=True
                while p<=last:
                    if p in ones or p+1 not in ones:good=False;break
                    p+=1;n=0
                    while p in ones:n+=1;p+=1
                    v.append(n-1)
                if good and len(v)>=10 and v[0]==v[2]==v[7]==0:
                    return {'status':'SAFE_SOURCE_ROOT','steps':tick,'state':q,'head':h,
                        'header':header,'gap':header-h-64,'registers':[v[j]for j in s.r.PHY],
                        'spares':v[9:],'one_cells':sorted(ones),'head_range':[lowest,highest],'trace':trace}
        b=int(h in ones)
        require((q,b)in T,('Premature halt',tick,q,h))
        w,d,z=T[q,b]
        require(not(b==0 and z==q and(not ones or(d==1 and h>max(ones))or(d==-1 and h<min(ones)))),'Outward ray before source root')
        require(tick<limit,'Startup proof search bound exhausted')
        trace.append([q,h,b,w,d,z])
        if w:ones.add(h)
        else:ones.discard(h)
        q=z;h+=d;lowest=min(lowest,h);highest=max(highest,h)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('table',type=Path);ap.add_argument('source',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    a.output.mkdir(parents=True,exist_ok=True)
    T=s.r.table(a.table);sites=json.loads(a.source.read_text());states={q for q,b in T}
    require(len(T)==2*len(states) and all((q,b)in T for q in states for b in(0,1)), 'Total binary table')
    require({z for w,d,z in T.values()}-states=={254},'Unique external halt')
    from source_compare import inspect
    checked,graph,metrics=inspect(a.source);require(checked==sites,'Source parser agreement')
    require(metrics['maximum_depth']<=64,'Source exceeds represented address area')
    mp={int(k):int(v)for k,v in json.loads((ROOT/'inputs/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:
        if q not in mp:mp[q]=q+1000
    require(len({mp[q]for q in states|{254}})==len(states)+1,'Runtime relabeling must be injective')
    L={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
    st=startup(T)
    require((st['steps'],st['state'],st['head'],st['gap'],st['registers']) ==
        (95726,84,-8,1,[4,0,0,0,0,0,0,0,0]), 'Exact clean source seed')
    require(st['spares']==[1]*40, 'Exact spare list')
    require(len(st['one_cells'])==95, 'Exact whole-tape support size')
    st['seed_theorem']='Top, cache and every head of the zero stack are truth code 0; the candidate cutoff is 4.'
    write_gz(a.output/'startup.json.gz',st)
    summary={k:v for k,v in st.items()if k!='trace'}
    summary['table_sha256']=sha(a.table);write_json(a.output/'startup_summary.json',summary)
    print('STARTUP',st['steps'],st['state'],st['head'],st['registers'],flush=True)
    del st
    begun=time.monotonic();lemmas,blocks=s.prove_blocks(L);cases=[];covered=set();minimum=None
    for i,site in enumerate(sites):
        for positive in((False,True)if site[1]=='CD'else(False,)):
            try:ans=s.case(L,lemmas,site,positive)
            except Exception as e:
                write_json(a.output/'failure.json',{'status':'NOT_PROVED','site_index':i,'site':site,'positive':positive,'reason':str(e),'proved_cases':len(cases)})
                raise
            covered.update(ans['rows']);ans['rows']=sorted(ans['rows']);ans.pop('trace')
            cases.append({'site_index':i,'positive':positive,**ans})
            minimum=ans['duration'][0]if minimum is None else min(minimum,ans['duration'][0])
        if(i+1)%1000==0:print('PROVED',i+1,'sites',len(cases),'cases',round(time.monotonic()-begun,2),'seconds',flush=True)
    for block in blocks:
        for ev in block['trace']:
            if ev[0]in('literal','unary'):covered.add(tuple(ev[1][:2]))
    inv={mp[q]:q for q in states};native_rows={(inv[q],b)for q,b in covered}
    require(native_rows==set(T),'Every row must occur in the quantified proof')
    require(len(cases)==metrics['guarded_cases'],'Complete guarded-case inventory')
    write_gz(a.output/'runtime_cases.json.gz',cases)
    report={'status':'UNIVERSAL_MATHEMATICAL_PASS','table_sha256':sha(a.table),'source_sha256':sha(a.source),
        'checker_sha256':sha(s.__file__),'helper_sha256':sha(s.r.__file__),'wrapper_sha256':sha(__file__),
        'working_states':len(states),'transition_rows':len(T),'primitive_occurrences':len(sites),
        'expected_cases':metrics['guarded_cases'],'proved_cases':len(cases),
        'symbolic_steps':sum(x['symbolic_steps']for x in cases),'minimum_duration_constant':minimum,
        'all_transition_rows_covered':True,'blocks':blocks,'seconds':time.monotonic()-begun,
        'case_receipts_sha256':sha(a.output/'runtime_cases.json.gz'),
        'scope':'All natural primary register values under each decrement guard, arbitrary natural extra gap, an arbitrary nonempty finite spare list, and complete zero exterior. Literal rows, induction over unary runs, and structural induction over finite spare lists. No bound on actual run length or data.',
        'proof_assistant_status':'Ordinary mathematical symbolic certificate; no new Lean/Rocq kernel endpoint for these bytes.'}
    write_json(a.output/'runtime.json',report)
    print(json.dumps({k:v for k,v in report.items()if k!='blocks'},indent=2),flush=True)
if __name__=='__main__':main()

"""Paired randomized A/A/B/B experiments. No maintained-backend timing claim.

Every graph arm includes independently checked exact cycle products. Every
positive source probe includes source reconstruction and independent replay.
Every pipeline fallback uses the same small exponential cube reference.
"""
import argparse,datetime,hashlib,json,platform,random,statistics,sys,time
from pathlib import Path
from power_graph import Edge,infer
from graph_checker import verify
from saturation import probe_braid
from kh_oracle import rank_braid
from words import validate_braid
BASE=Path(__file__).resolve().parents[1]

def graph_cases():
    for r,B,kind in [(32,64,'unbalanced'),(128,64,'unbalanced'),(128,256,'unbalanced'),(512,64,'unbalanced'),(32,64,'balanced'),(128,64,'balanced'),(128,256,'balanced'),(128,64,'prime-divisible'),(128,16,'residue-collision')]:
        a=(1<<B)+3;b=(1<<B)+1
        if kind=='residue-collision': a=65538;b=1
        if kind=='prime-divisible': a*=65537;b*=65537
        edges=[]
        for j in range(r):
            A,Bb=(b,a) if kind=='balanced' and j>=r//2 else (a,b)
            edges.append(Edge(j+1,(j+1)%r+1,A,Bb,False))
        yield f'{kind}-r{r}-b{B}',list(range(1,r+1)),edges,{'kind':kind,'vertices':r,'nominal_bits':B}

def braid_cases():
    cases=[('circle',1,[]),('one-crossing',2,[1]),('trefoil',2,[1]*3),('T25',2,[1]*5),('circle-three',3,[1,2]),('mixed-circle',3,[1,2,1,-2]),('figure-eight',3,[1,-2]*2),('T34',3,[1,2]*4),('circle-four',4,[1,2,3]),('sleeve-seven',4,[1,2,3,1,-1,2,-2]),('alternating-eight',3,[1,-2]*4),('five-strand-circle',5,[1,2,3,4])]
    for name,n,b in cases: validate_braid(n,b);yield name,n,b

def summarize(rows,base,variant):
    paired={}
    for row in rows: paired.setdefault(row['round'],{})[row['arm']]=row['seconds']
    return statistics.median(t[base]/t[variant] for t in paired.values())

def execute(case_name,call,arms,rng,repeats):
    samples=[]; warm=[]
    order=list(arms);rng.shuffle(order)
    for arm in order:
        t=time.perf_counter();res=call(arm);warm.append({'arm':arm,'seconds':time.perf_counter()-t,'result':res})
    for rep in range(repeats):
        order=list(arms);rng.shuffle(order)
        for seq,arm in enumerate(order):
            t=time.perf_counter();res=call(arm);samples.append({'round':rep,'order':seq,'arm':arm,'seconds':time.perf_counter()-t,'result':res})
    return samples,warm

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default=str(BASE/'data'/'benchmark.json'));p.add_argument('--repeats',type=int,default=7);args=p.parse_args()
    if args.repeats<1:raise ValueError('positive repeat count required')
    rng=random.Random(10082026);start=time.perf_counter();hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((BASE/'code').glob('*.py'))};graphs=[];braids=[]
    for name,vs,es,meta in graph_cases():
        def call(arm):
            out=infer(vs,es,modular=arm.startswith('modular'));proof={k:out[k] for k in ('killed','witnesses')};assert verify(vs,es,proof)
            return {'killed':len(out['killed']),'witnesses':len(out['witnesses']),**out['stats']}
        samples,warm=execute(name,call,['rational-A','rational-B','modular-A','modular-B'],rng,args.repeats)
        med={arm:statistics.median(s['seconds'] for s in samples if s['arm']==arm) for arm in ['rational-A','rational-B','modular-A','modular-B']}
        graphs.append({'name':name,**meta,'samples':samples,'warmups':warm,'medians':med,'paired_rational_over_modular':summarize(samples,'rational-A','modular-A'),'rational_AA':summarize(samples,'rational-A','rational-B'),'modular_AA':summarize(samples,'modular-A','modular-B')})
    for name,n,b in braid_cases():
        expected=rank_braid(n,b)['rank']==1
        def call(arm):
            if arm.startswith('probe'):
                out=probe_braid(n,b)
                if out['status']=='UNKNOT':
                    assert expected;return {'unknot':True,'via':'probe','rounds':len(out['certificate']['rounds'])}
            kh=rank_braid(n,b);assert (kh['rank']==1)==expected
            return {'unknot':expected,'via':'cube','rank':kh['rank'],'generators':kh['generators']}
        samples,warm=execute(name,call,['cube-A','cube-B','probe-A','probe-B'],rng,args.repeats)
        med={arm:statistics.median(s['seconds'] for s in samples if s['arm']==arm) for arm in ['cube-A','cube-B','probe-A','probe-B']}
        braids.append({'name':name,'strands':n,'braid':b,'unknot':expected,'samples':samples,'warmups':warm,'medians':med,'paired_cube_over_probe':summarize(samples,'cube-A','probe-A'),'cube_AA':summarize(samples,'cube-A','cube-B'),'probe_AA':summarize(samples,'probe-A','probe-B')})
    after={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((BASE/'code').glob('*.py'))};assert hashes==after
    result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'seconds':time.perf_counter()-start,'repeats':args.repeats,'source_sha256':hashes,'graphs':graphs,'braids':braids,'measured_calls':args.repeats*4*(len(graphs)+len(braids)),'warmup_calls':4*(len(graphs)+len(braids))}
    target=Path(args.output);target.parent.mkdir(parents=True,exist_ok=True);target.write_text(json.dumps(result,indent=2)+'\n')
    print('seconds',result['seconds'],'calls',result['measured_calls'])
    for row in graphs: print(row['name'],row['medians'],'ratio',row['paired_rational_over_modular'],'AA',row['rational_AA'],row['modular_AA'])
    for row in braids: print(row['name'],row['medians'],'ratio',row['paired_cube_over_probe'],'AA',row['cube_AA'],row['probe_AA'])
if __name__=='__main__': main()

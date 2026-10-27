import gc,json,platform,random,statistics,sys,time
from packet_extraction import Ring,forward_gray,centered_half_gray,projective_odd_root,lift_cube_root

def main():
    rng=random.Random(202610270214)
    specs=[('cube_twos12_e2',6,Ring(64,(1,1),1),(0,1)),
           ('cube_twos16_e2V2',8,Ring(64,(1,1),2),(0,1,0,0)),
           ('cube_twos14_e4',7,Ring(64,(1,1,0,0),1),(0,1,1,0)),
           ('cube_twos12_e4V2',6,Ring(256,(1,1,0,0),2),(0,1,1,0,0,0,0,0))]
    results=[]
    for name,k,ring,residue in specs:
        beta=[2]*k;R=2*k
        root=lift_cube_root(residue,ring)
        rows=[[tuple(rng.getrandbits(ring.precision) for _ in range(ring.dimension)) for _ in beta] for _ in range(R)]
        methods={'forward_gray':lambda stats=None:forward_gray(rows,beta,ring,stats),
                 'centered_half_gray':lambda stats=None:centered_half_gray(rows,beta,ring,stats),
                 'projective_cube':lambda stats=None:projective_odd_root(rows,beta,ring,root,3,stats),
                 'projective_cube_with_root_lift':lambda stats=None:projective_odd_root(rows,beta,ring,lift_cube_root(residue,ring),3,stats)}
        expected=None;data={}
        for key,fn in methods.items():
            stats={};result=fn(stats)
            if expected is not None and result!=expected:raise AssertionError((name,key))
            expected=result;data[key]={'seconds':[],'stats':stats}
        for rep in range(3):
            order=list(methods) if rep%2==0 else list(reversed(methods))
            for key in order:
                gc.collect();start=time.perf_counter();result=methods[key]();sec=time.perf_counter()-start
                if result!=expected:raise AssertionError('timed mismatch')
                data[key]['seconds'].append(sec)
        for d in data.values():d['median_seconds']=statistics.median(d['seconds'])
        t=data['projective_cube']['median_seconds']
        entry=dict(case=name,R=R,beta=beta,p=ring.precision,f=ring.f,ell=ring.ell,root=root,
                   methods=data,speedup_vs_half=data['centered_half_gray']['median_seconds']/t,
                   speedup_vs_forward=data['forward_gray']['median_seconds']/t)
        results.append(entry);print(json.dumps({'case':name,'forward':data['forward_gray']['median_seconds'],'half':data['centered_half_gray']['median_seconds'],'cube':t}),file=sys.stderr,flush=True)
    return dict(status='PASS',scope='same-ring exact coefficient microbenchmark, all exponents two; not full solver',
                python=sys.version,platform=platform.platform(),seed=202610270214,repeats=3,warmups=1,
                root_materialization_timed={'projective_cube':False,'projective_cube_with_root_lift':True},residue_root_search_timed=False,root_validation_and_all_extraction_setup_timed=True,results=results)
if __name__=='__main__':print(json.dumps(main(),indent=2,sort_keys=True))

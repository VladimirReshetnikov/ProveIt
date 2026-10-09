"""Follow-up on multiplicative-order aliasing in the fixed-prime sieve.

The original benchmark is retained unchanged. New cycle lengths bracket
multiples of 32 because 2 has order 32 modulo 65537. This tests the diagnosed
mechanism, not a representative distribution of knot presentations.
"""
import argparse,datetime,hashlib,json,platform,random,statistics,sys,time
from pathlib import Path
from benchmark import execute,summarize
from power_graph import Edge,infer
from graph_checker import verify
from paired_power import family,verify_pair
BASE=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default=str(BASE/'data'/'sieve_followup.json'));args=p.parse_args()
    rng=random.Random(202610082);start=time.perf_counter();records=[]
    hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((BASE/'code').glob('*.py'))}
    for r,B in [(31,64),(32,64),(33,64),(127,256),(128,256),(129,256),(511,64),(512,64),(513,64)]:
        vs=list(range(1,r+1));es=[Edge(i+1,(i+1)%r+1,(1<<B)+3,(1<<B)+1) for i in range(r)]
        def call(arm):
            out=infer(vs,es,modular=arm.startswith('modular'));assert out['killed']==vs;assert verify(vs,es,{k:out[k] for k in ('killed','witnesses')});return out['stats']
        samples,warm=execute(str((r,B)),call,['rational-A','rational-B','modular-A','modular-B'],rng,9)
        records.append({'vertices':r,'nominal_bits':B,'ratio':summarize(samples,'rational-A','modular-A'),'rational_AA':summarize(samples,'rational-A','rational-B'),'modular_AA':summarize(samples,'modular-A','modular-B'),'medians':{a:statistics.median(z['seconds'] for z in samples if z['arm']==a) for a in ['rational-A','rational-B','modular-A','modular-B']},'samples':samples,'warmups':warm})
    capacities=[]
    for pairs,bits in [(1,64),(16,256),(128,1024),(128,16384)]:
        times=[]
        for rep in range(7):
            t=time.perf_counter();rows,proofs=family(pairs,bits)
            assert all(verify_pair(rows,c) for c in proofs)
            es=[Edge(s,t,a,b,True) for s,t,a,b in rows];out=infer(list(range(1,2*pairs+2)),es)
            assert out['killed']==list(range(1,2*pairs+1));assert verify(list(range(1,2*pairs+2)),es,{k:out[k] for k in ('killed','witnesses')})
            times.append(time.perf_counter()-t)
        capacities.append({'pairs':pairs,'bits_parameter':bits,'coefficient_bits':bits+1,'expanded_relator_letters_formula':f'{pairs} * (4 * 2^{bits} + 4)','generator_count':2*pairs+1,'killed':2*pairs,'seconds':times,'median':statistics.median(times)})
    assert hashes=={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((BASE/'code').glob('*.py'))}
    result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'seconds':time.perf_counter()-start,'source_sha256':hashes,'cycle_cases':records,'capacity_cases':capacities,'measured_cycle_calls':324,'cycle_warmups':36,'capacity_calls':28}
    out=Path(args.output);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print('elapsed',result['seconds'])
    for r in records: print(r['vertices'],r['nominal_bits'],'ratio',r['ratio'],'AA',r['rational_AA'],r['modular_AA'])
    for c in capacities:print('capacity',c['pairs'],c['bits_parameter'],c['median'])
if __name__=='__main__':main()

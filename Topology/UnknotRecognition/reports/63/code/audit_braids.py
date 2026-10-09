"""Exhaustive short-braid and seeded longer-braid cross-oracle audit."""
import argparse,datetime,hashlib,itertools,json,platform,random,sys,time
from collections import Counter
from pathlib import Path
from words import validate_braid,braid_presentation,difference_basis,cyclic_reduce
from saturation import probe_braid
from source_checker import verify_braid
from kh_oracle import rank_braid
BASE=Path(__file__).resolve().parents[1]
def corpus():
    yield 'circle',1,[]
    for length in [1,3,5,7]:
        for b in itertools.product([-1,1],repeat=length): yield 'two-strand-exhaustive',2,list(b)
    for length in [2,4,6]:
        for b in itertools.product([-2,-1,1,2],repeat=length):
            try: validate_braid(3,b)
            except ValueError: continue
            yield 'three-strand-exhaustive',3,list(b)
    rng=random.Random(202610081)
    for n,target in [(4,100),(5,100)]:
        done=0
        while done<target:
            length=rng.choice([3,5,7,9]) if n==4 else rng.choice([4,6,8])
            b=[rng.randrange(1,n)*rng.choice([-1,1]) for _ in range(length)]
            try: validate_braid(n,b)
            except ValueError: continue
            done+=1; yield 'seeded-four-five',n,b

def power_only(n,b):
    roots=difference_basis(braid_presentation(n,b),n);alive=set(range(1,n+1));rounds=0
    while True:
        dead={abs(w[0]) for w in roots if w and len(set(w))==1}
        if not dead:break
        alive-=dead;roots=[cyclic_reduce(x for x in w if abs(x) not in dead) for w in roots];rounds+=1
    return sorted(alive),rounds

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default=str(BASE/'data'/'braid_audit.json'));args=p.parse_args()
    start=time.perf_counter(); rows=[]; cohorts={}; example={}; source_hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((BASE/'code').glob('*.py'))}
    for idx,(cohort,n,b) in enumerate(corpus()):
        kh=rank_braid(n,b); result=probe_braid(n,b); positive=result['status']=='UNKNOT'
        power_alive,power_rounds=power_only(n,b)
        if positive:
            assert kh['rank']==1 and verify_braid(n,b,result['certificate'])
        lengths=[]; modes=[]; nonpower=0; killed=0
        for r in result.get('certificate',{}).get('rounds',[]):
            killed+=len(r['graph']['killed'])
            for w in r['graph']['witnesses']:
                lengths.append(len(w['walk']));modes.append(w['mode'])
                nonpower+=any(r['donors'][j]['kind']!='power' for j,d in w['walk'])
        row={'id':idx,'cohort':cohort,'strands':n,'braid':b,'rank':kh['rank'],'cube_generators':kh['generators'],'probe':result['status'],'rounds':len(result.get('certificate',{}).get('rounds',[])),'killed':killed,'witness_lengths':lengths,'witness_modes':modes,'nonpower_witnesses':nonpower,'power_only_remaining':power_alive,'power_only_rounds':power_rounds,'counts':result.get('counts',[])}
        rows.append(row); c=cohorts.setdefault(cohort,Counter());c['cases']+=1;c['unknots']+=kh['rank']==1;c['positive_probe']+=positive;c['nonpower_positive']+=positive and nonpower>0;c['multiround_positive']+=positive and row['rounds']>1;c['resource_limits']+=result['status']=='RESOURCE_LIMIT';c['positive_beyond_power_only']+=positive and power_alive!=[n];c['different_remaining_set']+=([n] if positive else result.get('remaining_generators'))!=power_alive
        if positive and nonpower and 'nonpower_positive' not in example: example['nonpower_positive']={'source':row,'certificate':result['certificate']}
        if positive and row['rounds']>1 and 'multiround_positive' not in example: example['multiround_positive']={'source':row,'certificate':result['certificate']}
        if not positive and kh['rank']==1 and 'missed_unknot' not in example: example['missed_unknot']={'source':row,'result':result}
    end_hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((BASE/'code').glob('*.py'))};assert source_hashes==end_hashes
    out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'seconds':time.perf_counter()-start,'cases':len(rows),'cohorts':cohorts,'source_sha256':source_hashes,'examples':example,'rows':rows}
    target=Path(args.output);target.parent.mkdir(parents=True,exist_ok=True);target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['seconds','cases','cohorts','examples']},indent=2))
if __name__=='__main__': main()

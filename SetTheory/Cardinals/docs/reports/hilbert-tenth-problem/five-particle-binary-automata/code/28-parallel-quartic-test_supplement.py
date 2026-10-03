"""Extra paid-network boundary and simultaneous-lane checks; no asserts."""
import json,collections,time,gc,hashlib
from pathlib import Path
from compiler import Certificate,ev
from sparse_parallel import SparseParallelCompiler
ROOT=Path(__file__).resolve().parent;start=time.time();counts=collections.Counter();details=[]
import argparse
_parser_args=argparse.ArgumentParser(description=__doc__)
_parser_args.add_argument('--output-dir',type=Path,default=ROOT)
OUT=_parser_args.parse_args().output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
f=json.loads((ROOT/'fixtures.json').read_text());sources={k:v['data']for k,v in f['sources'].items()}
def check(ok,*why):
    if not ok:raise RuntimeError(why)
def exercise(cert,case,inverse,ref):
    y=case['inverse_output'if inverse else 'forward_output'];values=cert.witness(case['input'],y)
    snapshot=set(case['input'])
    for name,raw,lanes,selected,Y in cert.traces:
        b=getattr(ref,name);got=sorted((ev(lane['ID'],values),ev(lane['u'],values))for lane,s in zip(lanes,selected)if ev(s,values))
        check(got==sorted(b.eligible(snapshot)),'selected keys',case['id'],name,inverse,got)
        count_live=sum(ev(s,values)for s in selected);counts['max_simultaneous_selected']=max(counts['max_simultaneous_selected'],count_live)
        for lane in lanes:
            if not ev(lane['present'],values):
                check(all(ev(lane[k],values)==0 for k in ('ID','u','arity')),'padding scalar')
                check(all(ev(v,values)==0 for k in ('old','new')for v in lane[k]),'padding payload')
                counts['empty_lane_payload_checks']+=1
        snapshot=set(b.apply(snapshot));check(sorted(snapshot)==[ev(v,values)for v in Y],'output')
        counts['block_equalities']+=1
    counts['full_endpoint_equalities']+=1
    return values
cases=[x for x in f['cases']if x['mass']==4]
guard5=[x for x in f['cases']if x['source']=='guarded_direct'and x['mass']==5 and x['blocks']['E']['eligible']]
cases += guard5[:4]
groups=collections.defaultdict(list)
for x in cases:groups[(x['source'],x['mass'])].append(x)
for(source,n),group in sorted(groups.items()):
    ref=SparseParallelCompiler(sources[source])
    for inverse in(False,True):
        cert=Certificate(sources[source],n,1,inverse)
        for case in group:
            values=exercise(cert,case,inverse,ref)
            if case['id']=='isolation_E_+1'and not inverse:
                details.append(dict(case=case['id'],input=case['input'],target=case['forward_output'],ledger=cert.ledger()))
        del cert,values;gc.collect();print('case group passed',source,n,inverse,len(group),flush=True)
# Bounded horizon subset: all n<=3 oracle cases; mass-5 only T<=1.
# Larger mass-5 horizons were deliberately not retained in this bounded run.
for case in f['horizon_cases']:
    if case['mass']>3 and case['horizon']>1:continue
    cert=Certificate(sources[case['source']],case['mass'],case['horizon'],case['inverse'])
    values=cert.witness(case['input'],case['accepted_target'])
    bad=cert.witness(case['input'],case['rejected_target'],check=False)
    check(cert.circuit.score(bad)>0,'horizon wrong target');counts['horizon_accepted']+=1;counts['horizon_rejected']+=1
    del cert;gc.collect()
print('horizon checks passed',counts['horizon_accepted'],flush=True)
# A single unchanged circuit handles arbitrarily large signed translations.
for n,x in ((2,[0,5]),(3,[-18,-13,0])):
    ref=SparseParallelCompiler(sources['increment_right'])
    for inverse in(False,True):
        cert=Certificate(sources['increment_right'],n,1,inverse);base=sorted(ref.step(set(x),inverse=inverse))
        for shift in(-10**80,-1000001,0,1000001,10**80):
            shifted=[z+shift for z in x];target=[z+shift for z in base]
            values=cert.witness(shifted,target);counts['large_translation_acceptances']+=1
            if abs(shift)==10**80:details.append(dict(n=n,inverse=inverse,shift_sign=1 if shift>0 else -1,max_natural_witness_bits=max(v.bit_length()for v in values[cert.circuit.input_count:])))
        del cert;gc.collect()
# Exact paid arity formulas, independent of T values.
for n in(0,1,2,3):
    base=Certificate(sources['increment_right'],n,1).ledger()
    per_step=sum(b['delta']['witnesses']for b in base['blocks'])
    domain=4*max(n-1,0);Q=5*n-2 if n else 0
    for T in(0,1,2,3):
        cert=Certificate(sources['increment_right'],n,T);ledger=cert.ledger()['circuit']
        check(ledger['witnesses']==domain+T*per_step,'arity formula',n,T)
        check(ledger.get('Q',0)==Q and ledger['residuals']==ledger['witnesses']+Q,'residual formula',n,T)
        counts['arity_formula_checks']+=1;del cert;gc.collect()
check(counts['max_simultaneous_selected']>=2,'missing simultaneous-lane exercise')
r=dict(status='PASS',optimized=not __debug__,seconds=time.time()-start,counts=dict(counts),details=details,fixture_sha256=hashlib.sha256((ROOT/'fixtures.json').read_bytes()).hexdigest())
(OUT/('supplement-receipt-optimized.json'if not __debug__ else 'supplement-receipt.json')).write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:r[k]for k in('status','counts','seconds')},sort_keys=True))

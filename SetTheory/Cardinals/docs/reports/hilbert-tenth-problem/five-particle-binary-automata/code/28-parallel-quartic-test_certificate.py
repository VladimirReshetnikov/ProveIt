"""Bounded differential/binding checks, explicit exceptions survive python -O."""
from pathlib import Path
import gc,hashlib,itertools,json,sys,time,collections,random
from compiler import Certificate,Emitter,Circuit,const,var,sub,ev,natural_pairs,FROZEN,_parser
sys.path.insert(0,str(FROZEN))
from sparse_parallel import SparseParallelCompiler
ROOT=Path(__file__).resolve().parent
import argparse
_parser_args=argparse.ArgumentParser(description=__doc__)
_parser_args.add_argument('--output-dir',type=Path,default=ROOT)
OUT=_parser_args.parse_args().output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
counts=collections.Counter();ledgers={};start=time.time()
def check(b,*msg):
    if not b:raise RuntimeError(msg)
def reject(fn):
    try:fn()
    except ValueError:counts['rejections']+=1;return
    raise RuntimeError('expected rejection')
def raw_values(raw,values):
    records=[(ev(r['ID'],values),ev(r['u'],values),r['label'])for r in raw if ev(r['raw'],values)]
    check(len(records)==len(set((a,b)for a,b,_ in records)),'duplicate raw keys',records)
    return sorted(records)
def selected_values(lanes,selected,values):
    return sorted((ev(r['ID'],values),ev(r['u'],values))for r,f in zip(lanes,selected)if ev(f,values))
def mutations(c,values,label,all_witness=True):
    byvar=[[]for _ in values]
    for i,row in enumerate(c.rows):
        for v in set(k for m in row for k in m):byvar[v].append(i)
    indices=list(range(c.input_count,len(values)))
    if not all_witness:indices=random.Random(177).sample(indices,min(1000,len(indices)))
    for j in indices:
        original=values[j]
        for z in (original+1,)+( (original-1,) if original else ()):
            values[j]=z
            check(any(ev(c.rows[i],values)!=0 for i in byvar[j]),'witness mutation escaped',label,j,original,z)
            counts['witness_coordinate_mutations']+=1
        values[j]=original
    del byvar
f=json.loads((ROOT/'fixtures.json').read_text());sources={k:v['data']for k,v in f['sources'].items()};cases=list(f['cases'])
for domain in f['exhaustive_domains']:
    for i,case in enumerate(domain['cases']):cases.append(dict(case,source=domain['source'],id=domain['id']+'_'+str(i),exhaustive=domain['id']))
# Raw maps: all fixture snapshots, including multi-hit detector guards up to n=7.
groups=collections.defaultdict(list)
for case in cases:groups[(case['source'],case['mass'])].append(case)
for (source,n),group in sorted(groups.items()):
    m=_parser.compile_lazy_source(sources[source]);c=Circuit([str(i)for i in range(2*n)]);X=[sub(var(2*i),var(2*i+1))for i in range(n)]
    e=Emitter(c,m);raw={name:e.raw(X,name)for name in ('E','P')}
    for case in group:
        values=c.evaluate(natural_pairs(case['input']))
        for name in ('E','P'):
            got=raw_values(raw[name],values);want=[tuple(v)for v in case['blocks'][name]['raw']]
            check(got==want,'raw differential',case['id'],name,got,want);counts['raw_map_equalities']+=1
    del c,e,raw;gc.collect()
print('raw maps passed',counts['raw_map_equalities'],flush=True)
# Full arithmetic compilation through both blocks in both orders.
full_cases=[x for x in cases if x['mass']<=3 or x['id']=='malformed_cascade']
full_groups=collections.defaultdict(list)
for case in full_cases:full_groups[(case['source'],case['mass'])].append(case)
for (source,n),group in sorted(full_groups.items()):
    ref=SparseParallelCompiler(sources[source])
    for inverse in (False,True):
        cert=Certificate(sources[source],n,1,inverse);c=cert.circuit
        ledgers[f'{source}_n{n}_T1_inverse{inverse}']=cert.ledger()
        for case in group:
            y=case['inverse_output' if inverse else 'forward_output'];values=cert.witness(case['input'],y)
            check([ev(v,values)for v in cert.output]==y,'whole output',case['id'],inverse)
            snapshot=set(case['input'])
            for name,raw,lanes,selected,Y in cert.traces:
                block=getattr(ref,name)
                got=raw_values(raw,values);want=sorted((i,u,label)for(i,u),label in block.candidates(snapshot).items())
                check(got==want,'trace raw',case['id'],inverse,name)
                active=selected_values(lanes,selected,values)
                check(active==sorted(block.eligible(snapshot)),'selected keys',case['id'],inverse,name,active)
                snapshot=set(block.apply(snapshot))
                check(tuple(ev(v,values)for v in Y)==tuple(sorted(snapshot)),'block output',case['id'],inverse,name)
                counts['full_trace_block_equalities']+=1
            counts['full_endpoint_equalities']+=1
            if case.get('exhaustive'):counts['exhaustive_endpoint_equalities']+=1
            if n:
                bad=y[:-1]+[y[-1]+1];vbad=cert.witness(case['input'],bad,check=False)
                check(c.score(vbad)>0,'wrong target accepted',case['id']);counts['wrong_endpoint_rejections']+=1
            if case['id']=='malformed_cascade':
                check(y==case['input'],'new cascade changed')
                ordered=sorted(ref.metadata.step(set(case['input'])))
                check(ordered!=y,'ordered fixture no longer separates')
                check(c.score(cert.witness(case['input'],ordered,check=False))>0,'ordered endpoint accepted')
                counts['old_new_separators']+=1
        if source=='increment_right_zero' and n in (0,1):mutations(c,values,f'{source}-{n}')
        if source=='increment_right' and n==2 and not inverse:
            mutations(c,values,'pair_all')
            # Fully expanded ordinary quartic artifact with exact sparse coefficient count.
            p=cert.polynomial();payload={'format':'sparse-integer-polynomial-v1','input_count':c.input_count,'variable_count':len(c.names),'terms':[[coef,list(mon)]for mon,coef in sorted(p.items())]}
            data=json.dumps(payload,separators=(',',':')).encode();(OUT/'example-pair-quartic.json').write_bytes(data)
            ledgers['expanded_pair_quartic']=dict(monomials=len(p),degree=max(map(len,p),default=0),coefficient_bits=sum(abs(v).bit_length()for v in p.values()),max_coefficient_bits=max(abs(v).bit_length()for v in p.values()),coefficient_l1=sum(abs(v)for v in p.values()),serialized_bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
            check(ev(p,values)==0,'expanded polynomial witness')
            serialized=json.dumps(cert.serialize(),separators=(',',':')).encode();(OUT/'example-pair-sos.json').write_bytes(serialized)
            ledgers['serialized_pair_sos']=dict(bytes=len(serialized),sha256=hashlib.sha256(serialized).hexdigest())
        if source=='increment_right' and n==3 and not inverse:mutations(c,values,'triple_all')
        if source=='increment_right' and n==5 and not inverse:mutations(c,values,'cascade_sample',False)
        print('full passed',source,n,inverse,len(group),flush=True)
        del cert,c,values;gc.collect()
# Fixed horizon 0 and repeated whole steps, including inverse block order.
for n,T in ((0,0),(1,0),(2,0),(3,0),(2,2),(3,2)):
    for inverse in (False,True):
        s=sources['increment_right'];ref=SparseParallelCompiler(s);cert=Certificate(s,n,T,inverse)
        x=([0,5]if n==2 else [0,18,19]if n==3 else [-4]if n==1 else []);y=set(x)
        for _ in range(T):y=ref.step(y,inverse=inverse)
        cert.witness(x,sorted(y));counts['horizon_boundary_equalities']+=1
        ledgers[f'horizon_n{n}_T{T}_inverse{inverse}']=cert.ledger()
        if n:
            vals=cert.witness(x,sorted(y));vals[0]+=1;vals[1]+=1
            check(cert.circuit.score(vals)>0,'noncanonical external pair accepted');counts['external_domain_rejections']+=1
        if n>=2:
            reject(lambda:cert.witness(list(reversed(x)),sorted(y)))
            reject(lambda:cert.witness(x,list(reversed(sorted(y)))))
            reject(lambda:cert.witness([x[0]]*n,sorted(y)))
            reject(lambda:cert.witness(x,[sorted(y)[0]]*n))
        del cert;gc.collect()
# Exact comparator has one natural solution; bounded enumeration corroborates gadget proof.
for d in range(-5,6):
    found=[]
    for b in range(4):
        for slack in range(12):
            if b*(b-1)==0 and d-(2*b-1)*slack+1-b==0:found.append((b,slack))
    check(found==[(int(d>=0),d if d>=0 else -d-1)],'comparison uniqueness',d,found)
    counts['comparator_natural_uniqueness_cases']+=1
receipt=dict(status='PASS',optimized=not __debug__,seconds=time.time()-start,counts=dict(counts),ledgers=ledgers,scope='Exhaustive only on the four explicitly listed finite domains; other cases are targeted. All-input correctness and natural-witness uniqueness require the accompanying proof.',input_fixture_sha256=hashlib.sha256((ROOT/'fixtures.json').read_bytes()).hexdigest())
path=OUT/('receipt-optimized.json'if not __debug__ else 'receipt.json');path.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(status='PASS',counts=dict(counts),seconds=receipt['seconds']),sort_keys=True),flush=True)

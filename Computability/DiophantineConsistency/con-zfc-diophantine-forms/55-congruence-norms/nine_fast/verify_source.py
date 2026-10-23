#!/usr/bin/env python3
"""Independent finite audit of the positive-word source fusion.

No builder is imported. The source residuals and target interactions are
reconstructed from the retained sparse source. This verifies finite algebra,
not the unbounded compiler-to-refutation theorem.
"""
from pathlib import Path
from collections import defaultdict, Counter
import gzip, hashlib, itertools, json, math, random

ROOT=Path(__file__).resolve().parent

def need(ok, message):
    if not ok: raise ValueError(message)

def evaluate(body, assignment, fixed, modulus):
    values=[]
    for i,row in enumerate(body['nodes']):
        kind=row['kind']
        if kind=='literal': v=row['value']
        elif kind=='variable':v=assignment[row['name']]
        elif kind=='fixed':v=fixed[row['name']]
        else:
            need(0<=row['left']<i and 0<=row['right']<i, 'bad operand')
            a,b=values[row['left']],values[row['right']]
            v=a+b if kind=='add' else a-b if kind=='sub' else a*b
        values.append(v%modulus)
    return {name:values[i] for name,i in body['named_nodes'].items()}

def run():
    raw=(ROOT/'upstream/upstream_parent_quartic31.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest()=='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287','source hash')
    source=json.loads(raw); n=len(source['variables'])
    code=json.loads((ROOT/'upstream/code_positive.json').read_text())
    weights=code['weights']; targets=dict(zip(code['order'],code['targets']))
    rows={}; allpairs=list(itertools.combinations_with_replacement(range(n+1),2))
    for eq in source['equations']:
        terms=defaultdict(lambda:defaultdict(int))
        for term in eq['terms']:
            ex=term['powers']; alpha=ex[:n]
            need(sum(alpha)<=2,'source degree')
            pair=tuple([0]*(2-sum(alpha))+[i+1 for i,k in enumerate(alpha) for _ in range(k)])
            factor=math.factorial(2-sum(alpha))*math.prod(math.factorial(k) for k in alpha)
            terms[pair][tuple(ex[n:])]+=factor*term['coefficient']
        rows[eq['number']]={p:{m:c for m,c in cs.items() if c} for p,cs in terms.items()}
    reverse={q:j for j,q in targets.items()}; dcode={}; checks=0; hits=0
    for j,terms in rows.items():
        for pair,co in terms.items():
            position=targets[j]-sum(weights[k] for k in pair)
            need(position>=0 and position not in dcode,'coefficient positions')
            dcode[position]=co
            for beta in allpairs:
                checks+=1; landing=position+sum(weights[k] for k in beta)
                if landing in reverse:
                    need(reverse[landing]==j and beta==pair,'cross-target term')
                    hits+=1
            # Padded-pair factorial times expansion multiplicity equals 2.
            factor=2 if pair[0]==pair[1] else 1
            multiplicity=1 if pair[0]==pair[1] else 2
            need(factor*multiplicity==2,'factorial identity')
    need(len(dcode)==94 and hits==94 and checks==49632,'cardinalities')
    need(max(dcode)==5102 and dcode[5102]=={(0,0,0,0):1},'positive leading term')
    # A positive source zero cannot be the all-one vector: residual 5 is 1.
    p5=next(e for e in source['equations'] if e['number']==5)
    need(all(not any(t['powers'][n:]) for t in p5['terms']),'p5 port dependency')
    need(sum(t['coefficient'] for t in p5['terms'])==1,'nonzero all-one source')
    port_names=('beta','K','MC','MF_source')
    ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients'/f'{name}.bin.gz').read_bytes()),'little') for name in port_names]
    bits=[p.bit_length() for p in ports]
    need(bits==[1064921,1070004,1064921,1064922],'coherent port lengths')
    need(ports[0]==(1<<1064921)-1 and ports[2]%4==2,'native tuple checks')
    bounds=[]
    for row in dcode.values():
        bounds.append(sum(abs(c)*(1<<sum(e*b for e,b in zip(ex,bits))) for ex,c in row.items()))
    need(max(bounds)<1<<2134927,'coefficient bound')
    # Independently replay every source register with actual fixed coefficients.
    rng=random.Random(425180); comparisons=0
    for domain in ('positive','natural'):
        body=json.loads((ROOT/'generated'/f'calibrated_{domain}.json').read_text())
        for mod in (1000003,1000033,1000000007):
            pr=[p%mod for p in ports]
            coeff={pos:sum(c*math.prod(pow(p,e,mod) for p,e in zip(pr,ex)) for ex,c in row.items())%mod for pos,row in dcode.items()}
            fixed={'base_scale':pow(2,2134940,mod),'threshold_scale':pow(2,16012040,mod)}
            for recipe in body['coefficient_recipes']:
                fixed[recipe['name']]=sum(t['coefficient']*math.prod(pow(p,e,mod) for p,e in zip(pr,t['powers'])) for t in recipe['terms'])%mod
            for _ in range(24):
                vals={name:rng.randrange(1 if domain=='positive' else 0,19) for name in body['variables']}
                named=evaluate(body,vals,fixed,mod)
                b=(vals['epsilon_plus']+1) if domain=='positive' else vals['epsilon']+2
                g=2*(vals['g'] if domain=='positive' else vals['g0']+1)
                B=fixed['base_scale']*b*b%mod
                ell=sum(pow(B,w,mod) for w in weights[1:])%mod
                D=sum(co*pow(B,pos,mod) for pos,co in coeff.items())%mod
                at=sum(pow(B,q,mod) for q in code['targets'])%mod
                N0=pow(B,184,mod); L=2*b*pow(B,5741,mod)%mod
                mask=(N0-1-(b-1)*ell)%mod
                tc=(mask+N0*(B-2)*at)%mod
                jc=(2*(1+g+ell)**2*D+at)%mod
                sc=(g+N0*jc)%mod
                R=(L*L+(sc+tc)*L+L-1-sc)%mod
                expect={'b':b%mod,'B':B,'ell':ell,'Dcode':D,'targets':at,'N0':N0,'L':L,'mask':mask,'Tcode':tc,'Jcode':jc,'Scode':sc,'R':R,'N':fixed['threshold_scale']*pow(B,2966,mod)%mod,'Gcap':32*b*pow(B,183,mod)%mod}
                for key,value in expect.items():need(named[key]==value,'source replay '+key)
                comparisons+=1
    return {'status':'PASS','original_positive_source_terms':94,'protected_pairs':len({p for row in rows.values() for p in row}),'source_target_interactions':checks,'intended_target_hits':hits,'D_degree':5102,'D_leading_coefficient':1,'coefficient_bound_exponent':2134927,'largest_triangle_bound_bitlength':max(bounds).bit_length(),'actual_port_bitlengths':bits,'source_register_replays':comparisons,'scope':'Exact finite support and factorial identities, actual coefficient binding, and modular circuit replay. Universal carry, positivity and semantic arguments are in the report.'}

if __name__=='__main__':
    result=run();(ROOT/'SOURCE_FUSION_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

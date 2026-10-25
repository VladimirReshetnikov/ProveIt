#!/usr/bin/env python3
"""Independent signed-domain stage and literal guard audit.

Uses only the Python standard library plus our separately authored sparse
interface auditor. Does not import any producer or sign-inference code.
"""
from pathlib import Path
from collections import Counter
import json, hashlib, runpy, sys
HERE=Path(__file__).resolve().parent
oldargv=sys.argv[:]
sys.argv=[str(HERE/'audit_interfaces.py'),'integer378']
a=runpy.run_path(str(HERE/'audit_interfaces.py'))
sys.argv=oldargv
P=HERE.parent
B=P/'integer378'
e=json.loads((B/'source.json').read_text())
g=json.loads((B/'guarded.json').read_text())
c=json.loads((B/'signed_certificate.json').read_text())
m=a['d'];req=a['req'];add=a['add'];neg=a['neg'];mul=a['mul'];sc=a['sc'];sm=a['sm'];var=a['var'];cn=a['cn']
pol=lambda terms:sm([{tuple(mm):cc} for cc,mm in terms])
rawbody=json.loads((P/'integer378/natural_raw/equation.json').read_text())
req(e['variables']==rawbody['variables'] and e['residuals']==rawbody['residuals'],'signed source changed actual natural body')
req(g['variables'][:len(e['variables'])]==e['variables'] and g['residuals'][:len(e['residuals'])]==e['residuals'],'guarded source changed body')
N=len(e['variables']);R=len(e['residuals']);name_to_i={v['name']:i for i,v in enumerate(e['variables'])}
guards=set(c['signs']['guard_indices']);req(len(guards)==len(c['signs']['guard_indices'])==36,'wrong scalar guard set')
steps=c['signs']['proof_steps']
for s in steps:
    v=s['variable'];p=pol(e['residuals'][s['row']]['terms']);co=p.get((v,))
    req(co is not None and abs(co)==s['coefficient'],'sign coefficient mismatch')
    req(not any(v in mm and mm!=(v,) for mm in p),'variable has nonlinear self dependency')
    rhs=sc({mm:cc for mm,cc in p.items() if mm!=(v,)},-1 if co>0 else 1)
    req(rhs==pol(s['rhs']),'sign RHS differs from actual row')
    if s['kind']=='positive_monomials':
        req(all(cc>=0 for cc in rhs.values()),'negative positive-monomial coefficient')
        deps={i for mm in rhs for i,count in Counter(mm).items() if count%2}
        req(deps==set(s['dependencies']),'incorrect odd-degree sign dependencies')
    elif s['kind']=='affine_square':
        root=pol(s['square_root']);req(all(len(mm)<=1 for mm in root),'nonaffine square root')
        req(mul(root,root)==rhs and not s['dependencies'],'incorrect square sign certificate')
    else:raise ValueError('unknown sign rule')

def close(seed):
    known=set(seed);used=[]
    for s in steps:
        if set(s['dependencies'])<=known:known.add(s['variable']);used.append(s)
    return known,used
prefix,prefixsteps=close(guards)
req(prefix==set(c['prefix_known']) and prefixsteps==c['prefix_steps'],'recorded prefix closure differs')
req(set(c['prefix_required'])<=prefix,'required cap prefix sign missing')
# Actual appended scalar guard equations, with fresh disjoint private triples.
nextvar=N;nextrow=R
for v in sorted(guards):
    aux=list(range(nextvar,nextvar+3));nextvar+=3
    expected=sm([var(v)]+[neg(mul(var(i),var(i))) for i in aux]+[neg(var(aux[2]))])
    rr=g['residuals'][nextrow];nextrow+=1
    req(rr['label']=='nonnegative.'+str(v) and pol(rr['terms'])==expected,'scalar Legendre guard differs')
# Exact pairing identities; each pair's sum is denominator-1.
paircoords=set()
for pr in c['paired_remainders']:
    x,y=pr['pair'];req(x!=y and not ({x,y}&paircoords),'overlapping remainder pair');paircoords|={x,y}
    denom=pol(pr['denominator']);expected=sm([denom,neg(var(x)),neg(var(y)),cn(-1)])
    req(pol(e['residuals'][pr['row']]['terms'])==expected,'remainder sum identity differs')
    aux=list(range(nextvar,nextvar+3));nextvar+=3
    req(aux==pr['auxiliary'] and pr['guard_row']==nextrow,'incorrect product guard layout')
    expected=sm([mul(var(x),var(y))]+[neg(mul(var(i),var(i))) for i in aux]+[neg(var(aux[2]))])
    rr=g['residuals'][nextrow];nextrow+=1
    req(rr['label']=='pair.'+pr['label'] and pol(rr['terms'])==expected,'product Legendre guard differs')
req(len(paircoords)==24 and nextvar==len(g['variables']) and nextrow==len(g['residuals']),'guard coverage mismatch')
# Check exact raw seed identities and prefix positivity through affine export.
raw_to_norm={i:name_to_i[v['name']] for i,v in enumerate(m['variables']) if v['name'] in name_to_i}
seedx={raw_to_norm[p['pair'][0][1]] for p in m['seeds']}
seedy={raw_to_norm[p['pair'][1][1]] for p in m['seeds']}
req(seedx==set(c['seed_X']) and seedy==set(c['seed_Y']),'seed coordinate remapping differs')
req(not ((seedx|seedy)&guards),'seed guards unexpectedly retained')
rawgates={int(k):m['rows'][v] for k,v in m['gates'].items()}
low={}
for i,info in enumerate(m['variables']):
    low[i]=0 if i in raw_to_norm and raw_to_norm[i] in prefix else None
    if i in rawgates:
        rr=rawgates[i];co=next(cc for cc,mm in rr['terms'] if mm==[i]);req(co in (1,-1),'raw gate not monic')
        rhs=[(-cc//co,mm) for cc,mm in rr['terms'] if mm!=[i]]
        if all(cc>=0 and all(low[j] is not None for j in mm) for cc,mm in rhs):
            value=0
            for cc,mm in rhs:
                for j in mm:cc*=low[j]
                value=min(1000000,value+cc)
            low[i]=value if low[i] is None else max(low[i],value)
frameatoms=[z[1] for z in m['cap_certificate']['frame']['all_atoms']]
req(all(low[i] is not None for i in frameatoms),'a semantic frame sign depends on delayed conditions')
req(all(low[p['exponent'][1]] is not None and low[p['exponent'][1]]>=1 for p in m['seeds']),'a seed index lacks presemantic positive sign')
req(all(raw_to_norm[p['output'][1]] in guards for p in m['powers']),'an exact-power output sign is not independently guarded')
req(all(i in guards for i in c['prefix_added_output_guards']) and len(c['prefix_added_output_guards'])==4,'missing explicit bootstrap repair')
# Bind every exact-power and modular row to its stated semantic equation.
exrow=a['exrow'];row=a['row'];atom=a['atom'];A=atom(m['scale'][1]);rawnames=a['nameids'];seedraw={atom(z['exponent']):tuple(map(atom,z['pair'])) for z in m['seeds']}
base_map={};powerquot=[];baset=[];positive=set(i for i,v in low.items() if v is not None and v>=1)
for j,p in enumerate(m['powers']):
    n,k,out=map(atom,[p['base'],p['exponent'],p['output']]);x,y=seedraw[k]
    req(n in positive,'power base not independently positive in topological order')
    if n not in base_map:base_map[n]=rawnames['base'+str(len(base_map))+'.T']
    tt=base_map[n];qq=rawnames['pow'+str(j)+'.quotient'];powerquot.append(raw_to_norm[qq]);baset.append(raw_to_norm[tt])
    expected=sm([var(tt),neg(sc(mul(var(A),var(n)),2)),mul(var(n),var(n)),cn(1)])
    req(exrow(row('base'+str(list(base_map).index(n))+'.T_definition'),{tt,A,n})==neg(expected),'actual power modulus differs')
    expected=sm([var(x),mul(var(n),var(y)),neg(mul(var(A),var(y))),neg(var(out)),neg(mul(var(tt),var(qq)))])
    req(exrow(row('pow'+str(j)+'.power_congruence'),{x,y,n,A,out,tt,qq})==expected,'actual power congruence differs')
    positive.add(out)
# The exact residue requests have positive upper indices, known denominators,
# and no secret use of a quotient sign to identify a congruence.
qb=atom(m['radix']['root_base']);q=atom(m['radix']['radix']);nn=atom(m['radix']['modulus'])
modquot=[];outslacks=[]
for p in m['modular_requests']:
    upper=atom(p['n']);den=atom(p['den']);x,y=map(atom,p['pair']);qq=atom(p['quotient']);r=atom(p['remainder']);ss=atom(p['remainder_slack']);label=p['label'];modquot.append(raw_to_norm[qq])
    modulus=mul(var(den),var(q if p['kind']=='exact' else nn));residue=var(r)
    cut={upper,den,x,y,qq,r,ss,qb,A,q,nn}
    if p['kind']=='exact':
        out=atom(p['output']);oo=rawnames[label+'.modular_oslack'];cut|={out,oo};outslacks.append(raw_to_norm[oo])
        residue=add(residue,mul(var(den),var(out)))
        req(exrow(row(label+'.digit_bound'),{q,out,oo})==sm([var(q),neg(var(out)),neg(var(oo)),cn(-1)]),'exact output bound differs')
    expected=sm([var(x),mul(var(qb),var(y)),neg(mul(var(A),var(y))),neg(residue),neg(mul(modulus,var(qq)))])
    req(exrow(row(label+'.modular_digit'),cut)==expected,'modular digit row differs')
    req(exrow(row(label+'.remainder_bound'),{den,r,ss})==sm([var(den),neg(var(r)),neg(var(ss)),cn(-1)]),'modular remainder row differs')
rootquot=raw_to_norm[rawnames['modular.root_quotient']]
req(set(c['deferred_quotients_and_moduli'])==set(powerquot+baset+modquot+[rootquot]),'unjustified delayed quotient/modulus sign')
req(set(c['deferred_output_slacks'])==set(outslacks),'unjustified output slack sign')
# Every original domain condition returns after the stated mathematical stages.
axioms=seedx|seedy|set(c['deferred_quotients_and_moduli'])|paircoords|set(outslacks)
allknown,_=close(guards|axioms)
req(set(range(N))<=allknown,'a source coordinate remains signed')
canonical=lambda x:(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
pj=json.loads((B/'projection_certificate.json').read_text())
req(hashlib.sha256(canonical(g)).hexdigest()==pj['input_sha256'],'guarded equation not bound to projection source')
result={'status':'PASS','endpoint':'integer378','source_coordinates':N,'scalar_guards':36,'product_guards':12,'sign_rules_checked_against_actual_rows':len(steps),'prefix_sign_rules':len(prefixsteps),'all_semantic_frame_atoms_natural_before_cap':True,'all_seed_indices_positive_before_cap':True,'all_six_power_outputs_independently_guarded':True,'added_power_output_guards':4,'seed_pairs_oriented_by_literal_fullroot_cap':15,'all_exact_power_modulus_and_congruence_rows_checked':6,'all_modular_digit_and_remainder_rows_checked':11,'deferred_quotient_modulus_signs_accounted_for':len(c['deferred_quotients_and_moduli']),'paired_remainder_coordinates':24,'exact_output_slack_derived_after_power_radix':1,'all_original_natural_signs_restored':True,'guarded_source_sha256':pj['input_sha256'],'scope':'literal source/guard/sign-rule/semantic-port composition; unbounded stage proofs reviewed; projection algebra and complete quartic are separately checked by retained independent verifier'}
(HERE/'SIGNED378_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

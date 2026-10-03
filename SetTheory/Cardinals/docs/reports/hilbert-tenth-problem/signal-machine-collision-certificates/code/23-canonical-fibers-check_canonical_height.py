#!/usr/bin/env python3
"""Independent standard-library data-only audit; never imports/executes emitters.

The input and reference JSON files are inert arithmetic DAG records. Default
operation is strictly read-only. Write a receipt by redirecting stdout. With
--expect RECEIPT, recompute all checks and compare against that inert receipt.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import pathlib
import random
import re
import sys

FOLDED_MANIFEST_SHA256 = '774a4498984ebccf8216897e21bf597084e70b148557ba4fa12b597bba44ba91'
BASE_MANIFEST_SHA256 = '1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95'
PRIME = 1000003
FIXTURES = ('incdec', 'zero3', 'nop', 'positive3')
MODES = ('native', 'phase4')
NATIVE_PORTS = ['native__'+x for x in ('F0','F1','F2','a','c','d','f','h','i','j','k','o','r','s','w','tau','eta','zeta','ga','y_aux','odd_half','bound_beta')]
KAPPA = 'canonical_height_slack'
S = 'canonical_endpoint_clock_sum'

class AuditFailure(Exception):
    pass

def demand(condition, message):
    if not condition:
        raise AuditFailure(message)

def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()

def jload(p):
    # Refuse duplicate JSON keys; a parser discrepancy must not hide a DAG.
    def pairs(items):
        out = {}
        for k,v in items:
            demand(k not in out, 'duplicate JSON key: '+k)
            out[k]=v
        return out
    return json.loads(pathlib.Path(p).read_text(), object_pairs_hook=pairs)

def integer(x):
    return type(x) is int

def ports(d):
    return d['parameters']+d['auxiliaries']

def parse_text(text):
    gates=[]
    for line in text.splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        m=re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*) = ([A-Za-z_][A-Za-z_0-9]*|-?\d+) ([+*\-]) ([A-Za-z_][A-Za-z_0-9]*|-?\d+)',line)
        demand(m is not None, 'nonliteral or malformed textual DAG line: '+line)
        name,a,op,b=m.groups()
        gates.append([name,op,int(a) if re.fullmatch(r'-?\d+',a) else a,int(b) if re.fullmatch(r'-?\d+',b) else b])
    return gates

def validate_dag(d, text=None):
    demand(d['parameters']==['x','Tclean'], 'natural ports changed')
    p=ports(d)
    demand(all(type(x) is str and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',x) for x in p), 'invalid port')
    demand(len(p)==len(set(p)), 'duplicate supplied coordinate')
    seen=set(p)
    source=d['source']
    demand(type(source) is list and source, 'empty or invalid source')
    for g in source:
        demand(type(g) is list and len(g)==4,'invalid gate record')
        n,op,a,b=g
        demand(type(n) is str and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',n), 'invalid gate name')
        demand(n not in seen,'duplicate gate or port collision: '+n)
        demand(op in ('+','-','*'),'forbidden operation')
        for x in (a,b):
            demand(integer(x) or (type(x) is str and x in seen),'unbound/forward/nonliteral operand: '+str(x))
        seen.add(n)
    demand(d['output'] in seen-set(p),'output is not a computed gate')
    demand(all(type(c) is list and len(c)==2 for c in d['comparisons']), 'malformed comparisons')
    for c in d['comparisons']:
        for x in c:
            demand(integer(x) or (type(x) is str and x in seen), 'unbound comparison')
    byname={g[0]:g for g in source}
    live=set()
    todo=[d['output']]
    while todo:
        x=todo.pop()
        if integer(x) or x in live:
            continue
        live.add(x)
        if x in byname:
            todo.extend(byname[x][2:])
    dead=sorted(seen-live)
    demand(live==seen,'dead gates/ports: '+str(len(dead))+'; first eight: '+','.join(dead[:8]))
    if text is not None:
        demand(parse_text(text)==source, 'textual DAG does not equal JSON arithmetic source')
        demand('# Natural ports: '+', '.join(d['parameters']) in text, 'textual natural ports disagree')
        demand('# Strictly positive existential ports: '+', '.join(d['auxiliaries']) in text, 'textual positive ports disagree')
        demand(('# Polynomial output: '+d['output'] in text) or ('# Output: '+d['output'] in text), 'textual output disagrees')
    return {'M':sum(g[1]=='*' for g in source),'A':sum(g[1] in ('+','-') for g in source),'total':len(source),'positive_witnesses':len(d['auxiliaries']),'natural_parameters':len(d['parameters']),'comparisons':len(d['comparisons']),'integer_literals':sorted({x for g in source for x in g[2:] if integer(x)}),'all_gates_live':True,'all_coordinates_live':True}

def sos_decomposition(d, n):
    """Require literal differences, squares, left-associated sum, no free gates."""
    tail=d['source'][-(3*n-1):]
    squares=[]
    for i,(a,b) in enumerate(d['comparisons']):
        r,q=tail[2*i:2*i+2]
        demand(r[1:]==['-',a,b], 'SOS residual mismatch at row '+str(i))
        demand(q[1:]==['*',r[0],r[0]],'SOS square mismatch at row '+str(i))
        squares.append(q[0])
    acc=squares[0]
    for i,g in enumerate(tail[2*n:],1):
        demand(g[1:]==['+',acc,squares[i]],'SOS addition mismatch at row '+str(i))
        acc=g[0]
    demand(acc==d['output'], 'SOS output is not the complete sum')
    return d['source'][:-(3*n-1)],tail

def affine_cone(d, wire):
    """Exact integer polynomial for an affine cone; no modular assumptions."""
    by={g[0]:g for g in d['source']}
    cache={x:{x:1} for x in ports(d)}
    def get(x):
        if integer(x):
            return {'':x} if x else {}
        if x in cache:
            return cache[x]
        _,op,a,b=by[x]
        u,v=get(a),get(b)
        if op=='*':
            demand(set(u)<=set(['']) or set(v)<=set(['']), 'nonaffine cone')
            if set(u)<=set(['']):
                out={k:u.get('',0)*c for k,c in v.items()}
            else:
                out={k:v.get('',0)*c for k,c in u.items()}
        else:
            out=dict(u)
            for k,c in v.items():
                out[k]=out.get(k,0)+(c if op=='+' else -c)
        cache[x]={k:c for k,c in out.items() if c}
        return cache[x]
    return get(wire)

def subtract_affine(a,b):
    out=dict(a)
    for k,c in b.items():
        out[k]=out.get(k,0)-c
    return {k:c for k,c in out.items() if c}

def structure(d, old, text=None):
    counts=validate_dag(d,text)
    old_counts=validate_dag(old)
    demand(len(old['comparisons'])==20, 'reference does not have twenty comparisons')
    old_core,old_sos=sos_decomposition(old,20)
    demand(len(d['comparisons'])==21,'new row count is not twenty-one')
    new_core,new_sos=sos_decomposition(d,21)
    demand(d['parameters']==old['parameters'], 'old parameters changed')
    demand(d['auxiliaries']==old['auxiliaries']+[KAPPA], 'new positive witness must append exactly kappa')
    demand([x for x in d['auxiliaries'] if x.startswith('native__')]==NATIVE_PORTS, 'native 22-coordinate block changed')
    demand(d['domain']==old['domain'] and 'strictly positive' in d['domain'],'domain or positivity changed')
    for key in ('fixture','mapping','source_commit','source_pin','source_machine','physical_clock_factor','forward_final_payload_coordinate','native_clock_coordinate','cleaned_target_payload','removed_comparison','folded_clock_formula','folding_base_manifest_sha256','folding_parent_sha256'):
        demand(d[key]==old[key], 'inherited metadata changed: '+key)
    demand(d['comparisons'][:20]==old['comparisons'],'inherited comparison removed, reordered, or changed')
    old_by={g[0]:g for g in old_core}
    old_intermediate=old_by['bridge_height_without_time']
    demand(old_intermediate[1]=='+' and old_intermediate[3]=='height_slack','unexpected frozen intermediate')
    endpoint=old_intermediate[2]
    demand(old_by[endpoint][1:]==['+','bridge_input','bridge_target'], 'frozen endpoint sum malformed')
    consumers=[g for g in old_core if 'bridge_height_without_time' in g[2:]]
    demand(len(consumers)==1 and consumers[0][1:]==['+','bridge_height_without_time','theta_positive'],'old height intermediate not single-consumer')
    h=consumers[0][0]
    demand(all('bridge_height_without_time' not in c for c in old['comparisons']),'intermediate appears in old comparison')
    expected=[]
    for g in old_core:
        if g[0]=='bridge_height_without_time':
            expected.append([S,'+',endpoint,'theta_positive'])
        elif g[0]==h:
            expected.append([h,'+',S,'height_slack'])
        else:
            expected.append(g)
    demand(len(new_core)==len(expected)+2,'new arithmetic core is not old core plus exactly two row producers')
    demand(new_core[:len(expected)]==expected,'inherited arithmetic differs beyond precisely two reassociated gates')
    lhs,rhs=d['comparisons'][20]
    demand(new_core[-2:]==[[lhs,'+','height_slack',KAPPA],[rhs,'+',S,1]],'new row is not eta+kappa=S+1 using two additions')
    meta=d['canonical_height']
    demand(meta['S_register']==S and meta['h_register']==h and meta['added_positive_coordinate']==KAPPA,'canonical metadata wire mismatch')
    demand(meta['native_positive_coordinate_count']==22,'canonical metadata native port count mismatch')
    demand(meta['constraint']=='eta+kappa=S+1','canonical metadata constraint mismatch')
    demand(meta['folded_manifest_sha256']==FOLDED_MANIFEST_SHA256,'canonical metadata manifest pin mismatch')
    demand(meta['reassociation_original']==[old_intermediate,consumers[0]],'reassociation-original metadata mismatch')
    demand(meta['reassociation_new']==[[S,'+',endpoint,'theta_positive'],[h,'+',S,'height_slack']],'reassociation-new metadata mismatch')
    demand(affine_cone(d,h)==affine_cone(old,h),'exact affine height identity failed')
    wanted_S=affine_cone(old,endpoint)
    wanted_S['theta_positive']=wanted_S.get('theta_positive',0)+1
    demand(affine_cone(d,S)==wanted_S,'S is not encoded endpoint sum plus theta')
    wanted_r={k:-c for k,c in wanted_S.items()}
    wanted_r['height_slack']=1
    wanted_r[KAPPA]=1
    wanted_r['']=wanted_r.get('',0)-1
    wanted_r={k:c for k,c in wanted_r.items() if c}
    demand(subtract_affine(affine_cone(d,lhs),affine_cone(d,rhs))==wanted_r,'new residual polynomial wrong')
    demand(counts['M']==old_counts['M']+1 and counts['A']==old_counts['A']+4,'independent net count is not +1M+4A')
    demand(counts['total']==old_counts['total']+5,'independent total delta not five')
    counts['SOS_gates']=len(new_sos)
    for key,val in counts.items():
        demand(d['ledger'][key]==val,'ledger disagrees with DAG: '+key)
    return counts,{'old_height_wire':h,'endpoint_sum_wire':endpoint,'canonical_sum_affine':wanted_S,'residual_affine':wanted_r,'literal_inherited_core_gates':len(old_core)-2,'reassociated_gates':2,'new_row_producer_gates':2,'old_SOS':{'M':20,'A':39,'total':59},'new_SOS':{'M':21,'A':41,'total':62},'identity':'Q_new = Q_folded + (height_slack + canonical_height_slack - (bridge_input + bridge_target + theta_positive) - 1)^2','identity_domain':'all integer tuples; indeed every commutative coefficient ring'}

def leading_certificate(d):
    cert=d['exact_degree_certificate']
    demand(cert['modulus']==PRIME,'certificate modulus changed')
    demand(all(PRIME%q for q in range(2,1001)), 'hard-coded modulus is not prime')
    weights={x:i+2 for i,x in enumerate(ports(d))}
    demand(cert['substitution_weights']==weights,'substitution map not canonical linear specialization')
    env={x:(1,v%PRIME) for x,v in weights.items()}
    def get(x):
        return (0,x%PRIME) if integer(x) else env[x]
    trace=[]
    for n,op,a,b in d['source']:
        da,ca=get(a);db,cb=get(b)
        if op=='*':
            degree,top=da+db,ca*cb%PRIME
        else:
            degree=max(da,db)
            top=((ca if da==degree else 0)+(1 if op=='+' else -1)*(cb if db==degree else 0))%PRIME
        env[n]=(degree,top)
        trace.append([n,degree,top])
    degree,top=env[d['output']]
    demand(cert['gate_degree_top_trace']==trace,'per-gate degree/top trace mismatch')
    demand(cert['formal_degree']==degree and cert['nonzero_top_coefficient']==top and top!=0,'final degree certificate invalid')
    demand(d['ledger']['exact_degree']==degree,'ledger exact degree mismatch')
    return degree,top,weights,env

def trim(p):
    while len(p)>1 and p[-1]==0:
        p.pop()
    return p

def poly_add(a,b,sign=1):
    c=list(a)+[0]*max(0,len(b)-len(a))
    for j,v in enumerate(b):
        c[j]=(c[j]+sign*v)%PRIME
    return trim(c)

def poly_mul(a,b):
    if a==[0] or b==[0]:
        return [0]
    if len(a)==1:
        return trim([(a[0]*v)%PRIME for v in b])
    if len(b)==1:
        return trim([(b[0]*v)%PRIME for v in a])
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                c[i+j]+=x*y
    return trim([v%PRIME for v in c])

def full_polynomials(d,weights,trace=None):
    env={x:[0,weights[x]%PRIME] for x in ports(d)}
    def get(x):
        return [x%PRIME] if integer(x) else env[x]
    for n,op,a,b in d['source']:
        u,v=get(a),get(b)
        env[n]=poly_mul(u,v) if op=='*' else poly_add(u,v,1 if op=='+' else -1)
        if trace is not None:
            degree,top=trace[n]
            demand(len(env[n])-1<=degree,'full specialization exceeds formal degree')
            demand((env[n][degree] if degree<len(env[n]) else 0)==top,'full coefficient disagrees with top trace at '+n)
    return env

def evaluate(d,values,modulus=None):
    env=dict(values)
    def get(x):
        return x if integer(x) else env[x]
    for n,op,a,b in d['source']:
        x,y=get(a),get(b)
        z=x+y if op=='+' else x-y if op=='-' else x*y
        env[n]=z%modulus if modulus else z
    return env

def integer_digest(v):
    return sha_bytes((b'-' if v<0 else b'+')+abs(v).to_bytes(max(1,(abs(v).bit_length()+7)//8),'big'))

def numerical_checks(d,old):
    rng=random.Random('canonical-height-independent:'+d['fixture']+':'+str(d['physical_clock_factor']))
    digest=hashlib.sha256();n_signed=12;n_modular=32
    for modulus,n in ((None,n_signed),(1000003,n_modular//2),(1000033,n_modular//2)):
        for i in range(n):
            values={x:rng.randint(-2,2) if modulus is None else rng.randrange(-modulus,modulus) for x in ports(d)}
            newenv=evaluate(d,values,modulus);oldenv=evaluate(old,values,modulus)
            delta=values['height_slack']+values[KAPPA]-newenv[S]-1
            expected=oldenv[old['output']]+delta*delta
            if modulus:
                expected%=modulus
            demand(newenv[d['output']]==expected,'all-tuple numeric identity failure')
            for a,b in old['comparisons']:
                ov=(a if integer(a) else oldenv[a])-(b if integer(b) else oldenv[b])
                nv=(a if integer(a) else newenv[a])-(b if integer(b) else newenv[b])
                demand((ov-nv)%modulus==0 if modulus else ov==nv,'old residual changed numerically')
            if modulus is None:
                demand(newenv[d['output']]>=0,'integer SOS is negative')
            digest.update(integer_digest(newenv[d['output']]).encode())
    return {'signed_complete_assignments':n_signed,'modular_complete_assignments':n_modular,'old_residuals_per_assignment':20,'evaluation_digest_sha256':digest.hexdigest()}

def corruption_suite(d,old,text):
    results=[]
    def reject(name,mutate,which='structure'):
        c=copy.deepcopy(d)
        t=text
        replacement=mutate(c,t)
        if replacement is not None:
            t=replacement
        try:
            if which=='degree':
                leading_certificate(c)
            else:
                structure(c,old,t if which=='text' else None)
        except (AuditFailure,KeyError,IndexError,TypeError,ValueError) as e:
            results.append({'case':name,'rejected':True,'reason':str(e)})
        else:
            raise AuditFailure('corruption accepted: '+name)
    reject('duplicate_positive_coordinate',lambda c,t:c['auxiliaries'].append(c['auxiliaries'][-1]))
    reject('missing_kappa',lambda c,t:c['auxiliaries'].pop())
    reject('kappa_domain_relaxation',lambda c,t:c.__setitem__('domain','all auxiliaries natural'))
    reject('drop_positive_F',lambda c,t:c['auxiliaries'].remove('final_positive'))
    reject('drop_native_coordinate',lambda c,t:c['auxiliaries'].remove('native__bound_beta'))
    reject('unsupported_operation',lambda c,t:c['source'][0].__setitem__(1,'/'))
    reject('unbound_operand',lambda c,t:c['source'][0].__setitem__(3,'missing_input'))
    reject('duplicate_gate',lambda c,t:c['source'][1].__setitem__(0,c['source'][0][0]))
    reject('dead_extra_gate',lambda c,t:c['source'].append(['unused_gate','+',1,1]))
    reject('wrong_output',lambda c,t:c.__setitem__('output',c['source'][0][0]))
    reject('wrong_inherited_scalar',lambda c,t:c['source'][0].__setitem__(2,c['source'][0][2]+1))
    reject('wrong_source_pin',lambda c,t:c.__setitem__('source_pin','0'*64))
    reject('raw_mapping_change',lambda c,t:c['mapping'].__setitem__('K',6))
    reject('raw_guard_change',lambda c,t:c['source_machine']['instructions'][0].__setitem__(2,'nop' if c['source_machine']['instructions'][0][2]!='nop' else 'inc'))
    reject('remove_chronology_comparison',lambda c,t:c['comparisons'].pop(1))
    reject('remove_native_comparison',lambda c,t:c['comparisons'].pop(2))
    reject('remove_clock_congruence',lambda c,t:c['comparisons'].pop(18))
    reject('remove_clean_clock_row',lambda c,t:c['comparisons'].pop(19))
    reject('remove_height_row',lambda c,t:c['comparisons'].pop(20))
    def wrong_S(c,t):
        next(g for g in c['source'] if g[0]==S)[3]='height_slack'
    reject('wrong_reassociation_S',wrong_S)
    def wrong_h(c,t):
        next(g for g in c['source'] if g[2]==S and g[3]=='height_slack')[3]='theta_positive'
    reject('wrong_reassociation_height',wrong_h)
    def wrong_new_row(c,t):
        next(g for g in c['source'] if g[0]==c['comparisons'][-1][1])[3]=2
    reject('new_row_off_by_one',wrong_new_row)
    reject('SOS_unsquared_last_residual',lambda c,t:c['source'][-21].__setitem__(1,'+'))
    reject('SOS_missing_final_sum',lambda c,t:c['source'].pop())
    reject('forged_ledger_total',lambda c,t:c['ledger'].__setitem__('total',c['ledger']['total']-1))
    reject('forged_degree',lambda c,t:c['exact_degree_certificate'].__setitem__('formal_degree',1),'degree')
    reject('forged_top_trace',lambda c,t:c['exact_degree_certificate']['gate_degree_top_trace'][0].__setitem__(2,0),'degree')
    reject('forged_substitution',lambda c,t:c['exact_degree_certificate']['substitution_weights'].__setitem__('x',99),'degree')
    reject('textual_gate_corruption',lambda c,t:t.replace('bridge_input_scaled = 5 * x','bridge_input_scaled = 6 * x',1),'text')
    return results

def authenticate_references(root,live=None):
    ref=root/'reference'/'folded'
    manifest=ref/'MANIFEST.json'
    demand(sha_bytes(manifest.read_bytes())==FOLDED_MANIFEST_SHA256,'folded manifest pin mismatch')
    entries=jload(manifest)['files']
    out={}
    for f in FIXTURES:
        for mode in MODES:
            rel='circuits/'+f+'-'+mode+'-folded.json'
            p=ref/rel;b=p.read_bytes()
            demand(sha_bytes(b)==entries[rel]['sha256'] and len(b)==entries[rel]['bytes'],'reference hash mismatch: '+rel)
            out[f+'-'+mode]={'sha256':sha_bytes(b),'bytes':len(b)}
    bm=root/'reference'/'base'/'MANIFEST.json'
    demand(sha_bytes(bm.read_bytes())==BASE_MANIFEST_SHA256,'base manifest pin mismatch')
    if live:
        baseline=jload(root/'audit'/'frozen-before.json')
        for dirname,expected in baseline.items():
            folder=pathlib.Path(live)/dirname
            actual={str(p.relative_to(folder)):{'sha256':sha_bytes(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(folder.rglob('*')) if p.is_file()}
            demand(actual==expected,'frozen directory changed since before-audit snapshot: '+dirname)
    return out

def audit_zero_step(root):
    manifest=jload(root/'reference'/'base'/'MANIFEST.json')['files']
    out={}
    for mode,factor in (('native',1),('phase4',4)):
        rel='circuits/zero-step-'+mode+'.json'
        p=root/rel;reference=root/'reference'/'base'/rel
        raw=p.read_bytes();expected=reference.read_bytes();entry=manifest[rel]
        demand(raw==expected,'zero-step copy not byte-identical: '+mode)
        demand(sha_bytes(expected)==entry['sha256'] and len(expected)==entry['bytes'],'zero-step reference not manifest-pinned: '+mode)
        d=jload(p);counts=validate_dag(d)
        demand(d['auxiliaries']==[] and len(d['comparisons'])==1,'zero-step witnesses/row changed')
        demand(d['physical_clock_factor']==factor,'zero-step model factor changed')
        core,tail=sos_decomposition(d,1)
        demand(len(core)==2 and core[0][1:]==['*',384*factor,'x'] and core[1][1:]==['+',core[0][0],400*factor],'zero-step affine clock changed')
        demand(d['comparisons']==[[core[1][0],'Tclean']],'zero-step clock comparison changed')
        for k,v in counts.items():
            demand(d['ledger'][k]==v,'zero-step ledger mismatch: '+k)
        degree,top,weights,trace=leading_certificate(d)
        full=full_polynomials(d,weights,trace)
        demand(len(full[d['output']])-1==degree==2,'zero-step exact degree mismatch')
        out[mode]={'sha256':sha_bytes(raw),'byte_identical_to_pinned_base':True,'ledger_recomputed':counts,'exact_degree':degree,'nonzero_leading_coefficient':top,'polynomial':'('+str(384*factor)+'*x+'+str(400*factor)+'-Tclean)^2'}
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parents[1])
    parser.add_argument('--expect',type=pathlib.Path)
    parser.add_argument('--live-frozen',type=pathlib.Path,metavar='PARENT',help='Optional parent directory containing original frozen input packets')
    args=parser.parse_args();root=args.root.resolve()
    refs=authenticate_references(root,args.live_frozen)
    report={'audit':'canonical-height-independent-data-only-v1','passed':True,'scope':'Eight complete nonempty-history circuits; arithmetic identities and preserved interface, not a new native/Pell existence proof','frozen_manifest_sha256':{'folded':FOLDED_MANIFEST_SHA256,'base':BASE_MANIFEST_SHA256},'reference_circuits':refs,'circuits':{},'corruption_tests':[]}
    found={}
    for p in (root/'circuits').glob('*.json'):
        d=jload(p)
        if d.get('fixture') not in FIXTURES:
            continue
        mode='native' if d['physical_clock_factor']==1 else 'phase4' if d['physical_clock_factor']==4 else 'unknown'
        key=d['fixture']+'-'+mode
        demand(key not in found,'duplicate fixture/model circuit')
        found[key]=(p,d)
    demand(set(found)=={f+'-'+m for f in FIXTURES for m in MODES},'not exactly eight expected complete circuits')
    for f in FIXTURES:
        for mode in MODES:
            key=f+'-'+mode;p,d=found[key]
            old=jload(root/'reference'/'folded'/'circuits'/(key+'-folded.json'))
            demand(d['canonical_height']['parent_sha256']==refs[key]['sha256'],'canonical parent pin mismatch')
            text=p.with_suffix('.dag.txt').read_text()
            counts,identity=structure(d,old,text)
            degree,top,weights,trace=leading_certificate(d)
            full=full_polynomials(d,weights,trace)
            old_full=full_polynomials(old,{x:weights[x] for x in ports(old)})
            output=full[d['output']]
            demand(len(output)-1==degree and output[-1]==top,'independent full univariate exact degree mismatch')
            lhs,rhs=d['comparisons'][-1]
            residual=poly_add(full[lhs],full[rhs],-1)
            demand(output==poly_add(old_full[old['output']],poly_mul(residual,residual)),'full-univariate output identity failed')
            numbers=numerical_checks(d,old)
            counts['exact_degree']=degree
            report['circuits'][key]={'file':str(p.relative_to(root)),'sha256':sha_bytes(p.read_bytes()),'ledger_recomputed':counts,'all_tuple_identity_proof':identity,'degree':{'formal_upper_bound':degree,'full_univariate_degree':len(output)-1,'modulus':PRIME,'nonzero_leading_coefficient':top,'all_gate_coefficients_crosschecked':len(d['source']),'full_output_coefficients_sha256':sha_bytes(json.dumps(output,separators=(',',':')).encode())},'numerical_sanity':numbers}
            if key=='incdec-native':
                report['corruption_tests']=corruption_suite(d,old,text)
    report['zero_step']=audit_zero_step(root)
    report['totals']={'circuits':len(found),'gates':sum(x['ledger_recomputed']['total'] for x in report['circuits'].values()),'signed_assignments':sum(x['numerical_sanity']['signed_complete_assignments'] for x in report['circuits'].values()),'modular_assignments':sum(x['numerical_sanity']['modular_complete_assignments'] for x in report['circuits'].values()),'rejected_corruptions':len(report['corruption_tests'])}
    authenticate_references(root,args.live_frozen)
    if args.expect:
        demand(report==jload(args.expect),'recomputed audit differs from expected receipt')
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':
    try:
        main()
    except AuditFailure as e:
        print('AUDIT FAILED: '+str(e),file=sys.stderr)
        sys.exit(1)

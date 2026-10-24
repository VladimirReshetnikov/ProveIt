#!/usr/bin/env python3
"""Exact DAG degree/leading-coefficient audit and finite transcription checks."""
from collections import Counter
from pathlib import Path
import gzip, hashlib, json, random
import build

ROOT=Path(__file__).resolve().parent

def fail(s):raise ValueError(s)

def degree_coefficient(packet):
    variables=packet['variables'];ports=packet['fixed_ports'];names=variables+ports
    target=packet['degree_certificate']['monomial'];n=len(names)
    limits=[target.get(x,0) for x in variables]+[1000]*len(ports)
    zero=(0,)*n
    def add(a,b,s=1):
        z=dict(a)
        for m,c in b.items():
            z[m]=z.get(m,0)+s*c
            if not z[m]:del z[m]
        return z
    def mul(a,b):
        z={}
        for m,c in a.items():
            for t,e in b.items():
                u=tuple(x+y for x,y in zip(m,t))
                if any(x>y for x,y in zip(u,limits)):continue
                z[u]=z.get(u,0)+c*e
        return {m:c for m,c in z.items() if c}
    values=[]
    for node in packet['nodes']:
        op=node[0]
        if op=='constant':values.append((0,{zero:node[1]} if node[1] else {}))
        elif op in ('variable','port'):
            mon=list(zero);j=names.index(node[1]);mon[j]=1
            values.append((1 if op=='variable' else 0,{tuple(mon):1} if limits[j] else {}))
        else:
            da,a=values[node[1]];db,b=values[node[2]]
            if op=='mul':values.append((da+db,mul(a,b)))
            else:
                d=max(da,db)
                values.append((d,add(a if da==d else {},b if db==d else {},-1 if op=='sub' else 1)))
    degree,top=values[packet['output']]
    if degree!=packet['exact_degree']:fail('degree upper bound differs')
    t=tuple(target.get(x,0) for x in variables)
    coeff={m[len(variables):]:c for m,c in top.items() if m[:len(variables)]==t}
    variant=packet['base_variant']
    exponent={20:12,19:16,18:56}[variant]
    scalar={20:3**12,19:1944**4,18:2**32*3**64}[variant]
    if packet['transport_eliminated'] and variant==20:exponent=16;scalar=3**16
    expected={(exponent,0,0,0,0,0):scalar}
    if coeff!=expected:fail(f'leading coefficient mismatch: {coeff}')
    return {'degree_upper_bound':degree,'exact_nonzero_coefficient':str(scalar)+'*beta^'+str(exponent),
        'target_monomial':target,'proof':'Exact homogeneous polynomial arithmetic with all six coefficient ports symbolic.'}

def evaluate(packet,env,mod):
    vals=[]
    for n in packet['nodes']:
        op=n[0]
        if op=='constant':v=n[1]
        elif op in ('variable','port'):v=env[n[1]]
        elif op=='add':v=vals[n[1]]+vals[n[2]]
        elif op=='sub':v=vals[n[1]]-vals[n[2]]
        elif op=='mul':v=vals[n[1]]*vals[n[2]]
        else:fail('unknown operation')
        vals.append(v%mod)
    return {k:vals[i] for k,i in packet['residuals'].items()},vals[packet['output']]

def spec(variant,v,transport=False):
    J=3*v['J3']+1;q=v['beta']*J+1;W=4*(3*v['w3']+1)
    X=q*W;Y=(2*v['v_scale']+1)*q**3;c=v['c'];f=v['f']
    a=v['a'] if variant==20 else (X+1)*Y
    E=a-Y;H=4*a+3;delta=(a+2)**2-1
    if transport:
        C=v['C'];F=(v['K0']+W)*C-v['z']*(q-1);alpha=q-F-C
    else:F=v['F'];alpha=v['alpha'];C=q-F-alpha
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(v['MC']+q*v['MF'])*J
    k=R+1+v['h']*E;eta=v['eta'] if variant!=18 else c-Y*k
    zeta=k-eta;I=(2*v['r']+1)*c*c
    B=f*f*(c*v['T']-R);V=B-c;yold=B+v['y'];tauold=E*(c-eta)+v['tau']
    G=v['cone_A']*F*v['cone_B']*C-(q-v['cone_A']*F-v['cone_B']*C)**2
    P=1+v['pair_pos1']**2+v['pair_pos2']**2+v['pair_pos3']*(v['pair_pos3']+1)
    coeff=delta*(f*f-1) if variant==20 else I*I
    out={}
    if variant==20:out['scale']=a-(X+1)*Y
    if variant!=18:out['remainder']=c-eta-Y*k
    out.update({'first_norm':tauold*tauold-E*(c-eta)*(k+E*(c-eta))-1,
        'main_norm':(X+a*c+v['gamma']*H)**2-delta*c*c-1,
        'strong_norm':I*I-delta*(f*f-1),
        'auxiliary_norm':coeff*(V*V-yold*yold)+yold*yold-1,
        'joint_guard':G*eta*zeta-(v['pair_root']**2-G-eta*zeta+1)**2-P})
    if not transport:out['transport']=(v['K0']+W)*C-F-v['z']*(q-1)
    return out

def fixed_ports():
    folder=ROOT.parent.parent/'coefficients'
    binding=json.loads((folder/'BINDING.json').read_text())
    values={}
    for name in build.PORTS:
        record=binding['payloads'][name]
        raw=gzip.decompress((folder/record['file']).read_bytes())
        if hashlib.sha256(raw).hexdigest()!=record['raw_sha256']:fail('coefficient digest '+name)
        number=int.from_bytes(raw,'little')
        if number.bit_length()!=record['bits']:fail('coefficient bit length '+name)
        values[name]=number
    if values['beta']!=(1<<1064921)-1:fail('beta numeral')
    if values['cone_A']!=1<<1113 or values['cone_B']!=1<<666104:fail('cone numerals')
    return values

def audit(packet):
    variable_count=len(packet['variables'])
    if variable_count!=packet['variable_count']:fail('variable count')
    nodes=packet['nodes'];live=set()
    def visit(i):
        if i in live:return
        if not 0<=i<len(nodes):fail('node index')
        live.add(i);n=nodes[i]
        if n[0] in ('add','sub','mul'):
            if n[1]>=i or n[2]>=i:fail('non-topological node')
            visit(n[1]);visit(n[2])
    visit(packet['output'])
    if live!=set(range(len(nodes))):fail('dead nodes')
    seen={n[1] for n in nodes if n[0]=='variable'}
    if seen!=set(packet['variables']):fail('unused or undeclared input')
    counts=Counter(n[0] for n in nodes if n[0] in ('add','sub','mul'))
    if dict(counts)!=packet['operation_counts'] or sum(counts.values())!=packet['operations']:fail('operation count')
    rng=random.Random(731014+variable_count);mod=1000000007
    for trial in range(80):
        env={x:rng.randrange(-9,10) for x in packet['variables']+packet['fixed_ports']}
        rows,total=evaluate(packet,env,mod);want=spec(packet['base_variant'],env,packet['transport_eliminated'])
        if rows!={k:x%mod for k,x in want.items()}:fail('independent residual transcription')
        if total!=sum(x*x for x in rows.values())%mod:fail('sum of squares')
    actual={name:value%mod for name,value in fixed_ports().items()}
    for trial in range(80):
        env={name:rng.randrange(-9,10) for name in packet['variables']}
        env.update(actual)
        rows,total=evaluate(packet,env,mod)
        want=spec(packet['base_variant'],env,packet['transport_eliminated'])
        if rows!={k:x%mod for k,x in want.items()}:fail('actual-coefficient transcription')
        if total!=sum(x*x for x in rows.values())%mod:fail('actual-coefficient sum of squares')
    return {'name':packet['name'],'operations':packet['operations'],'residuals':packet['residual_count'],
        'degree_certificate':degree_coefficient(packet),'transcription_diagnostics':80,'actual_coefficient_diagnostics':80,
        'diagnostic_scope':'Finite modular checks are transcription diagnostics, not semantic proofs.'}

def main():
    results=[]
    for variant,transport in build.EXPORTED_VARIANTS:
        path=ROOT/(f'quotient{variant}'+('_transport' if transport else '')+'.json');packet=json.loads(path.read_text())
        if packet!=build.make(variant,transport):fail('literal packet differs from generator')
        results.append(audit(packet))
    (ROOT/'VERIFICATION.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()

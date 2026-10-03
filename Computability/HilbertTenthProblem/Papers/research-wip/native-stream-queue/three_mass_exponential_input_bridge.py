#!/usr/bin/env python3
"""Four authenticated ordinary-input exponential / unbounded-history compositions.

Only JSON parents are loaded. No dependency module or cached bytecode executes.
Public build/checked/evaluate support exactly the four documented variants.
"""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

if not __debug__:
    raise RuntimeError('run without -O')
PINS = {
 'pell_fixed_affine_exponent52.py':'64893c621c538a8f5dba8a0fc417fd46aae7c607da996dd5f304ca13642f1486',
 'pell_fixed_affine_exponent52.json':'ebf7cafaa1f19c77c72302e5fee2e2c41c19b76a1ab72942758478ab1dd1adf1',
 'pell_fixed_affine_exponent52.md':'891301377f3740657c268e3e48f697dc5cb5a08037665aa772c1bff0d200b9ec',
 'native_pell_factored_first_coefficient.py':'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'native_pell_factored_first_coefficient.json':'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md':'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
}
VARIANTS = ('incdec','zero3','nop','positive3')

def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,(list,tuple)): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def sha(b): return hashlib.sha256(b).hexdigest()
def digest(x): return sha(json.dumps(x,sort_keys=True,separators=(',',':')).encode())
def parents(root):
    root=Path(root) if root is not None else Path(__file__).resolve().parent
    for name,pin in PINS.items():
        if sha((root/name).read_bytes())!=pin: raise ValueError('source authentication: '+name)
    e=json.loads((root/'pell_fixed_affine_exponent52.json').read_text())
    n=json.loads((root/'native_pell_factored_first_coefficient.json').read_text())
    return e,{f['variant'][6:]:f['packet'] for f in n['forms'] if f['variant'].startswith('clock_')}

def rename(v,prefix,parameters):
    return v if type(v) is int or v in parameters else prefix+v

def rows_rename(rows,prefix,parameters):
    return [[prefix+n,op,rename(a,prefix,parameters),rename(b,prefix,parameters)] for n,op,a,b in rows]

def ledger(rows,parameters,aux,roots):
    defined=set(parameters+aux); degrees={n:1 for n in defined}; table={}; m=0
    for n,op,a,b in rows:
        if type(n) is not str or n in defined or op not in ('+','-','*'): raise ValueError('bad DAG')
        for v in (a,b):
            if type(v) is not int and (type(v) is not str or v not in defined): raise ValueError('forward reference/type')
        da=0 if type(a) is int else degrees[a]; db=0 if type(b) is int else degrees[b]
        degrees[n]=da+db if op=='*' else max(da,db)
        table[n]=(a,b); defined.add(n); m+=op=='*'
    live=set(); stack=list(roots)
    while stack:
        v=stack.pop()
        if type(v) is str and v not in live:
            live.add(v)
            if v in table: stack.extend(table[v])
    if not set(table)<=live: raise ValueError('dead gates')
    return {'operations':len(rows),'M':m,'A':len(rows)-m,'positive_witnesses':len(aux),
            'all_gates_live':True,'literal_degree_upper_bound':max(degrees[v] if type(v) is str else 0 for v in roots)}

def _compose(e,h,variant,finalizer):
    if e['source'][-1]!=['output','-','factor_product_5',1]: raise ValueError('exponent finalizer')
    if h['parameters']!=['x','y','T'] or len(h['comparisons'])!=20: raise ValueError('history interface')
    K=h['parent_metadata']['mapping']['K']; q0=h['parent_metadata']['mapping']['initial']
    wanted=[['bridge_input_scaled','*',K,'x'],['bridge_input','+','bridge_input_scaled',q0]]
    got=[r for r in h['source'] if r[0] in ('bridge_input_scaled','bridge_input')]
    if got!=wanted: raise ValueError('loader shape')
    for v,target in [('x','bridge_input_scaled'),('bridge_input_scaled','bridge_input')]:
        if [r[0] for r in h['polynomial_source'] if v in r[2:]]!=[target]: raise ValueError('private loader')
        if any(v in c for c in h['comparisons']): raise ValueError('comparison loader consumer')
    erows=rows_rename(e['source'][:-1],'exp__',['x'])
    def hist(rows):
        ans=rows_rename(rows,'mass__',['x','y','T'])
        for r in ans:
            if r[0]=='mass__bridge_input_scaled': r[3]='exp__Q'
            if r[0]=='mass__bridge_input': r[3]=q0-K
        return ans
    source=erows+hist(h['source'])
    sos='mass__'+h['output']; unit='exp__factor_product_5'
    tail=([
        ['bridge_exp_residual','-',unit,1],['bridge_exp_square','*','bridge_exp_residual','bridge_exp_residual'],
        ['bridge_output','+','bridge_exp_square',sos]] if finalizer=='sos' else [
        ['bridge_sos_plus_one','+',sos,1],['bridge_unit_times_sos','*',unit,'bridge_sos_plus_one'],
        ['bridge_output','-','bridge_unit_times_sos',1]])
    poly=erows+hist(h['polynomial_source'])+tail
    comparisons=[[unit,1]]+[[rename(a,'mass__',['x','y','T']),rename(b,'mass__',['x','y','T'])] for a,b in h['comparisons']]
    aux=['exp__'+v for v in e['auxiliaries']]+['mass__'+v for v in h['auxiliaries']]
    params=['x','y','T']
    certledger=ledger(source,params,aux,[v for c in comparisons for v in c])
    polyledger=ledger(poly,params,aux,['bridge_output'])
    polyledger['refined_degree_upper_bound']=(max(108,h['degree']['upper_bound']) if finalizer=='sos' else h['degree']['upper_bound']+54)
    return {'variant':variant,'finalizer':finalizer,'parameters':params,'auxiliaries':aux,
      'domains':{'x':'positive integer','y':'natural integer','T':'natural integer','auxiliaries':'positive integers'},
      'source':source,'comparisons':comparisons,'polynomial_source':poly,'output':'bridge_output',
      'interfaces':{'ordinary_input':'x','computed_initial_payload':'exp__Q','final_payload':'y','native_physical_clock':'T',
                    'exponent_unit':unit,'history_sos':sos,'encoded_initial_configuration':'mass__bridge_input'},
      'certificate_ledger':certledger,'polynomial_ledger':polyledger,
      'degree':{'exact_degree_claimed':False,'upper_bound':polyledger['refined_degree_upper_bound'],
                'reason':'degree(U)=54 and affine Q substitution cannot increase the inherited history SOS degree'},
      'relation':('(U_exp-1)^2+S_history(Q-1,y,T)' if finalizer=='sos' else 'U_exp*(1+S_history(Q-1,y,T))-1'),
      'ordinary_input_projection':'initial payload 2^(96*x); initial valuations (96*x,0)',
      'fixed_machine':copy.deepcopy(h['parent_metadata']['machine']),
      'historical_provenance':{'history_packet_sha256':digest(h),'history_ledger':copy.deepcopy(h['polynomial_ledger']),
        'parent_raw_input':'x_old=Q-1','history_degree':copy.deepcopy(h['degree'])},
      'scope':'Four nonuniversal fixed machines. Runtime existential. No source-input universality theorem asserted.'}

def build(variant='incdec',*,finalizer='sos',root=None):
    if type(variant) is not str or variant not in VARIANTS: raise ValueError('variant')
    if type(finalizer) is not str or finalizer not in ('sos','anchor'): raise ValueError('finalizer')
    e,hs=parents(root); return _compose(e,hs[variant],variant,finalizer)

def checked(packet,*,root=None):
    if type(packet) is not dict or type(packet.get('variant')) is not str: raise ValueError('packet')
    p=build(packet['variant'],finalizer=packet.get('finalizer'),root=root)
    if not exact(packet,p): raise ValueError('noncanonical packet')
    return p

def values_of(rows,values):
    d=dict(values)
    for n,op,a,b in rows:
        a=a if type(a) is int else d[a]; b=b if type(b) is int else d[b]
        d[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return d

def evaluate(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root)
    if type(signed) is not bool or type(values) is not dict or set(values)!=set(p['parameters']+p['auxiliaries']): raise ValueError('assignment')
    for k,v in values.items():
        if type(v) is not int: raise ValueError('integer required')
        if not signed and (v<0 or (k not in ('y','T') and v==0)): raise ValueError('domain')
    return values_of(p['polynomial_source'],values)[p['output']]

class Intern:
    def __init__(self): self.ids={}
    def node(self,key):
        if key not in self.ids: self.ids[key]=len(self.ids)
        return self.ids[key]
    def atom(self,x): return self.node(('atom',type(x).__name__,x))
    def op(self,op,a,b): return self.node((op,a,b))

def structural_proof(e,h,p):
    """Exact local affine equality then identical whole downstream expression DAG."""
    K=h['parent_metadata']['mapping']['K']; q0=h['parent_metadata']['mapping']['initial']
    # Expand the two ACTUAL loader rows in the indeterminate Q.  A pair is
    # (constant coefficient, Q coefficient); multiplication must stay affine.
    def affine_rows(rows,values):
        d=dict(values)
        for n,op,a,b in rows:
            a=(a,0) if type(a) is int else d[a]
            b=(b,0) if type(b) is int else d[b]
            if op=='*':
                assert a[1]*b[1]==0
                d[n]=(a[0]*b[0],a[0]*b[1]+a[1]*b[0])
            else:
                sign=1 if op=='+' else -1
                d[n]=(a[0]+sign*b[0],a[1]+sign*b[1])
        return d
    oldlocal=affine_rows([r for r in h['source'] if r[0] in ('bridge_input_scaled','bridge_input')],{'x':(-1,1)})
    newlocal=affine_rows([r for r in p['source'] if r[0] in ('mass__bridge_input_scaled','mass__bridge_input')],{'exp__Q':(0,1)})
    assert oldlocal['bridge_input']==newlocal['mass__bridge_input']==(q0-K,K)
    intern=Intern(); leaves={v:intern.atom(v) for v in p['parameters']+p['auxiliaries']}
    nd=dict(leaves)
    for n,op,a,b in p['polynomial_source']:
        get=lambda v:intern.atom(v) if type(v) is int else nd[v]
        nd[n]=intern.op(op,get(a),get(b))
        if n=='mass__bridge_input': nd[n]=intern.atom('PROVED_AFFINE_INPUT')
    ed={'x':leaves['x'],**{v:leaves['exp__'+v] for v in e['auxiliaries']}}
    for n,op,a,b in e['source'][:-1]:
        get=lambda v:intern.atom(v) if type(v) is int else ed[v]
        ed[n]=intern.op(op,get(a),get(b))
        assert ed[n]==nd['exp__'+n]
    hd={'y':leaves['y'],'T':leaves['T'],**{v:leaves['mass__'+v] for v in h['auxiliaries']}}
    hd['x']=intern.op('-',ed['Q'],intern.atom(1))
    same=0
    for n,op,a,b in h['polynomial_source']:
        get=lambda v:intern.atom(v) if type(v) is int else hd[v]
        hd[n]=intern.op(op,get(a),get(b))
        if n=='bridge_input': hd[n]=intern.atom('PROVED_AFFINE_INPUT')
        if n!='bridge_input_scaled':
            assert hd[n]==nd['mass__'+n]; same+=1
    for a,b in h['comparisons']:
        for v in (a,b):
            assert (intern.atom(v) if type(v) is int else hd[v])==(intern.atom(v) if type(v) is int else nd[rename(v,'mass__',['x','y','T'])])
    if p['finalizer']=='sos':
        res=intern.op('-',ed['factor_product_5'],intern.atom(1))
        expected=intern.op('+',intern.op('*',res,res),hd[h['output']])
    else: expected=intern.op('-',intern.op('*',ed['factor_product_5'],intern.op('+',hd[h['output']],intern.atom(1))),intern.atom(1))
    assert expected==nd[p['output']]
    return {'actual_loader_coefficients_constant_then_Q':list(oldlocal['bridge_input']),'unchanged_history_registers_after_affine_cut':same,'exponent_registers':51,'history_residuals':20,'complete_output_identity':True}

def finalizer_polynomial(packet):
    """Expand every actual finalizer gate over independent U,S indeterminates."""
    d={packet['interfaces']['exponent_unit']:{(1,0):1},packet['interfaces']['history_sos']:{(0,1):1}}
    for n,op,a,b in packet['polynomial_source'][-3:]:
        a={(0,0):a} if type(a) is int else d[a]
        b={(0,0):b} if type(b) is int else d[b]
        out={}
        if op=='*':
            for (i,j),v in a.items():
                for (k,l),w in b.items(): out[i+k,j+l]=out.get((i+k,j+l),0)+v*w
        else:
            out=dict(a)
            for key,v in b.items(): out[key]=out.get(key,0)+(v if op=='+' else -v)
        d[n]={k:v for k,v in out.items() if v}
    return d[packet['output']]

def divider96():
    rows=[['entry','L0','zero',1]]
    for i in range(96):
        rows += [[f'L{i}',f'D{i}','positive',0],[f'D{i}',f'L{i+1}' if i<95 else 'inc_B','dec',0]]
    rows += [['inc_B','back_B','inc',1],['back_B','L0','positive',1],['L0','transfer_entry','zero',0],
      ['transfer_entry','transfer_loop','zero',0],['transfer_loop','dec_B','positive',1],
      ['dec_B','inc_A','dec',1],['inc_A','back_A','inc',0],['back_A','transfer_loop','positive',0],
      ['transfer_loop','done','zero',1]]
    # Literal separated syntax in both directions: any shared source/target
    # must contain just complementary tests on one counter.
    for slot in (0,1):
        groups={}
        for r in rows: groups.setdefault(r[slot],[]).append(r)
        for group in groups.values():
            assert len(group)==1 or (len(group)==2 and {r[2] for r in group}=={'zero','positive'} and len({r[3] for r in group})==1)
    assert not any(r[1]=='entry' or r[0]=='done' for r in rows)
    states=sorted({r[i] for r in rows for i in (0,1)})
    fixtures=[]
    for x in range(1,9):
        c=[96*x,0]; q='entry'; steps=0; ticks=0
        while q!='done':
            if q.startswith('L') and q[1:].isdigit(): assert c[0]+96*c[1]+int(q[1:])==96*x
            if q=='transfer_loop': assert c[0]+c[1]==x
            enabled=[r for r in rows if r[0]==q and (r[2]=='inc' or (r[2] in ('dec','positive') and c[r[3]]>0) or (r[2]=='zero' and c[r[3]]==0))]
            assert len(enabled)==1
            _,q,op,i=enabled[0]; N=(2**c[0])*(3**c[1]); prime=(2,3)[i]
            if op=='inc': ticks+=(108+96*prime)*N+8; c[i]+=1
            elif op=='dec': ticks+=96*N+108*(N//prime)+8; c[i]-=1
            else: ticks+=192*N+8
            steps+=1
            assert steps<=198*x+4
        assert c==[x,0] and steps==198*x+4
        reverse_steps=0
        while q!='entry':
            enabled=[r for r in rows if r[1]==q and (r[2]=='dec' or (r[2] in ('inc','positive') and c[r[3]]>0) or (r[2]=='zero' and c[r[3]]==0))]
            assert len(enabled)==1
            q,_,op,i=enabled[0]
            if op=='inc': c[i]-=1
            elif op=='dec': c[i]+=1
            reverse_steps+=1
            assert reverse_steps<=steps
        assert c==[96*x,0] and reverse_steps==steps
        fixtures.append({'x':x,'source_steps':steps,'physical_ticks':str(ticks)})
    return {'states':states,'instructions':rows,'state_count':len(states),'instruction_count':len(rows),
      'entry':'entry','exit':'done','source_steps_on_96x': '198*x+4','fixtures':fixtures,
      'scope':'Source-level reversible normalization only; not compiled into the four polynomial costs.'}

def verify(root):
    e,hs=parents(root); forms=[]; rng=random.Random(9652); counts={'complete_structural_identities':0,'history_residual_identities':0,
      'whole_numeric_identities':0,'signed_cases':0,'rational_cases':0,'literal_sos_checks':0,'public_evaluations':0,'guard_rejections':0,'copy_isolation':0}
    for variant,finalizer in [(v,f) for v in VARIANTS for f in ('sos','anchor')]:
        h=hs[variant]; p=build(variant,finalizer=finalizer,root=root); proof=structural_proof(e,h,p)
        counts['complete_structural_identities']+=1; counts['history_residual_identities']+=20
        assert p['polynomial_ledger']['operations']==h['polynomial_ledger']['operations']+54
        assert p['polynomial_ledger']['M']==h['polynomial_ledger']['M']+32
        assert p['polynomial_ledger']['A']==h['polynomial_ledger']['A']+22
        assert len(p['auxiliaries'])==len(h['auxiliaries'])+12
        for i in range(24):
            vals={v:rng.randint(-2,3) if i<12 else rng.randint(1,3) for v in p['parameters']+p['auxiliaries']}
            if i>=20: vals={k:Fraction(v,2) for k,v in vals.items()}
            ev=values_of(e['source'][:-1],{'x':vals['x'],**{v:vals['exp__'+v] for v in e['auxiliaries']}})
            hv=values_of(h['polynomial_source'],{'x':ev['Q']-1,'y':vals['y'],'T':vals['T'],**{v:vals['mass__'+v] for v in h['auxiliaries']}})
            nv=values_of(p['polynomial_source'],vals)
            U=ev['factor_product_5']; S=hv[h['output']]
            expected=(U-1)**2+S if finalizer=='sos' else U*(1+S)-1
            assert nv[p['output']]==expected
            assert U*(1+S)-1-((U-1)**2+S)==(U-1)*(S-U+2)
            value=lambda v: v if type(v) is int else hv[v]
            assert hv[h['output']]==sum((value(a)-value(b))**2 for a,b in h['comparisons'])
            counts['whole_numeric_identities']+=1; counts['literal_sos_checks']+=1
            counts['signed_cases']+=i<12; counts['rational_cases']+=i>=20
            if i in (0,12):
                assert evaluate(p,vals,signed=i==0,root=root)==nv[p['output']]; counts['public_evaluations']+=1
        one={k:1 for k in p['parameters']+p['auxiliaries']}
        bads=[]
        for path,val in [('finalizer',True),('variant',True),('parameters',('x','y','T')),('output','x')]:
            q=copy.deepcopy(p);q[path]=val;bads.append(q)
        for v in (True,5.0):
            q=copy.deepcopy(p);q['polynomial_source'][51][2]=v;bads.append(q)
        for q in bads:
            try: checked(q,root=root)
            except ValueError: counts['guard_rejections']+=1
            else: raise AssertionError('packet accepted')
        for key,val in [('x',0),('y',-1),('T',-1),(p['auxiliaries'][0],0),('x',True),('x',1.0)]:
            bad=dict(one);bad[key]=val
            try: evaluate(p,bad,root=root)
            except ValueError: counts['guard_rejections']+=1
            else: raise AssertionError('domain accepted')
        q=build(variant,finalizer=finalizer,root=root);q['source'][0][2]=False;assert exact(build(variant,finalizer=finalizer,root=root),p);counts['copy_isolation']+=1
        outer=[]
        mapping=h['parent_metadata']['mapping'];K=mapping['K'];m=mapping['modulus']
        for x in (1,2,3,7,16):
            Q=1<<(96*x);n=K*(Q-1)+mapping['initial']; trace=[];ticks=0
            for _ in range(3):
                if (n-1)%K+1==mapping['halt']: break
                z,r=divmod(n-1,m); a,b=mapping['table'][r]; c,d=mapping['clocks'][r]
                trace.append(n);ticks+=c*z+d;n=a*z+b
            halted=(n-1)%K+1==mapping['halt']
            if variant=='positive3': assert not halted and (n-1)%K+1==mapping['trap']
            else:
                assert halted and (n-1)//K+1==Q
                assert ticks==(600*Q+16 if variant=='incdec' else 192*Q+8)
            outer.append({'x':x,'initial_payload':str(Q),'halted':halted,'halt_clock':str(ticks) if halted else None,
                          'source_steps':len(trace) if halted else None,'Pell_witnesses_materialized':False})
        forms.append({'variant':variant,'finalizer':finalizer,'packet':p,'proof':proof,'loaded_outer_cases':outer})
    # Integer anchor lemma finite checks include negative U; proof is independent.
    anchor=0
    for U in range(-8,9):
        for S in range(41):
            assert (U*(1+S)-1==0)==((U-1)**2+S==0)==(U==1 and S==0); anchor+=1
    # Negative/noninteger SOS would destroy this argument, so retain full SOS.
    assert 2*(1+Fraction(-1,2))-1==0
    finalizer_proofs=[]
    for variant in VARIANTS:
        chosen={f['finalizer']:f['packet'] for f in forms if f['variant']==variant}
        assert exact(chosen['sos']['polynomial_source'][:-3],chosen['anchor']['polynomial_source'][:-3])
        a=finalizer_polynomial(chosen['anchor']); b=finalizer_polynomial(chosen['sos'])
        assert a=={(1,1):1,(1,0):1,(0,0):-1}
        assert b=={(2,0):1,(1,0):-2,(0,0):1,(0,1):1}
        gap={k:a.get(k,0)-b.get(k,0) for k in a.keys()|b.keys()}
        gap={k:v for k,v in gap.items() if v}
        assert gap=={(1,1):1,(0,1):-1,(2,0):-1,(1,0):3,(0,0):-2}
        finalizer_proofs.append({'variant':variant,'anchor_minus_sos_coefficients':[[list(k),v] for k,v in sorted(gap.items())],
          'identity':'F_anchor-F_SOS=(U-1)*(S-U+2)','entire_pre_finalizer_source_equal':True})
    d=divider96()
    return {'status':'PASS_THREE_MASS_EXPONENTIAL_INPUT_BRIDGE','source_sha256':sha(Path(__file__).read_bytes()),
      'pins':PINS,'counts':dict(counts,integer_finalizer_cases=anchor,symbolic_finalizer_corrections=4,loaded_outer_cases=40,distinct_loaded_outer_cases=20,divider_cases=8),
      'forms':forms,'finalizer_comparison':finalizer_proofs,'division_prefix':d,
      'scope':'x>0 to valuations (96x,0), four fixed nonuniversal sources, unbounded existential duration. No all-r.e unary-input theorem.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
    result=verify(args.root)
    if args.expect and not exact(result,json.loads(args.expect.read_text())): raise ValueError('receipt mismatch')
    if args.output: args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'counts':result['counts'],'ledgers':{f['variant']+'_'+f['finalizer']:f['packet']['polynomial_ledger'] for f in result['forms']}},sort_keys=True))
if __name__=='__main__': main()

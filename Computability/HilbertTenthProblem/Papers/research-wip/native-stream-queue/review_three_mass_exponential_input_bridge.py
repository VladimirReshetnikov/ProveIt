#!/usr/bin/env python3
"""Independent bounded audit of eight complete exponential-input mass circuits.

No historical Python dependency executes. The candidate API is loaded from
source bytes only after all nine direct source/receipt/note hashes are checked.
"""
from __future__ import annotations
import argparse, copy, hashlib, json, random, subprocess, sys, tempfile, types
from fractions import Fraction
from pathlib import Path

if not __debug__:
    raise RuntimeError('This reviewed checker requires assertions enabled')
PINS = {
 'three_mass_exponential_input_bridge.py':'fe892d2920a866c723ad648ea52ac467d0f531c6aabe13c000f3cd53fef57ef2',
 'three_mass_exponential_input_bridge.json':'976e75fc90da362949774ee5cfae2e1b48f35bf351203825b82b3dfba7353296',
 'three_mass_exponential_input_bridge.md':'0d839b4661cad99e37c19a590e9e14840d1d2961383a111c107f2957ccd87187',
 'pell_fixed_affine_exponent52.py':'64893c621c538a8f5dba8a0fc417fd46aae7c607da996dd5f304ca13642f1486',
 'pell_fixed_affine_exponent52.json':'ebf7cafaa1f19c77c72302e5fee2e2c41c19b76a1ab72942758478ab1dd1adf1',
 'pell_fixed_affine_exponent52.md':'891301377f3740657c268e3e48f697dc5cb5a08037665aa772c1bff0d200b9ec',
 'native_pell_factored_first_coefficient.py':'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'native_pell_factored_first_coefficient.json':'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md':'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
}
VARIANTS=('incdec','zero3','nop','positive3')
def sha(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def source_data(artifact_root,parent_root):
    blobs={}
    for n,p in PINS.items():
        path=(artifact_root if n.startswith('three_mass_') else parent_root)/n
        blobs[n]=path.read_bytes()
        assert sha(blobs[n])==p, n
    return blobs

def execute(rows,assignment):
    env=dict(assignment)
    for name,op,left,right in rows:
        a=left if type(left) is int else env[left]
        b=right if type(right) is int else env[right]
        env[name]={'*':lambda:a*b,'+':lambda:a+b,'-':lambda:a-b}[op]()
    return env

def rename(v,prefix,shared): return v if type(v) is int or v in shared else prefix+v

def full_sos(rows,pairs):
    result=copy.deepcopy(rows)
    for i,(left,right) in enumerate(pairs):
        result += [[f'sos_res{i}','-',left,right],[f'sos_sq{i}','*',f'sos_res{i}',f'sos_res{i}']]
    for i in range(1,len(pairs)):
        result.append([f'sos_sum{i}','+',f'sos_sq0' if i==1 else f'sos_sum{i-1}',f'sos_sq{i}'])
    return result

def reconstruct(e,h,mode):
    assert h['polynomial_source']==full_sos(h['source'],h['comparisons'])
    out=[]
    for n,op,a,b in e['source'][:-1]: out.append(['exp__'+n,op,rename(a,'exp__',{'x'}),rename(b,'exp__',{'x'})])
    certificate=copy.deepcopy(out)
    K=h['parent_metadata']['mapping']['K']; q0=h['parent_metadata']['mapping']['initial']
    for n,op,a,b in h['polynomial_source']:
        row=['mass__'+n,op,rename(a,'mass__',{'x','y','T'}),rename(b,'mass__',{'x','y','T'})]
        if n=='bridge_input_scaled':
            assert [n,op,a,b]==[n,'*',K,'x']; row=['mass__'+n,'*',K,'exp__Q']
        if n=='bridge_input':
            assert [n,op,a,b]==[n,'+','bridge_input_scaled',q0]; row=['mass__'+n,'+','mass__bridge_input_scaled',q0-K]
        out.append(row)
        if len(certificate)<len(e['source'])-1+len(h['source']): certificate.append(row)
    U='exp__factor_product_5'; S='mass__'+h['output']
    if mode=='sos': out += [['bridge_exp_residual','-',U,1],['bridge_exp_square','*','bridge_exp_residual','bridge_exp_residual'],['bridge_output','+','bridge_exp_square',S]]
    else: out += [['bridge_sos_plus_one','+',S,1],['bridge_unit_times_sos','*',U,'bridge_sos_plus_one'],['bridge_output','-','bridge_unit_times_sos',1]]
    pairs=[[U,1]]+[[rename(a,'mass__',{'x','y','T'}),rename(b,'mass__',{'x','y','T'})] for a,b in h['comparisons']]
    return certificate,pairs,out

class DAG:
    def __init__(self): self.nodes={}
    def atom(self,v): return self.intern(('atom',type(v).__name__,v))
    def intern(self,v):
        if v not in self.nodes: self.nodes[v]=len(self.nodes)
        return self.nodes[v]
    def op(self,op,a,b): return self.intern((op,a,b))
    def walk(self,rows,env,cut=None):
        d=dict(env)
        for n,op,a,b in rows:
            d[n]=self.op(op,self.atom(a) if type(a) is int else d[a],self.atom(b) if type(b) is int else d[b])
            if cut and n in cut: d[n]=cut[n]
        return d

def proof(e,h,p):
    # Symbolic local affine coefficients: z=Q-1. Check actual operands first.
    old={r[0]:r for r in h['source']}; new={r[0]:r for r in p['source']}
    K=h['parent_metadata']['mapping']['K']; q0=h['parent_metadata']['mapping']['initial']
    assert old['bridge_input_scaled']==['bridge_input_scaled','*',K,'x']
    assert old['bridge_input']==['bridge_input','+','bridge_input_scaled',q0]
    assert new['mass__bridge_input_scaled']==['mass__bridge_input_scaled','*',K,'exp__Q']
    assert new['mass__bridge_input']==['mass__bridge_input','+','mass__bridge_input_scaled',q0-K]
    assert [r[0] for r in h['polynomial_source'] if 'x' in r[2:]]==['bridge_input_scaled']
    assert [r[0] for r in h['polynomial_source'] if 'bridge_input_scaled' in r[2:]]==['bridge_input']
    assert all('x' not in pair and 'bridge_input_scaled' not in pair for pair in h['comparisons'])
    # The equality K*Q-K+q0 = K*Q+(q0-K) is an exact affine expansion.
    old_coeff=(K,-K+q0); new_coeff=(K,q0-K); assert old_coeff==new_coeff
    d=DAG(); leaves={v:d.atom(v) for v in p['parameters']+p['auxiliaries']}
    cut=d.atom(('proved_affine_Q',old_coeff))
    nd=d.walk(p['polynomial_source'],leaves,{'mass__bridge_input':cut})
    ed=d.walk(e['source'][:-1],{'x':leaves['x'],**{v:leaves['exp__'+v] for v in e['auxiliaries']}})
    for n,_,_,_ in e['source'][:-1]: assert ed[n]==nd['exp__'+n]
    hd=d.walk(h['polynomial_source'],{'x':d.op('-',ed['Q'],d.atom(1)),'y':leaves['y'],'T':leaves['T'],**{v:leaves['mass__'+v] for v in h['auxiliaries']}},{'bridge_input':cut})
    retained=0
    for n,_,_,_ in h['polynomial_source']:
        if n!='bridge_input_scaled': assert hd[n]==nd['mass__'+n];retained+=n!='bridge_input_scaled'
    for a,b in h['comparisons']:
        for v in (a,b): assert (d.atom(v) if type(v) is int else hd[v])==(d.atom(v) if type(v) is int else nd[rename(v,'mass__',{'x','y','T'})])
    u=ed['factor_product_5']; s=hd[h['output']]
    if p['finalizer']=='sos':
        r=d.op('-',u,d.atom(1)); want=d.op('+',d.op('*',r,r),s)
    else: want=d.op('-',d.op('*',u,d.op('+',s,d.atom(1))),d.atom(1))
    assert want==nd['bridge_output']
    return {'Q_affine_coefficients':[K,q0-K],'unchanged_history_DAG_registers':retained,'retained_residuals':20,'exponent_registers':51}

def audit_ledger(rows,free,roots):
    degrees={v:1 for v in free}; table={}; nM=0
    for n,op,a,b in rows:
        assert type(n) is str and n not in degrees and op in ('+','-','*')
        assert all(type(v) is int or type(v) is str and v in degrees for v in (a,b))
        da=0 if type(a) is int else degrees[a]; db=0 if type(b) is int else degrees[b]
        degrees[n]=da+db if op=='*' else max(da,db)
        table[n]=(a,b); nM+=op=='*'
    live=set(); stack=list(roots)
    while stack:
        v=stack.pop()
        if type(v) is str and v not in live:
            live.add(v);stack.extend(table.get(v,()))
    assert set(table)<=live and set(free)<=live
    return {'operations':len(rows),'M':nM,'A':len(rows)-nM,'positive_witnesses':len(free)-3,'all_gates_live':True,'literal_degree_upper_bound':max(0 if type(v) is int else degrees[v] for v in roots)}

# An independent sparse polynomial interpreter verifies the degree54 exponent.
def p_add(a,b,sign=1):
    c=dict(a)
    for key,value in b.items(): c[key]=c.get(key,0)+sign*value
    return {k:v for k,v in c.items() if v}
def p_mul(a,b):
    c={}
    for i,u in a.items():
        for j,v in b.items():
            k=tuple(x+y for x,y in zip(i,j));c[k]=c.get(k,0)+u*v
    return {k:v for k,v in c.items() if v}
def exponent_degree(e):
    coords=['x']+e['auxiliaries']; zero=(0,)*len(coords)
    d={v:{tuple(int(i==j) for i in range(len(coords))):1} for j,v in enumerate(coords)}
    for n,op,a,b in e['source']:
        if n.startswith('factor_product_'): break
        a={zero:a} if type(a) is int else d[a]; b={zero:b} if type(b) is int else d[b]
        d[n]=p_mul(a,b) if op=='*' else p_add(a,b,1 if op=='+' else -1)
    result={n:{'exact_degree':max(map(sum,d[n])),'expanded_terms':len(d[n])} for n in ('N0','N1','Ns','N3','Nk','Nl')}
    assert [v['exact_degree'] for v in result.values()]==[5,7,14,22,3,3]
    assert sum(v['exact_degree'] for v in result.values())==54
    # Nonzero factors over Q[x,...] have additive product degree.
    return result

def sparse_finalizer(p):
    d={p['interfaces']['exponent_unit']:{(1,0):1},p['interfaces']['history_sos']:{(0,1):1}}
    for n,op,a,b in p['polynomial_source'][-3:]:
        a={(0,0):a} if type(a) is int else d[a];b={(0,0):b} if type(b) is int else d[b]
        d[n]=p_mul(a,b) if op=='*' else p_add(a,b,1 if op=='+' else -1)
    return d[p['output']]

def check_prefix(record):
    rows=record['instructions']; states={s for r in rows for s in r[:2]}
    assert len(states)==201 and len(rows)==202 and sorted(states)==record['states']
    assert all(len(r)==4 and r[2] in ('inc','dec','positive','zero') and type(r[3]) is int and r[3] in (0,1) for r in rows)
    for slot in (0,1):
        for state in states:
            group=[r for r in rows if r[slot]==state]
            assert len(group)<=2
            if len(group)==2: assert {r[2] for r in group}=={'zero','positive'} and group[0][3]==group[1][3]
    assert not any(r[1]=='entry' or r[0]=='done' for r in rows)
    fixtures=[]
    for x in (1,2,3,4,5,8,9,16):
        state='entry';c=[96*x,0];trace=[];ticks=0
        while state!='done':
            if state.startswith('L') and state[1:].isdigit(): assert c[0]+96*c[1]+int(state[1:])==96*x
            if state=='transfer_loop': assert c[0]+c[1]==x
            enabled=[r for r in rows if r[0]==state and (r[2]=='inc' or r[2] in ('dec','positive') and c[r[3]]>0 or r[2]=='zero' and c[r[3]]==0)]
            assert len(enabled)==1
            row=enabled[0]; trace.append((state,tuple(c)));_,state,op,i=row;payload=2**c[0]*3**c[1];prime=(2,3)[i]
            if op=='inc': ticks+=(108+96*prime)*payload+8;c[i]+=1
            elif op=='dec': ticks+=96*payload+108*(payload//prime)+8;c[i]-=1
            else: ticks+=192*payload+8
            assert len(trace)<=198*x+4
        assert c==[x,0] and len(trace)==198*x+4
        for oldstate,oldc in reversed(trace):
            enabled=[r for r in rows if r[1]==state and (r[2]=='dec' or r[2] in ('inc','positive') and c[r[3]]>0 or r[2]=='zero' and c[r[3]]==0)]
            assert len(enabled)==1
            state,_,op,i=enabled[0]
            if op=='inc': c[i]-=1
            elif op=='dec': c[i]+=1
            assert state==oldstate and tuple(c)==oldc
        fixtures.append({'x':x,'steps':len(trace),'physical_ticks_sha256':sha(str(ticks).encode())})
    return {'states':201,'instructions':202,'forward_inverse_cases':len(fixtures),'fixtures':fixtures,'included_in_eight_circuit_costs':False}

def verify(artifact_root,parent_root):
    blobs=source_data(artifact_root,parent_root)
    module=types.ModuleType('independent_candidate_api');module.__file__=str(artifact_root/'three_mass_exponential_input_bridge.py')
    exec(compile(blobs['three_mass_exponential_input_bridge.py'],module.__file__,'exec'),module.__dict__)
    e=json.loads(blobs['pell_fixed_affine_exponent52.json']);n=json.loads(blobs['native_pell_factored_first_coefficient.json']);receipt=json.loads(blobs['three_mass_exponential_input_bridge.json'])
    hs={f['variant'][6:]:f['packet'] for f in n['forms'] if f['variant'].startswith('clock_')}
    assert receipt['source_sha256']==PINS['three_mass_exponential_input_bridge.py'] and len(receipt['forms'])==8
    rng=random.Random(2026100396); forms=[]; counts={'literal_full_sources':0,'full_DAG_identities':0,'residual_DAG_identities':0,'full_numeric_identities':0,'signed_cases':0,'rational_cases':0,'residual_value_checks':0,'literal_SOS_checks':0,'public_evaluations':0,'guard_rejections':0,'defensive_copies':0,'loaded_table_cases':0,'positive_pretyping_bounds':0}
    bymode={}
    for f in receipt['forms']:
        p=f['packet'];v=f['variant'];mode=f['finalizer'];h=hs[v]
        assert v in VARIANTS and mode in ('sos','anchor') and p['variant']==v and p['finalizer']==mode
        assert exact(p,module.build(v,finalizer=mode,root=parent_root))
        assert p['parameters']==['x','y','T'] and p['auxiliaries']==['exp__'+a for a in e['auxiliaries']]+['mass__'+a for a in h['auxiliaries']]
        assert p['domains']=={'x':'positive integer','y':'natural integer','T':'natural integer','auxiliaries':'positive integers'}
        cs,cp,ps=reconstruct(e,h,mode);assert p['source']==cs and p['comparisons']==cp and p['polynomial_source']==ps
        counts['literal_full_sources']+=1
        pr=proof(e,h,p);counts['full_DAG_identities']+=1;counts['residual_DAG_identities']+=20
        cert=audit_ledger(cs,p['parameters']+p['auxiliaries'],sum(cp,[]));pol=audit_ledger(ps,p['parameters']+p['auxiliaries'],[p['output']])
        assert exact(cert,p['certificate_ledger'])
        refined=max(108,h['degree']['upper_bound']) if mode=='sos' else 54+h['degree']['upper_bound']
        pol['refined_degree_upper_bound']=refined;assert exact(pol,p['polynomial_ledger'])
        assert p['degree']['exact_degree_claimed'] is False and p['degree']['upper_bound']==refined
        assert [pol[k]-h['polynomial_ledger'][k] for k in ('operations','M','A')]==[54,32,22]
        assert len(p['auxiliaries'])-len(h['auxiliaries'])==12
        bymode[v,mode]=sparse_finalizer(p)
        for case in range(20):
            values={k:rng.randint(-2,3) if case<10 else rng.randint(1,3) for k in p['parameters']+p['auxiliaries']}
            if case>=18: values={k:Fraction(x,3) for k,x in values.items()}
            ev=execute(e['source'][:-1],{'x':values['x'],**{a:values['exp__'+a] for a in e['auxiliaries']}})
            hv=execute(h['polynomial_source'],{'x':ev['Q']-1,'y':values['y'],'T':values['T'],**{a:values['mass__'+a] for a in h['auxiliaries']}})
            nv=execute(ps,values);U=ev['factor_product_5'];S=hv[h['output']]
            val=lambda x:x if type(x) is int else hv[x]
            assert S==sum((val(a)-val(b))**2 for a,b in h['comparisons']);counts['literal_SOS_checks']+=1
            assert nv[p['output']]==((U-1)**2+S if mode=='sos' else U*(1+S)-1)
            counts['full_numeric_identities']+=1;counts['signed_cases']+=case<10;counts['rational_cases']+=case>=18
            for a,b in h['comparisons']:
                child=lambda x:x if type(x) is int else nv[rename(x,'mass__',{'x','y','T'})]
                assert val(a)-val(b)==child(a)-child(b);counts['residual_value_checks']+=1
            if case in (0,10):
                assert module.evaluate(p,values,signed=case==0,root=parent_root)==nv[p['output']];counts['public_evaluations']+=1
            if 10<=case<18: assert ev['Q']>=49 and ev['Q']-1>=0;counts['positive_pretyping_bounds']+=1
        bads=[]
        for key,value in [('variant',True),('variant','missing'),('finalizer',True),('finalizer','bad'),('output','x'),('parameters',tuple(p['parameters']))]:
            q=copy.deepcopy(p);q[key]=value;bads.append(q)
        for field in ('source','polynomial_source'):
            for value in (True,48.0,49):
                q=copy.deepcopy(p);q[field][0][2]=value;bads.append(q)
        for path,value in [('operations',float(pol['operations'])),('all_gates_live',1),('refined_degree_upper_bound',False)]:
            q=copy.deepcopy(p);q['polynomial_ledger'][path]=value;bads.append(q)
        q=copy.deepcopy(p);q['comparisons']=q['comparisons'][1:];bads.append(q)
        for q in bads:
            try: module.checked(q,root=parent_root)
            except ValueError: counts['guard_rejections']+=1
            else: raise AssertionError('mutated packet accepted')
        one={k:1 for k in p['parameters']+p['auxiliaries']}
        assignments=[]
        for k,value in [('x',0),('x',-1),('x',True),('x',1.0),('y',-1),('T',-1),(p['auxiliaries'][0],0),(p['auxiliaries'][0],False)]:
            q=dict(one);q[k]=value;assignments.append((q,False))
        q=dict(one);q['extra']=1;assignments.append((q,False))
        q=dict(one);del q['T'];assignments.append((q,False))
        assignments += [(one,1),(one,None)]
        for values,signed in assignments:
            try: module.evaluate(p,values,signed=signed,root=parent_root)
            except ValueError: counts['guard_rejections']+=1
            else: raise AssertionError('invalid assignment accepted')
        natural=dict(one,y=0,T=0);assert module.evaluate(p,natural,root=parent_root)==execute(ps,natural)[p['output']];counts['public_evaluations']+=1
        for field in ('source','polynomial_source','comparisons','auxiliaries'):
            q=module.build(v,finalizer=mode,root=parent_root);q[field].clear();assert exact(module.build(v,finalizer=mode,root=parent_root),p);counts['defensive_copies']+=1
        # Direct finite source table run at six independently chosen large inputs.
        mapping=h['parent_metadata']['mapping'];K=mapping['K'];m=mapping['modulus'];cases=[]
        for x in (1,2,4,9,17,33):
            Q=1<<(96*x);n=K*(Q-1)+mapping['initial'];ticks=0;steps=0
            while (n-1)%K+1 not in (mapping['halt'],mapping['trap']):
                quotient,residue=divmod(n-1,m);a,b=mapping['table'][residue];c,d=mapping['clocks'][residue]
                n=a*quotient+b;ticks+=c*quotient+d;steps+=1;assert steps<=3
            halt=(n-1)%K+1==mapping['halt'];assert halt==(v!='positive3')
            if halt:
                assert (n-1)//K+1==Q and ticks==(600*Q+16 if v=='incdec' else 192*Q+8)
            cases.append({'x':x,'halted':halt,'steps':steps,'payload_sha256':sha(str(Q).encode())});counts['loaded_table_cases']+=1
        forms.append({'variant':v,'finalizer':mode,'certificate_ledger':cert,'polynomial_ledger':pol,'proof':pr,'loaded_table_cases':cases})
    for v in VARIANTS:
        assert bymode[v,'sos']=={(2,0):1,(1,0):-2,(0,0):1,(0,1):1}
        assert bymode[v,'anchor']=={(1,1):1,(1,0):1,(0,0):-1}
        correction=p_mul({(1,0):1,(0,0):-1},{(0,1):1,(1,0):-1,(0,0):2})
        assert p_add(bymode[v,'anchor'],bymode[v,'sos'],-1)==correction
    counts['symbolic_finalizer_corrections']=4
    counts['integer_finalizer_cases']=0
    for U in range(-12,13):
        for S in range(51):
            assert (U*(1+S)-1==0)==((U-1)**2+S==0)==(U==1 and S==0)
            counts['integer_finalizer_cases']+=1
    # The anchor equivalence needs integer U even if S is nonnegative:
    assert Fraction(1,2)*(1+1)-1==0 and (Fraction(1,2)-1)**2+1!=0
    counts['nonnegative_rational_anchor_counterexamples']=1
    with tempfile.TemporaryDirectory(prefix='review_mass_bridge_pins_') as tmp:
        root=Path(tmp)
        for name in PINS:
            if not name.startswith('three_mass_'): (root/name).write_bytes(blobs[name])
        module.build(root=root)
        counts['warm_pin_rejections']=0
        for name in module.PINS:
            (root/name).write_bytes(blobs[name]+b'\n')
            try: module.build(root=root)
            except ValueError: counts['warm_pin_rejections']+=1
            else: raise AssertionError('changed dependency accepted')
            (root/name).write_bytes(blobs[name])
    for kwargs in ({'variant':1},{'variant':'bad'},{'finalizer':False},{'finalizer':'bad'}):
        try: module.build(root=parent_root,**kwargs)
        except ValueError: counts['guard_rejections']+=1
        else: raise AssertionError('bad selector accepted')
    proc=subprocess.run([sys.executable,'-O',str(artifact_root/'three_mass_exponential_input_bridge.py'),'--root',str(parent_root)],capture_output=True,text=True)
    assert proc.returncode!=0 and 'run without -O' in proc.stderr
    counts['optimized_mode_rejections']=1
    return {'status':'PASS_INDEPENDENT_THREE_MASS_EXPONENTIAL_INPUT_BRIDGE','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'counts':counts,'forms':forms,'exponent_factor_degree_expansions':exponent_degree(e),'divider_prefix':check_prefix(receipt['division_prefix']),'scope':'Eight full literal sources and same inherited natural/positive zero relation for the four fixed exponential-input sources. No new universal unary-input theorem; no full Pell witnesses materialized; prefix uncompiled and excluded from costs.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
    r=verify(args.artifacts.resolve(),args.root.resolve())
    if args.expect: assert exact(r,json.loads(args.expect.read_text())),'receipt mismatch'
    if args.output: args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':r['status'],'counts':r['counts']},sort_keys=True))
if __name__=='__main__':main()

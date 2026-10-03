#!/usr/bin/env python3
"""Four bounded literal direct clean-clock compositions; no historical Python."""
import argparse, copy, hashlib, json
from collections import Counter
from fractions import Fraction
from pathlib import Path

if not __debug__:
    raise RuntimeError('This checker requires Python assertions.')
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
REPORT='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/'
PINS = {'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_target_free_height.md': 'f0bd6c2011ca1aa0dd5e6dbaaea7907d35f13f4dd756fc2786528c80f60f75ff', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.json': 'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.md': '8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.py': '96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/20-event-budget-PROOF.md': 'd74157254a36e53c1568cea383cdcc46dd73adca48a1a9a7eee4e46b51b73922', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/15-clean-targets-CLEAN-TARGET-THEOREM.md': '3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-FOLDED-ADDENDUM.md': '1ce912386db479f63eed0d05f2a7d79649b4d8a03b91bf2080338f1cafaafde8', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-THEOREM.md': '93bf673898816aed526ef943160a9d3dfb950cedc3bf0f59d6ae4d78c7add11d'}
PARENT=WIP+'three_mass_target_free_height.json'
VARIANTS=('clock_incdec','clock_zero3','clock_nop','clock_positive3')
EXPECTED=(597,472,470,473)


def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def authenticated(repo):
    blobs={}
    for path,digest in PINS.items():
        b=(repo/path).read_bytes()
        assert sha(b)==digest, ('dependency pin',path)
        blobs[path]=b
    d=json.loads(blobs[PARENT])
    # All twelve transitive source/receipt/proof pins remain checked as data.
    for path,digest in d['parent_pins'].items():
        assert PINS[WIP+path]==digest
    return d

def finalize(pairs,prefix):
    rows=[]
    for i,(a,b) in enumerate(pairs):
        r=f'{prefix}res{i}';s=f'{prefix}sq{i}'
        rows += [[r,'-',a,b],[s,'*',r,r]]
    out=f'{prefix}sq0'
    for i in range(1,len(pairs)):
        nxt=f'{prefix}sum{i}';rows.append([nxt,'+',out,f'{prefix}sq{i}']);out=nxt
    return rows,out

def rename(value): return {'y':'clean_final_payload','T':'U'}.get(value,value) if type(value) is str else value

def emit(parent):
    assert parent['parameters']==['x','y','T']
    assert parent['domains']=={'parameters':'natural','auxiliaries':'positive'}
    assert len(parent['comparisons'])==19
    oldtail,oldout=finalize(parent['comparisons'],'ep_')
    assert parent['polynomial_source']==parent['source']+oldtail and parent['output']==oldout
    old=parent['source']; mp=parent['mapping'];m=mp['modulus']
    assert m==30 and mp['K']==5 and mp['initial']==1
    assert mp['halt'] in (2,3)
    times=[r for r in old if 'T' in r[2:]]
    assert times==[[parent['interfaces']['height'],'+','bridge_height_without_time','T'],old[-1]]
    assert old[-1][1:] == ['+',old[-2][0],'T']
    assert old[-2][1:] == ['*',old[-2][2],old[-3][0]]
    assert old[-3][1:]==['-','clock_quotient_hat',1]
    assert parent['comparisons'][-1]==[old[-4][0],old[-1][0]]
    radix=[r for r in old if r[1:] == ['*',131072,'bridge_height_square']]
    assert len(radix)==1
    # Height-two proof: L <= (4768m+2308)h^2. Leave >=2h^2 gap.
    minimum=max(radix[0][2],4768*m+2310)
    C=1 << (minimum-1).bit_length()
    assert C==262144
    core=[[n,op,rename(a),rename(b)] for n,op,a,b in old]
    for r in core:
        if r[0]==radix[0][0]: r[2]=C
    adjusted_pairs=[[rename(a),rename(b)] for a,b in parent['comparisons']]
    clock=adjusted_pairs[-1][0]
    bridge=[['clean_payload_sum','+','x','clean_final_payload'],
            ['clean_payload_ticks','*',192,'clean_payload_sum'],
            ['clean_double_clock_word','*',2,clock],
            ['clean_sum','+','clean_double_clock_word','clean_payload_ticks'],
            ['clean_clock_word','+','clean_sum',208]]
    comparisons=copy.deepcopy(adjusted_pairs); comparisons[-1][0]='clean_clock_word'
    tail,out=finalize(comparisons,'clean_')
    packet={'variant':parent['variant'],'parameters':['x','U'],
            'auxiliaries':parent['auxiliaries']+['clean_final_payload'],
            'domains':{'parameters':'natural','auxiliaries':'positive'},
            'mapping':copy.deepcopy(mp),'source':core+bridge,'comparisons':comparisons,
            'polynomial_source':core+bridge+tail,'output':out,
            'interfaces':copy.deepcopy(parent['interfaces']),
            'radix_multiplier':C,'radix_minimum':minimum,
            'parent_source_sha256':sha(canonical(old)),
            'scope':'Four fixed nonuniversal raw-input first-clean-target clocks; no universal loader or parent zero-tuple bijection.'}
    return packet,core,adjusted_pairs

def audit_graph(packet):
    rows=packet['polynomial_source'];ports=packet['parameters']+packet['auxiliaries']
    assert len(ports)==len(set(ports))
    seen=set(ports);deps={};deg={n:1 for n in ports};top={n:i+2 for i,n in enumerate(ports)}
    modulus=1000003;trace=[];counts=Counter()
    def degree(x): return 0 if type(x) is int else deg[x]
    def leading(x): return x%modulus if type(x) is int else top[x]
    for n,op,a,b in rows:
        assert type(n)is str and n not in seen and op in ('+','-','*')
        assert all(type(x)is int or type(x)is str and x in seen for x in (a,b))
        da,db=degree(a),degree(b);la,lb=leading(a),leading(b)
        d=da+db if op=='*' else max(da,db)
        c=la*lb if op=='*' else (la if da==d else 0)+(1 if op=='+' else -1)*(lb if db==d else 0)
        seen.add(n);deps[n]=[x for x in (a,b) if type(x)is str];deg[n]=d;top[n]=c%modulus
        trace.append([n,d,top[n]]);counts['M' if op=='*' else 'A']+=1
    live={packet['output']}
    for n,op,a,b in reversed(rows):
        if n in live: live.update(deps[n])
    assert live==seen
    tail,out=finalize(packet['comparisons'],'clean_')
    assert rows==packet['source']+tail and packet['output']==out
    assert top[out]!=0
    return {'M':counts['M'],'A':counts['A'],'operations':len(rows),
            'positive_witnesses':len(packet['auxiliaries']),'comparisons':len(packet['comparisons']),
            'exact_degree':deg[out],'modulus':modulus,'specialized_leading_coefficient':top[out],
            'degree_trace_sha256':sha(canonical(trace)),'all_gates_and_ports_live':True}

def run(rows,values):
    e=values.copy()
    get=lambda x:x if type(x)is int else e[x]
    for n,op,a,b in rows:
        x,y=get(a),get(b);e[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return e

def algebra(packet,adjusted_core,adjusted_pairs):
    # Exact formal bridge coefficients on independent Ctau,x,F indeterminates.
    expected=[208,2,192,192]
    env={adjusted_pairs[-1][0]:[0,1,0,0],'x':[0,0,1,0],'clean_final_payload':[0,0,0,1]}
    get=lambda x:[x,0,0,0] if type(x)is int else env[x]
    for n,op,a,b in packet['source'][-5:]:
        x,y=get(a),get(b)
        if op=='*':
            assert not any(x[1:]) or not any(y[1:])
            env[n]=[x[0]*v for v in y] if not any(x[1:]) else [y[0]*v for v in x]
        else: env[n]=[u+(v if op=='+' else -v) for u,v in zip(x,y)]
    assert env['clean_clock_word']==expected
    # All retained rows agree literally after just the explicit name/constant edits.
    assert packet['source'][:-5]==adjusted_core
    assert packet['comparisons'][:-1]==adjusted_pairs[:-1]
    assert packet['comparisons'][-1][1]==adjusted_pairs[-1][1]
    tail,out=finalize(adjusted_pairs,'ep_')
    count=0
    for i in range(12):
        ports=packet['parameters']+packet['auxiliaries']
        values={n:(j*3+i*5)%7-3 for j,n in enumerate(ports)}
        if i>=8: values={n:Fraction(v,2) for n,v in values.items()}
        e=run(packet['polynomial_source'],values);a=run(adjusted_core+tail,values)
        oldleft,right=adjusted_pairs[-1];newleft=packet['comparisons'][-1][0]
        assert e[newleft]==2*e[oldleft]+192*(values['x']+values['clean_final_payload'])+208
        assert e[packet['output']]==a[out]-(a[oldleft]-a[right])**2+(e[newleft]-e[right])**2
        assert e[packet['output']]==sum((e[x]-e[y])**2 for x,y in packet['comparisons'])
        count+=1
    return {'full_signed_corrections':count,'rational_corrections':4,
            'retained_comparisons':18,'formal_bridge_coefficients_Ctau_x_F':expected,
            'whole_identity':'Q=adjusted_parent-(Ctau-rhs)^2+(2*Ctau+192*(x+F)+208-rhs)^2',
            'adjusted_parent_is_original_parent':False}

def check_literal_mapping(packet):
    mp=packet['mapping'];K=mp['K'];m=mp['modulus'];v=packet['variant']
    assert set(mp['codes'])==({'s','a','h'} if v=='clock_incdec' else {'s','h'})
    assert mp['codes']['s']==1 and mp['codes']['h']==mp['halt'] and mp['trap']==len(mp['codes'])+1
    # Every guard depends only on N modulo 2 or 3, constant on each 30-residue
    # encoded-state class; both next-state and physical time are affine in q.
    for s in range(1,m+1):
        code=(s-1)%K+1;offset=(s-code)//K+1
        outputs=[];durations=[]
        for q in (0,1):
            N=6*q+offset;N1=N;nextcode=mp['trap'];duration=192*N+8
            if v=='clock_incdec':
                if code==1:N1=2*N;nextcode=2;duration=300*N+8
                elif code==2 and N%2==0:N1=N//2;nextcode=3;duration=150*N+8
            elif code==1:
                enabled=v=='clock_nop' or v=='clock_zero3' and N%3!=0 or v=='clock_positive3' and N%3==0
                if enabled:nextcode=2
            outputs.append(K*(N1-1)+nextcode);durations.append(duration)
        assert mp['table'][s-1]==[outputs[1]-outputs[0],outputs[0]]
        assert mp['clocks'][s-1]==[durations[1]-durations[0],durations[0]]
    return m

def trace_source(packet,x):
    # Literal residue table, with independent physical tick checks per fixture.
    mp=packet['mapping'];m=mp['modulus'];K=mp['K'];n=K*x+mp['initial'];path=[n];ticks=[];qs=[];rs=[]
    for _ in range(4):
        q,r=divmod(n-1,m);a,d=mp['table'][r];c,b=mp['clocks'][r]
        qs.append(q);rs.append(r);ticks.append(c*q+b);n=a*q+d;path.append(n)
        state=(n-1)%K+1
        if state==mp['trap']: return None
        if state==mp['halt']:break
    else: raise AssertionError('fixture did not terminate within its literal bound')
    y=(n-mp['halt'])//K+1;N=x+1
    assert y==N
    theta=sum(ticks)
    assert theta==(600*N+16 if packet['variant']=='clock_incdec' else 192*N+8)
    return path,qs,rs,ticks,y,theta

def outer(packet,x,larger=False):
    result=trace_source(packet,x)
    if result is None:return None
    path,qs,rs,ticks,F,theta=result;mp=packet['mapping'];m=mp['modulus']
    U=2*theta+192*(F+x)+208
    assert U==(1584*(x+1)+48 if packet['variant']=='clock_incdec' else 768*(x+1)+32)
    h=1
    while h<=max(path[0]+U,*qs):h*=2
    if larger:h*=2
    B=packet['radix_multiplier']*h*h;t=len(qs);P=B**t;J=sum(B**i for i in range(t))
    pack=lambda vs:sum(v*B**i for i,v in enumerate(vs))
    E=[pack([int(r==s) for r in rs]) for s in range(m)];W=pack(qs)
    baseline=min(a for a,d in mp['table']);classes=sorted({a for a,d in mp['table']}-{baseline})
    Z=[pack([q if mp['table'][r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
    Ctau=pack(ticks);assert (Ctau-theta)%(B-1)==0
    values={n:1 for n in packet['auxiliaries']}
    values.update(x=x,U=U,clean_final_payload=F,height_slack=h-path[0]-U,
                  quotient_hat=W+1,global_slack=P-J-W-1-sum(Z)-len(Z),
                  clock_quotient_hat=1+2*(Ctau-theta)//(B-1))
    values.update({f'edge{s}_hat':v+1 for s,v in enumerate(E)})
    values.update({f'product{s}_hat':v+1 for s,v in enumerate(Z)})
    assert all(values[n]>0 for n in packet['auxiliaries'])
    e=run(packet['source'],values)
    for i in (0,1,18):
        a,b=packet['comparisons'][i];assert e[a]==e[b]
    H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;A=(e['native__F3']-8)//16
    assert H&M==A
    assert e[packet['interfaces']['height']]==h and e[packet['interfaces']['target']]==path[-1]
    assert U<=4768*m*h*h+4608*h+16 <= (4768*m+2308)*h*h < B-1
    assert U<h and e['clean_clock_word']>=U
    # A fabricated wrap has the same congruence, but violates the paid height range.
    assert U+B-1>=h
    # With all other coordinates fixed, either clean-time mutation breaks the clock row.
    for delta in (-1,1):
        v=values.copy();v['U']+=delta;z=run(packet['source'],v)
        a,b=packet['comparisons'][-1];assert z[a]!=z[b]
    return {'x':x,'U':U,'final_payload':F,'native_time':theta,'steps':t,'height':h,
            'clock_quotient_hat':values['clock_quotient_hat'],'larger_height':larger,
            'genuine_outer_AND':True,'native_Pell_witnesses_materialized':False}

def verify(repo):
    parent=authenticated(repo);forms=[];counts=Counter()
    for index,form in enumerate(parent['forms']):
        p=form['packet'];assert p['variant']==VARIANTS[index]
        child,core,pairs=emit(p);ledger=audit_graph(child)
        assert ledger['operations']==EXPECTED[index]
        assert ledger['M']==p['polynomial_ledger']['M']+2 and ledger['A']==p['polynomial_ledger']['A']+3
        assert ledger['positive_witnesses']==len(p['auxiliaries'])+1 and ledger['comparisons']==19
        assert ledger['exact_degree']==p['degree']['upper_bound']
        counts['exact_residue_map_and_clock_rows']+=check_literal_mapping(child)
        proof=algebra(child,core,pairs)
        fixtures=[]
        for x in list(range(12))+[40,100]:
            for larger in (False,True):
                f=outer(child,x,larger)
                if f is not None:fixtures.append(f)
        # General h>=2 coefficient identity supporting the uniform clock bound.
        # 2308h²−4608h−16 = (h−2)(2308h+8).
        assert [2308,-4608,-16]==[2308,8-4616,-16]
        for h in (2,3,4,8,128):
            assert 2308*h*h-4608*h-16==(h-2)*(2308*h+8)>=0
            assert child['radix_multiplier']*h*h-1-(4768*30+2308)*h*h>=2*h*h-1
        child['ledger']=ledger
        forms.append({'packet':child,'algebra':proof,'outer_fixtures':fixtures})
        counts['complete_sources']+=1;counts['full_gates']+=ledger['operations']
        counts['full_signed_corrections']+=12;counts['rational_corrections']+=4
        counts['genuine_outer_fixtures']+=len(fixtures);counts['clock_mutation_rejections']+=2*len(fixtures)
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'dependency_pins':copy.deepcopy(PINS),
            'scope':'Constructive four-source clean-clock composition; independent intake is in companion note. No historical Python, numerical universal table or native Pell witness materialization.',
            'counts':dict(counts),'forms':forms}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True)
    g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=ap.parse_args();d=verify(a.repo.resolve());serialized=json.dumps(d,sort_keys=True,indent=2)+'\n'
    assert exact(d,json.loads(serialized))
    if a.output:a.output.write_text(serialized)
    else:assert exact(d,json.loads(a.expect.read_text())),'saved receipt mismatch'
    print(json.dumps({'status':'PASS',**d['counts']},sort_keys=True))
if __name__=='__main__':main()

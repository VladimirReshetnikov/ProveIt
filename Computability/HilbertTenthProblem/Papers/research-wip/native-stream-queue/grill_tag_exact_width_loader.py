#!/usr/bin/env python3
"""Paid canonical-width E-block loader and one complete fixed-program composition.

A source-pinned research emitter, not a new ordinary-input universal program.
Only Python integer arithmetic is used by this file; the pinned history builder
has its documented local dependencies, including SymPy. See companion proof.
"""
if not __debug__:
    raise RuntimeError('Run without -O')
import argparse, copy, hashlib, json, random, sys, types
from collections import Counter
from pathlib import Path
PINS={
 'grill_tag_native_composed205.py':'4084a58d5cf30694a8717c26d0abdf2aecc2fa6a7099d9815f35521005afab94',
 'grill_tag_halt_bridge.py':'3984312d5a5d9c8ebfde557e683e32bcba7fc69dbf65cfe1a9037803eebdb892',
 'grill_tag_native_word_closure.py':'80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7',
 'native_binary_input_dilation130.py':'7e7ccb297083ffb799775d729b81ec0e403981f287af62513338c5d366fb9ac2',
 'native_binary_input_dilation130.json':'175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182',
 'gpcp_fixed_program_input_bridge.py':'0d5023b52a5ffe87f5c9e26b436048571e75ccbebfd18c62f9820729b10b74f0'}
def need(p,s):
    if not p:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a)is not type(b):return False
    if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a)in(tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def normalize(a):return json.loads(json.dumps(a))
def authenticate(root):
    root=Path(root).resolve()
    for name,digest in PINS.items():need(sha((root/name).read_bytes())==digest,'Pinned dependency '+name)
    return root
def load(root,name):
    data=(root/name).read_bytes();need(sha(data)==PINS[name],'Pinned executed source')
    module=types.ModuleType('_exact_width_'+Path(name).stem);module.__file__=str(root/name)
    exec(compile(data,str(root/name),'exec'),module.__dict__);return module

def count(source):
    c=Counter(o for n,o,a,b in source)
    return dict(total=len(source),M=c['*'],A=c['+']+c['-'])
def execute(source,values):
    e=dict(values)
    for n,o,a,b in source:
        need(n not in e and o in ('+','-','*'),'SSA operation')
        a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
        e[n]=a*b if o=='*' else a+b if o=='+' else a-b
    return e
def at(env,x):return env[x] if type(x)is str else x
def renamed(rows,fn):return [[fn(n),o,fn(a),fn(b)] for n,o,a,b in rows]
def pairs_renamed(pairs,fn):return [[fn(a),fn(b)] for a,b in pairs]
def power_chain(width):
    need(type(width)is int and width>=4,'Fixed integral width >=4')
    exponent=1;name='q';rows=[]
    for bit in bin(width)[3:]:
        exponent*=2;n='Q' if exponent==width else 'width_power'+str(exponent)
        rows.append([n,'*',name,name]);name=n
        if bit=='1':
            exponent+=1;n='Q' if exponent==width else 'width_power'+str(exponent)
            rows.append([n,'*',name,'q']);name=n
    need(name=='Q' and len(rows)==width.bit_length()+width.bit_count()-2,'Literal binary chain')
    return rows

def constants(N):
    need(type(N)is int and N>=3,'At least two input symbols and separate halt symbol')
    a=28*(N+1);b=7*a;K=1<<b;D=1<<14
    gval=lambda r:2*((1<<(2*r))-1)//3
    A=(1<<7)*(gval(a-3)+(1<<(2*a-5))*gval(7)+(1<<(2*a+10))*gval(a-4))
    return dict(N=N,a=a,width=b,K=K,D=D,A=A,M=K-1,C=A*(K-1)*(D-1))

def loader(root,N,*,width_port='initial_width'):
    """Complete fixed-width recoder+3 comparisons. Width port is a supplied port.

    Input x>0 is explicitly transformed to u=x+1. Outputs are encoded_X and
    initial_width. To compose, alias width_port to the native computed P0.
    No positivity is claimed for a computed difference Q-X off the zero set.
    """
    root=authenticate(root);need(type(width_port)is str,'Width port name')
    c=constants(N);old=json.loads((root/'native_binary_input_dilation130.json').read_text())['certificate']
    need(old['source'][:3]==[['q2','*','q','q'],['Q','*','q2','q2'],['B','*',8,'Q']],'Canonical inline recoder prefix')
    need({n for n,o,a,b in old['source'] if 'q2'in(a,b)}=={'Q'},'Power chain privacy')
    chain=power_chain(c['width']);raw=chain+[['B','*',1<<(c['width']-1),'Q']]+old['source'][3:]
    def f(v):return ('input_u' if v=='x' else 'spread_R' if v=='z' else 'rec__'+v) if type(v)is str else v
    rows=[['input_u','+','x',1]]+renamed(raw,f)
    rows += [['canonical_left','+','rec__input_slack','canonical_beta'],['canonical_right','+','input_u',1],
             ['encoded_scaled','*',c['M'],'encoded_X'],['encoded_power','*',c['A'],'rec__Q'],
             ['encoded_spread','*',c['C'],'spread_R'],['encoded_sum','+','encoded_power','encoded_spread'],
             ['encoded_right','-','encoded_sum',c['A']]]
    pairs=pairs_renamed(old['comparisons'],f)+[['canonical_left','canonical_right'],['encoded_scaled','encoded_right'],[width_port,'rec__Q']]
    aux=[f(v) for v in old['auxiliaries']]+['spread_R','canonical_beta']
    need(len(rows)==136+len(chain) and count(rows)==dict(total=136+len(chain),M=68+len(chain),A=68),'Paid interface prefix')
    need(len(pairs)==37 and len(aux)==51,'Complete recoder/binding domains')
    return dict(source=rows,comparisons=pairs,auxiliaries=aux,parameters=['x','encoded_X',width_port],
                constants=c,chain_length=len(chain),certificate=count(rows),scope='Exact E numeral and exact canonical width for binary(x+1), least-significant-first; positive supplied output ports.')

def audit(rows,parameters,aux,output):
    names=parameters+aux;need(len(set(names))==len(names),'Distinct complete coordinates')
    known=set(names);degree={n:1 for n in names}
    for n,o,a,b in rows:
        need(type(n)is str and n not in known and o in ('+','-','*'),'Unique valid operation')
        need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Closed topological source')
        da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0
        degree[n]=da+db if o=='*' else max(da,db);known.add(n)
    live={output}
    for n,o,a,b in reversed(rows):
        need(n in live,'Dead emitted gate '+n);live.update(v for v in(a,b) if type(v)is str)
    need(set(names)<=live,'Unused complete coordinate')
    return degree[output]

def finalizer(source,pairs,unit):
    rows=[r[:] for r in source];last=None
    for i,(a,b) in enumerate(pairs):
        r='final_res'+str(i);q='final_sq'+str(i)
        rows += [[r,'-',a,b],[q,'*',r,r]]
        if last is None:last=q
        else:n='final_sum'+str(i);rows.append([n,'+',last,q]);last=n
    rows += [['final_positive','+',last,1],['final_product','*',unit,'final_positive'],['final_output','-','final_product',1]]
    return rows,'final_output'

def compose(root,native,N):
    """Internal composition from the authenticated builder packet in verify()."""
    need(type(native)is dict and native['unit_product']is True,'Selected actual native unit form')
    def f(v):return 'encoded_X' if v=='x' else 'hist__'+v if type(v)is str else v
    H=renamed(native['source'],f);HP=pairs_renamed(native['comparisons'],f);unit=f(native['unit_register'])
    need(HP[-1]==[unit,1] and sum(pair==[unit,1] for pair in HP)==1,'One existing native integer unit anchor')
    L=loader(root,N,width_port=f(native['interfaces']['P0']))
    source=L['source']+H;pairs=HP[:-1]+L['comparisons'];rows,out=finalizer(source,pairs,unit)
    aux=['encoded_X']+[f(v) for v in native['auxiliaries']]+L['auxiliaries']
    degree=audit(rows,['x'],aux,out)
    old_count=count(native['polynomial_source']);new_count=count(rows);increment={k:new_count[k]-old_count[k] for k in new_count}
    need(increment==dict(total=247+L['chain_length'],M=105+L['chain_length'],A=142),'Complete finalizer adjustment')
    return dict(source=source,comparisons=pairs+[[unit,1]],polynomial_source=rows,output=out,unit_register=unit,
                parameters=['x'],auxiliaries=aux,certificate=count(source),polynomial=count(rows),degree_upper=degree,
                native_polynomial=old_count,increment=increment,loader=L,
                native_comparison_count=len(HP),native_witnesses=len(native['auxiliaries']),
                scope='Complete fixed corrected Grill program on exact E(binary(x+1)); no external horizon. This measured source table is nonuniversal. The native unit finalizer includes every loader residual.')

def outer(root,N,x):
    need(type(x)is int and x>0,'Positive ordinary x');H=load(root,'grill_tag_halt_bridge.py');c=constants(N)
    u=x+1;n=u.bit_length();q=1<<n;Q=q**c['width'];B=(1<<(c['width']-1))*Q;P=B**n
    J=(P-1)//(B-1);mask=(q*P-1)//(2*B-1);A=(u*J)&mask;R=sum(((u>>i)&1)<<(c['width']*i) for i in range(n))
    bits=[(u>>i)&1 for i in range(n)];word=''.join(H.encode(y,(1,)*N,'E',halt=N-1) for y in bits)
    X=int(word[::-1],2);width=1<<len(word);beta=2*u+1-q
    need(width==Q and 3*X<Q and beta>0,'Exact width, strong margin and canonical positive slack')
    v=dict(x=x,input_u=u,encoded_X=X,initial_width=Q,spread_R=R,canonical_beta=beta,
           rec__q=q,rec__P=P,rec__J=J,rec__K=mask,rec__Ahat=A+1,rec__quotient_hat=(A-R)//(Q-1)+1,
           rec__input_slack=q-u,rec__output_slack=Q-R)
    need((A-R)%(Q-1)==0 and all(z>0 for z in v.values()),'Positive genuine recoder outer assignment')
    return v,dict(x=x,u=u,n=n,encoded_bits=len(word),encoded_X_bits=X.bit_length(),word_sha256=sha(word.encode()),width_shifted_six_residual=63*Q)

def verify(root):
    root=authenticate(root);H=load(root,'grill_tag_halt_bridge.py');C=load(root,'grill_tag_native_composed205.py')
    # Concrete complete source recipe, deliberately not a universal program:
    # symbols0,1 are binary inputs; symbol2 is unused halt; all productions00.
    widths=(1,1,1);rules={(p,y):(0,0) for p in (0,1) for y in (0,1)};program=H.compile_program(widths,rules,halt=2)
    prior=sys.getrecursionlimit()
    try:
        sys.setrecursionlimit(max(prior,32*len(program)+4096))
        native=C.build(program,unit_product=True,root=root)
    finally:sys.setrecursionlimit(prior)
    p=compose(root,native,3);counts=Counter();fixtures=[]
    for N in (3,4,7):
        L=loader(root,N)
        for x in range(1,32):
            v,r=outer(root,N,x);values={n:1 for n in L['parameters']+L['auxiliaries']};values.update({n:z for n,z in v.items() if n in values})
            e=execute(L['source'],values);rr=[at(e,a)-at(e,b) for a,b in L['comparisons']]
            need(rr[:5]==[0]*5 and rr[-3:]==[0]*3,'All genuine outer/interface rows')
            need(e['rec__copies']&v['rec__K']==v['rec__Ahat']-1,'Actual native AND outer ports')
            need(v['rec__J'].bit_count()==v['rec__q'].bit_length()-1 and v['rec__J']>e['rec__B'],'Geometry outer contract')
            wrong=dict(values,initial_width=64*values['initial_width']);ew=execute(L['source'],wrong)
            need(at(ew,L['comparisons'][-1][0])-at(ew,L['comparisons'][-1][1])==r['width_shifted_six_residual']>0,'Terminal six-zero padding fails paid width binding')
            counts['genuine_outer_word_interfaces']+=1;counts['rejected_six_zero_width_extensions']+=1
            if x in (1,2,7,31):fixtures.append(dict(alphabet_size=N,**r))
    # Independent canonical-length census, including the excluded one-bit case.
    for u in range(1,129):
        candidates=[]
        for n in range(2,11):
            q=1<<n;s=q-u
            for beta in (2*u+1-q,):
                if s>0 and beta>0 and s+beta==u+1:candidates.append(n)
        need(candidates==([] if u==1 else [u.bit_length()]),'Canonical duration, including n1 exclusion');counts['canonical_length_census_inputs']+=1
    # Complete all-value output correction: old native + U*new residual SOS.
    rng=random.Random(78416291);hnative=renamed(native['polynomial_source'],lambda v:'encoded_X' if v=='x' else 'hist__'+v if type(v)is str else v)
    for j in range(24):
        signed=j>=12;v={n:rng.randrange(-2,4) if signed else rng.randrange(1,4) for n in p['parameters']+p['auxiliaries']}
        # J=0 keeps these off-zero full evaluations bounded for the long program.
        for name in native['auxiliaries']:
            if name.startswith('Shat'):v['hist__'+name]=1
        e=execute(p['polynomial_source'],v);old=execute(hnative,{n:z for n,z in v.items() if n=='encoded_X' or n.startswith('hist__')})
        rr=[at(e,a)-at(e,b) for a,b in p['loader']['comparisons']]
        need(e[p['output']]==old['hist__'+native['output']]+e[p['unit_register']]*sum(r*r for r in rr),'Complete polynomial correction')
        counts['complete_polynomial_corrections']+=1;counts['signed_complete_polynomial_corrections']+=signed
    # Source-level structural proof, independent of these finite evaluations.
    f=lambda v:'encoded_X' if v=='x' else 'hist__'+v if type(v)is str else v
    need(p['source'][len(p['loader']['source']):]==renamed(native['source'],f),'Every paid history source row retained')
    need(p['comparisons'][:len(native['comparisons'])-1]==pairs_renamed(native['comparisons'][:-1],f),'Every original nonunit comparison retained')
    need(p['comparisons'][-1]==[f(native['unit_register']),1],'Existing unit comparison retained')
    counts['complete_literal_history_source_preservations']=1
    # General expansion of denominator-cleared loader row has no hidden J port:
    # M*X-A*Q-C*R+A = A*(M*J-Q+1) after X=A*(J+(D-1)*R).
    for N in (3,4,7):
        c=constants(N)
        for _ in range(32):
            J,Q,R=[rng.randrange(-8,9) for _ in range(3)];X=c['A']*(J+(c['D']-1)*R)
            need(c['M']*X-c['A']*Q-c['C']*R+c['A']==c['A']*(c['M']*J-Q+1),'Exact cleared-denominator identity');counts['signed_block_identity_cases']+=1
    return normalize(dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,counts=dict(counts),
        recipe=dict(widths=list(widths),halt=2,rules=[dict(phase=k[0],symbol=k[1],output=list(v)) for k,v in sorted(rules.items())],
                    grill_phase_count=len(program),positive_runs=sum(v>0 for v in program),program=list(program),source_language='Rejects every nonempty binary source word; no universal table claim.'),
        complete=p,outer_fixtures=fixtures,scope='Complete source for one fixed nonuniversal corrected table; general paid interface proof in note. Exact binary(x+1) width bound, all positive witnesses, no external horizon. Native positive existence is inherited; no full Pell zero materialized.'))

def main():
    a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);ns=a.parse_args();answer=verify(ns.root)
    if ns.expect:need(exact(answer,json.loads(ns.expect.read_text())),'Exact full receipt replay')
    if ns.output:ns.output.write_text(json.dumps(answer,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(status=answer['status'],counts=answer['counts'],polynomial=answer['complete']['polynomial'],increment=answer['complete']['increment'],witnesses=len(answer['complete']['auxiliaries']),degree_upper=answer['complete']['degree_upper']),sort_keys=True))
if __name__=='__main__':main()

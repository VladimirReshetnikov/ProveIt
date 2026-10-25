"""Independent literal, algebraic, degree and coefficient-binding checks."""
from pathlib import Path
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
import sys
from construct_coefficients import construct,raw_bytes

ROOT=Path(__file__).resolve().parent
def need(test,message):
    if not test:raise ValueError(message)
def read(p):return json.loads(p.read_text())

def graph_check(old,new):
    need(new['witnesses']==old['witnesses'] and new['fixed_numerals']==old['fixed_numerals'],'input signature')
    old_rows={r[0]:r for r in old['source']};new_rows={r[0]:r for r in new['source']}
    sharp='d0' in new_rows
    changed={'L','LBt','center','d','d0','bB','dmbB','Vcenter'}
    need({k:v for k,v in old_rows.items() if k not in changed}=={k:v for k,v in new_rows.items() if k not in changed},'unchanged gate prefix/suffix')
    expected={
        'd':['d','*','Am1','UE'], 'bB':['bB','*','cTR','Bt'],
        'dmbB':['dmbB','-','d','bB'], 'Vcenter':['Vcenter','*','V','dmbB'],
        'center':['center','+','n','Vcenter']}
    if sharp:
        expected['d0']=['d0','*','Am1','UE'];expected['d']=['d','+','d0','UE']
    need({k:v for k,v in new_rows.items() if k in changed}==expected,'changed carrier gates')
    known=set(new['witnesses']+new['fixed_numerals'])
    for name,op,a,b in new['source']:
        need(name not in known and op in ('+','-','*'),'invalid gate')
        need(all(isinstance(x,int) or x in known for x in (a,b)),'non-topological gate')
        known.add(name)
    live={new['output']}
    for name,op,a,b in reversed(new['source']):
        if name in live: live.update(x for x in (a,b) if isinstance(x,str))
    need(all(r[0] in live for r in new['source']),'dead gate')
    need(all(x in live for x in new['witnesses']+new['fixed_numerals']),'unused input/port')
    need(len(new['source'])==87+sharp,'operation count')
    counts=dict(Counter(r[1] for r in new['source']))
    need(counts=={'*':52,'+':20+sharp,'-':15},'operation split')
    return counts

# Small exact polynomial ring in formal cut registers, independent of the DAG.
def scalar(c):return {():c} if c else {}
def atom(s):return {(s,):1}
def add(a,b):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+c
    return {m:c for m,c in r.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));r[key]=r.get(key,0)+c*d
    return {m:c for m,c in r.items() if c}
def sq(a):return mul(a,a)
def product(*args):
    r=scalar(1)
    for a in args:r=mul(r,a)
    return r
def identities():
    A,U,E=map(atom,('Aminus1','U','E'))
    Delta=mul(A,add(A,scalar(2)))
    G=mul(E,add(scalar(1),product(Delta,sq(U),E)))
    d=product(A,U,E)
    need(sub(G,sq(d))==add(E,product(scalar(2),A,sq(U),sq(E))),'lower-center identity')
    ds=product(add(A,scalar(1)),U,E)
    need(sub(G,sq(ds))==sub(E,product(sq(U),sq(E))),'sharp-center identity')
    n,V,d,b,B=map(atom,('n','V','d','b','B'))
    need(add(n,mul(V,sub(d,mul(b,B))))==sub(add(n,mul(d,V)),product(b,V,B)),'whole carrier shear')
    Q,M,G,V,d,Z0=map(atom,('Q','M','G','V','d','Z0'))
    Z=add(product(M,d,V),Z0)
    left=sub(mul(sub(Q,scalar(1)),sq(Z)),product(sq(M),G,sub(mul(Q,sq(V)),scalar(1))))
    right=add(add(neg(product(sq(M),add(mul(Q,sub(G,sq(d))),sq(d)),sq(V))),
                  product(scalar(2),sub(Q,scalar(1)),M,d,V,Z0)),
              add(mul(sub(Q,scalar(1)),sq(Z0)),mul(sq(M),G)))
    need(left==right,'global degree identity')
    return ['lower-center difference','sharp-center difference','whole carrier shear','global degree identity']

def degrees(circuit):
    env={x:1 for x in circuit['witnesses']};env.update({x:0 for x in circuit['fixed_numerals']})
    get=lambda x:0 if isinstance(x,int) else env[x]
    for name,op,a,b in circuit['source']:
        env[name]=get(a)+get(b) if op=='*' else max(get(a),get(b))
    return env

def univariate(circuit,constants,slopes,p):
    def trim(a):
        while len(a)>1 and a[-1]==0:a.pop()
        return a
    def plus(a,b,sign=1):
        r=[0]*max(len(a),len(b))
        for i,c in enumerate(a):r[i]+=c
        for i,c in enumerate(b):r[i]+=sign*c
        return trim([c%p for c in r])
    def times(a,b):
        r=[0]*(len(a)+len(b)-1)
        for i,c in enumerate(a):
            if c:
                for j,d in enumerate(b):
                    if d:r[i+j]+=c*d
        return trim([c%p for c in r])
    env={k:[v%p] for k,v in constants.items()};env.update({k:[0,v%p] for k,v in slopes.items()})
    get=lambda x:[x%p] if isinstance(x,int) else env[x]
    for name,op,a,b in circuit['source']:
        aa,bb=get(a),get(b)
        env[name]=times(aa,bb) if op=='*' else plus(aa,bb,-1 if op=='-' else 1)
    return env[circuit['output']]

def verify(variant='lower'):
    pins=read(ROOT/'provenance/SOURCE_PINS.json')
    for row in pins['files']:
        data=(ROOT/row['local_path']).read_bytes()
        need(len(data)==row['size'],'pinned size')
        need(hashlib.sha256(data).hexdigest()==row['sha256'],'pinned sha256')
        need(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob_sha1'],'pinned git blob')
    old=read(ROOT/'upstream133/compact/equation_85.json')
    sharp=variant=='sharp';degree=318 if sharp else 323;operations=88 if sharp else 87
    new=read(ROOT/f'equation_{operations}_degree{degree}.json')
    need(new['operations']==operations and new['exact_degree']==degree,'declared metrics')
    need(new['domain']==old['domain']=='strictly positive integers','declared domain')
    counts=graph_check(old,new)
    need(new['operation_breakdown']==counts,'declared operation split')
    algebra=identities()
    values=construct();ports={}
    for name,value in values.items():
        spec=new['coefficient_binding']['ports'][name]
        parent=old['coefficient_binding']['ports'][name]
        payload=(ROOT/'coefficients'/spec['file']).read_bytes();raw=gzip.decompress(payload)
        need(raw==raw_bytes(value),'coefficient reconstruction')
        need(hashlib.sha256(raw).hexdigest()==parent['raw_sha256']==spec['raw_sha256'],'whole tuple raw hash')
        need(hashlib.sha256(payload).hexdigest()==spec['gzip_sha256'],'payload hash')
        need(value.bit_length()==parent['bits']==spec['bits'],'coefficient bit count')
        ports[name]={'bits':value.bit_length(),'raw_sha256':spec['raw_sha256']}
    beta=values['beta']
    need(beta>=31 and beta%2==1 and values['K0']>0 and 0<values['MC']<beta<values['MF']<2*beta,'coefficient box')
    od=degrees(old);nd=degrees(new)
    need({k:nd[k] for k in ('Q','Mtot','Dg','V','d')}=={'Q':86,'Mtot':13,'Dg':56,'V':80,'d':28},'cut degree bounds')
    need(od['Znum']==99 and nd['Am1']+2*nd['U']+2*nd['Dtau']==51,'remainder degree bounds')
    defect=46 if sharp else 51
    bounds=[2*13+86+defect+2*80,86+13+28+80+99,86+2*99,2*13+56]
    need(bounds==[degree,306,284,82],'global degree bound')
    p=1000003;slopes={name:j+1 for j,name in enumerate(new['witnesses'])}
    ray=univariate(new,values,slopes,p)
    q0=beta*slopes['J']%p;k0=(slopes['eta']+slopes['zeta'])%p
    leading=((2**10)*pow(q0,150,p)*pow(slopes['w'],32,p)*pow(slopes['Y'],76,p) if sharp else
             -(2**11)*pow(q0,153,p)*pow(slopes['w'],33,p)*pow(slopes['Y'],77,p))
    leading=leading*pow(slopes['i'],14,p)*pow(k0,44,p)*pow(q0-slopes['F'],2,p)%p
    need(len(ray)-1==degree and ray[-1]==leading and leading!=0,'actual-tuple degree attainment')
    rejected=[]
    for gate in ('d','Vcenter','center'):
        bad=deepcopy(new);row=next(r for r in bad['source'] if r[0]==gate);row[3]=1
        try:graph_check(old,bad)
        except ValueError:rejected.append(gate)
        else:raise ValueError('gate mutation accepted')
    return {'operations':operations,'operation_breakdown':counts,'exact_degree':degree,
            'global_degree_term_bounds':bounds,'identities':algebra,'coefficients':ports,
            'actual_tuple_ray':{'prime':p,'slopes':slopes,'degree':degree,'leading_coefficient':leading},
            'rejected_gate_mutations':rejected,'pinned_source_files':len(pins['files']),
            'scope':'Literal graph, exact algebra, whole tuple and degree checks; ordinary mathematical and inherited calibration proofs are separate.'}

if __name__=='__main__':
    receipt={variant:verify(variant) for variant in ('lower','sharp')};text=json.dumps(receipt,indent=2)+'\n'
    if len(sys.argv)==2:Path(sys.argv[1]).write_text(text)
    else:print(text,end='')

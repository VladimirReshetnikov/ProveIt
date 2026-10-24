#!/usr/bin/env python3
"""Independent exact integer-polynomial audit; Python standard library only.

This does not import build.py or the rational discovery implementation.
Packed exponent keys implement a separate sparse polynomial ring.
"""
from pathlib import Path
from collections import defaultdict,Counter
from math import comb,isqrt
import copy,gzip,hashlib,json
ROOT=Path(__file__).resolve().parent
OPS={'add','sub','mul'}
BASE=128
def require(p,msg):
    if not p:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def plus(*polys):
    r=defaultdict(int)
    for p in polys:
        for e,c in p.items():r[e]+=c
    return {e:c for e,c in r.items() if c}
def minus(p,q):return plus(p,{e:-c for e,c in q.items()})
def times(p,q):
    r=defaultdict(int)
    for e,c in p.items():
        for f,d in q.items():r[e+f]+=c*d
    return {e:c for e,c in r.items() if c}
def scalar(p,c):return {e:v*c for e,v in p.items() if v*c}
def square(p):return times(p,p)
def constant(c):return {0:c} if c else {}
def variable(k):return {BASE**k:1}
def powers(e,n):
    out=[]
    for _ in range(n):out.append(e%BASE);e//=BASE
    require(e==0,'packed degree overflow')
    return tuple(out)
def encode(es):return sum(e*BASE**i for i,e in enumerate(es))
def readpoly(name,n=4):
    records=json.loads((ROOT/name).read_text());out={}
    for r in records:
        es=r['powers'];c=r['coefficient']
        require(len(es)==n and all(isinstance(x,int) and 0<=x<BASE for x in es),'exponents')
        require(isinstance(c,int) and c!=0,'integer coefficients')
        key=encode(es);require(key not in out,'duplicate coefficient');out[key]=c
    return out
def shifted(p,k,h):
    out=defaultdict(int);b=BASE**k
    for e,c in p.items():
        n=(e//b)%BASE
        for j in range(n+1):out[e+(j-n)*b]+=c*comb(n,j)*h**(n-j)
    return {e:c for e,c in out.items() if c}
def degree(p,weights):return max(sum(x*y for x,y in zip(powers(e,len(weights)),weights)) for e in p)
def cutpoly(dag,root,cuts):
    cache={}
    def walk(i):
        if i in cache:return cache[i]
        if i in cuts:p=variable(cuts[i])
        else:
            n=dag['nodes'][i];k=n['kind']
            if k=='literal':p=constant(n['value'])
            else:
                require(k in OPS,'unaccounted free/fixed input in polynomial cut')
                x,y=walk(n['left']),walk(n['right'])
                p={'add':plus,'sub':minus,'mul':times}[k](x,y)
        cache[i]=p;return p
    return walk(root)
def signatures(dag):
    out=[]
    for n in dag['nodes']:
        k=n['kind']
        if k in OPS:
            pair=[out[n['left']],out[n['right']]]
            if k in ('add','mul'):pair.sort()
            payload=[k,*pair]
        else:payload=n
        out.append(sha(json.dumps(payload,sort_keys=True,separators=(',',':')).encode()))
    return out
def translated_signature(dag,successors=False):
    """Canonical expressions, using only elementary certified ring identities."""
    out=[];database={}
    def atom(p):
        h=sha(json.dumps(p,separators=(',',':')).encode());database[h]=p;return h
    zero,one=atom(['literal',0]),atom(['literal',1])
    def op(k,x,y):
        if k=='sub':
            if x==y:return zero
            if y==zero:return x
            p=database[x]
            if p[0]=='add' and y in p[1:]:return p[2] if p[1]==y else p[1]
        if k=='add':
            if x==zero:return y
            if y==zero:return x
        if k=='mul':
            if x==zero or y==zero:return zero
            if x==one:return y
            if y==one:return x
        if k in ('add','mul') and x>y:x,y=y,x
        return atom([k,x,y])
    for n in dag['nodes']:
        k=n['kind']
        if k in OPS:h=op(k,out[n['left']],out[n['right']])
        elif k=='literal':h=atom([k,n['value']])
        else:
            h=atom([k,n['name']])
            if k=='variable' and successors:h=op('add',h,one)
        out.append(h)
    return out[dag['output']]
def audit_topology(d):
    nodes=d['nodes'];names=set();counts=Counter()
    for i,n in enumerate(nodes):
        k=n['kind'];require(k in OPS|{'literal','variable','fixed'},'node kind')
        if k in OPS:
            require(0<=n['left']<i and 0<=n['right']<i,'topology');counts[k]+=1
        elif k=='variable':names.add(n['name'])
    live=set()
    def visit(i):
        if i in live:return
        live.add(i);n=nodes[i]
        if n['kind'] in OPS:visit(n['left']);visit(n['right'])
    visit(d['output'])
    require(len(live)==len(nodes),'all nodes live')
    require(names==set(d['variables']) and len(names)==9,'all9 variables live')
    require(sum(counts.values())==d['total_operations'],'operation count')
    require(dict(counts)==d['operation_counts'],'operation partition')
    return dict(counts)
def local_formulas():
    A,C,i,Z=[variable(k) for k in range(4)];one=constant(1)
    J=minus(scalar(A,4),constant(5));am1=minus(square(A),one)
    D=plus(times(am1,square(C)),one);e0=times(times(i,J),square(C))
    F=plus(times(times(am1,D),square(e0)),one)
    L=minus(plus(times(C,D),one),A);G=plus(A,times(F,L));H=plus(C,times(F,Z))
    I=plus(times(minus(square(G),one),square(H)),one)
    raw=times(times(D,F),I);T=times(times(A,D),e0)
    return locals()
def audit_local_tables():
    f=local_formulas();P=readpoly('radical_P.json');upper=readpoly('radical_upper_P.json')
    sig={encode((0,5,1,0)):1024};L={encode((0,24,6,1)):2**20}
    require(upper==plus(P,L),'corrected polynomial')
    delta=minus(square(P),times(square(sig),f['raw']))
    require(delta==readpoly('radical_defect.json'),'uncorrected exact defect')
    require(max(powers(e,4)[0] for e in delta)<=17,'formal square root cancellation')
    defect=minus(square(upper),times(square(sig),f['raw']))
    require(defect==readpoly('radical_upper_defect.json'),'corrected exact defect')
    pp,dd=P,defect
    for k,h in enumerate((3,1,1,1)):pp=shifted(pp,k,h);dd=shifted(dd,k,h)
    require(pp==readpoly('radical_P_shifted.json'),'shifted P identity')
    require(dd==readpoly('radical_upper_defect_shifted.json'),'shifted defect identity')
    require(all(c>0 for c in pp.values()),'majorant positive branch')
    require(pp.get(0)==15915642730652,'majorant positive boundary')
    require(all(c>0 for c in dd.values()) and dd[0]>0,'strict uniform majorant defect')
    require(dd[0]==32237226735615909648,'boundary witness')
    # The uncorrected truncation is deliberately a failing countercontrol.
    bad=delta
    for k,h in enumerate((3,1,1,1)):bad=shifted(bad,k,h)
    require(bad[0]<0,'uncorrected truncation fails at boundary')
    # Independently check cheap majorant defect.
    defect0=minus(square(f['T']),times(f['D'],f['F']))
    expected=times(f['D'],minus(times(f['D'],square(f['e0'])),constant(1)))
    require(defect0==expected,'cheap exact majorant identity')
    return f,upper,defect,{'P_terms':len(P),'upper_terms':len(upper),'shifted_P_terms':len(pp),'shifted_P_constant':pp[0],'shifted_defect_terms':len(dd),'shifted_defect_constant':dd[0],'uncorrected_boundary_defect':bad[0]}
def audit_norm(d):
    n=d['named_nodes'];ports=['E0','Omega','V0','V1','a0','a1']
    vals=[variable(k) for k in range(6)];E,O,V,W,a,b=vals
    theta=minus(E,times(O,plus(V,W)))
    expected=minus(square(minus(square(theta),times(square(O),plus(a,b)))),scalar(times(times(square(square(O)),a),b),4))
    actual=cutpoly(d,d['output'],{n[name]:k for k,name in enumerate(ports)})
    require(actual==expected,'exact final norm')
    delta0,delta1=minus(square(V),a),minus(square(W),b)
    bs=plus(minus(square(E),scalar(times(times(E,O),plus(V,W)),2)),times(square(O),plus(delta0,delta1)))
    resolved=plus(square(bs),scalar(times(times(times(square(O),V),W),bs),4),scalar(times(square(square(O)),plus(times(delta0,square(W)),times(a,delta1))),4))
    require(expected==resolved,'universal cancellation-resolved norm')
    return len(expected)
def audit_circuits(f,upper):
    rows=[]
    retained=['b','B','ell','targets','N0','mask','Tcode','Usource','Gsource','Jcode','Scode','L','N','R','capbase','U','Y','M','P','K','A','B1','W1','C','J','Q','D','margin','Omega','E0','V0','a0']
    for radical in [False,True]:
        for domain in ['positive','natural']:
            fn=('saturated_radical_' if radical else 'saturated_')+domain+'.json'
            d=json.loads((ROOT/fn).read_text());p=json.loads((ROOT/'upstream'/('gap2082_'+domain+'.json')).read_text())
            audit_topology(d);sd,sp=signatures(d),signatures(p)
            for name in retained:require(sd[d['named_nodes'][name]]==sp[p['named_nodes'][name]],'retained source '+name)
            n=d['named_nodes'];cuts={n[k]:j for j,k in enumerate(['A','C','i','Z'])}
            input_i=next(k for k,node in enumerate(d['nodes']) if node.get('kind')=='variable' and node.get('name')=='i')
            input_j=next(k for k,node in enumerate(d['nodes']) if node.get('kind')=='variable' and node.get('name')=='j')
            require(cutpoly(d,n['i'],{input_i:0})==(plus(variable(0),constant(1)) if domain=='natural' else variable(0)),'domain i coordinate')
            require(cutpoly(d,n['j0'],{input_j:0})==(variable(0) if domain=='natural' else minus(variable(0),constant(1))),'domain j0 coordinate')
            require(cutpoly(d,n['Z'],{n['B1']:0,n['j0']:1,n['C']:2})==plus(variable(0),times(variable(1),variable(2))),'Z exact carrier binding')
            for name in ['F','G','H','I','raw_a1']:
                expected=f['raw'] if name=='raw_a1' else f[name]
                require(cutpoly(d,n[name],cuts)==expected,'exact local '+name)
            if radical:
                require(cutpoly(d,n['V1'],cuts)==upper,'exact radical DAG')
                sig={encode((0,5,1,0)):1024}
                require(cutpoly(d,n['sigma'],cuts)==sig,'radical scale')
                require(cutpoly(d,n['a1'],cuts)==times(square(sig),f['raw']),'scaled radicand binding')
            else:
                require(cutpoly(d,n['V1'],cuts)==times(times(f['T'],f['G']),f['H']),'cheap majorant DAG')
                require(cutpoly(d,n['a1'],cuts)==f['raw'],'unscaled radicand binding')
            audit_norm(d)
            rows.append({'file':fn,'operations':d['total_operations'],'operation_counts':d['operation_counts'],'sha256':sha((ROOT/fn).read_bytes())})
        pos=json.loads((ROOT/(('saturated_radical_' if radical else 'saturated_')+'positive.json')).read_text())
        nat=json.loads((ROOT/(('saturated_radical_' if radical else 'saturated_')+'natural.json')).read_text())
        require(translated_signature(pos,True)==translated_signature(nat),'whole natural/positive successor identity')
    # Literal negative control: perturb the final subtraction to addition.
    bad=copy.deepcopy(d);bad['nodes'][bad['output']]['kind']='add'
    rejected=False
    try:audit_norm(bad)
    except ValueError:rejected=True
    require(rejected,'final norm corruption rejected')
    return rows
def audit_fixed():
    binding=json.loads((ROOT/'fixed/BINDING.json').read_text());rows=[]
    for r in binding['records']:
        raw=gzip.decompress((ROOT/r['path']).read_bytes())
        require(sha(raw)==r['raw_sha256'],'fixed magnitude')
        require(sha((ROOT/r['path']).read_bytes())==r['gzip_sha256'],'fixed payload')
        require(len(raw)==r['raw_bytes'],'fixed size')
        value=int.from_bytes(raw,'little');require(value.bit_length()==r['bits'],'fixed bit length')
        rows.append(r['name'])
    require(len(rows)==11,'eleven fixed leaves')
    for domain in ['positive','natural']:
        parent=json.loads((ROOT/'upstream'/('gap2082_'+domain+'.json')).read_text())
        for radical in [False,True]:
            d=json.loads((ROOT/(('saturated_radical_' if radical else 'saturated_')+domain+'.json')).read_text())
            require(d['coefficient_recipes']==parent['coefficient_recipes'],'all unchanged coefficient recipes')
            require({n['name'] for n in d['nodes'] if n['kind']=='fixed'}==set(rows),'whole fixed leaf binding')
    return {'fixed_leaves':len(rows),'raw_bytes':sum(r['raw_bytes'] for r in binding['records'])}
def audit_degrees(upper,defect):
    r,nu,W=8799,2324,116;a=r+4*nu+2;O=5*a+2*W+3;V0=3*a+r+1;d0=3*a+r+2;E=a+4
    rows=[]
    for radical in [False,True]:
        V1=degree(upper,(a,1,1,r)) if radical else 18*a+r+24
        d1=degree(defect,(a,1,1,r)) if radical else 34*a+2*r+48
        bs=max(2*E,E+O+max(V0,V1),2*O+max(d0,d1))
        ds=[2*bs,2*O+V0+V1+bs,4*O+d0+2*V1,4*O+2*V0+d1]
        expect=1103950 if radical else 1628768
        require(max(ds)==expect and ds.count(expect)==1,'unique dominant degree')
        rows.append({'radical':radical,'A':a,'Omega':O,'V0':V0,'delta0':d0,'V1':V1,'delta1':d1,'Bsmall':bs,'resolved_degrees':ds,'exact_degree':expect})
    return rows
def main():
    f,p,defect,local=audit_local_tables()
    receipt={'status':'PASS','local':local,'circuits':audit_circuits(f,p),'fixed':audit_fixed(),'degrees':audit_degrees(p,defect),
             'whole_natural_translation':'verified by exact elementary expression identities',
             'proof_scope':'Exact algebra/data/circuit certificates. Unbounded Pell and source equivalence are proved in PROOF.md; native/compiler calibration inherited.'}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

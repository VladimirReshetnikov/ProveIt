#!/usr/bin/env python3
"""Independent read-only audit. Never imports or executes upstream programs."""
import ast, gzip, hashlib, json, math
from pathlib import Path
import sympy as S
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
checks=[]
def require(ok,label):
    if not ok: raise ValueError(label)
    checks.append(label)
def read(p): return json.loads(p.read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def parse(text):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int: return S.Integer(n.value)
        if isinstance(n,ast.Name): return S.Symbol(n.id)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,(ast.UAdd,ast.USub)):
            v=go(n.operand); return v if isinstance(n.op,ast.UAdd) else -v
        if isinstance(n,ast.BinOp):
            a,b=go(n.left),go(n.right)
            if isinstance(n.op,ast.Add): return a+b
            if isinstance(n.op,ast.Sub): return a-b
            if isinstance(n.op,ast.Mult): return a*b
            if isinstance(n.op,ast.Pow) and b.is_Integer and 0<=b<=32: return a**int(b)
        raise ValueError('Non-polynomial syntax')
    return S.expand(go(ast.parse(text,mode='eval').body))
def eq(a,b,label): require(S.expand(a-b)==0,label)
def polynomials(d):
    rs=[parse(t) for t in d['residuals']]
    unknowns=set(map(S.Symbol,d['variables'])); ports=set(map(S.Symbol,d['fixed_numerals']))
    require(len(unknowns)==d['variable_count']==len(d['variables']),d['name']+': unique variable count')
    require(len(rs)==d['equation_count'],d['name']+': row count')
    live=set().union(*(r.free_symbols for r in rs))
    require(live==unknowns|ports,d['name']+': exact live symbols, no hidden parameters')
    degs=[S.Poly(r,*sorted(unknowns,key=str)).total_degree() for r in rs]
    require(degs==d['residual_degrees'],d['name']+': residual degrees')
    return rs
binding=read(HERE/'BINDING.json')
for name,h in binding['source_hashes'].items(): require(sha((HERE/name).read_bytes())==h,'bound source '+name)
source=read(HERE/'source/octic30.json'); sr=polynomials(source)
require((HERE/'source/octic30.json').read_bytes()==(ROOT/'integer_system/inherited/octic30.json').read_bytes(),'byte-exact author/source30 identity')
q42=read(HERE/'source/quartic42_x_square.json'); qr=[parse(t) for t in q42['residuals']]
rest={S.Symbol(k):parse(v) for k,v in source['full_parent_restorations'].items()}
require(set(rest)==set(map(S.Symbol,q42['variables'])),'complete parent restoration')
require(sorted(i for i in source['parent_residual_maps_to_child_row_or_zero'] if i)==list(range(1,16)),'all source30 rows reached exactly once')
require(len(qr)==len(source['parent_residual_maps_to_child_row_or_zero'])==27,'complete 27-row parent map')
for i,(r,j) in enumerate(zip(qr,source['parent_residual_maps_to_child_row_or_zero'])):
    eq(r.xreplace(rest),sr[j-1] if j else S.Integer(0),'Q42X restoration row '+str(i+1))
J,F,alpha,beta,eta,V,j,c,h,E=S.symbols('J F alpha beta eta V j c h E')
x=F*alpha; y=F*(beta*J+1-F-alpha); z=eta*(1-V+j*c+h*E-eta)
def pos(prefix):
    a,b,c=S.symbols(prefix+'1 '+prefix+'2 '+prefix+'3'); return 1+a*a+b*b+c*(c+1)
def G(x,y,t): return x*y-(t*t-x-y+1)**2
for i,(w,prefix) in enumerate([(x,'FA_pos'),(y,'FC_pos'),(z,'EZ_pos')],12): eq(sr[i],w-pos(prefix),'source positivity row '+str(i+1))
metrics={}
for name,count,degree in [('octic28',28,8),('degree16_26',26,16)]:
    d=read(ROOT/'integer_system'/f'{name}.json'); rr=polynomials(d)
    cb=d['coefficient_binding']; packet_dir=ROOT/'integer_system'
    require(d['fixed_numerals']==source['fixed_numerals'] and cb['mask_convention']==source['coefficient_binding']['mask_convention'],name+': unchanged four numeral names and shifted-mask convention')
    require((packet_dir/cb['manifest']).resolve()==(HERE/'BINDING.json').resolve(),name+': portable release binding')
    require((packet_dir/cb['compiler_manifest']).resolve()==(HERE/'coefficients/COEFFICIENT_BINDING.json').resolve(),name+': portable compiler manifest')
    require((packet_dir/cb['transfer_proof']).resolve()==(HERE/'coefficients/COEFFICIENT_PROOF.md').resolve(),name+': portable transfer proof')
    require(set(cb['ports'])==set(binding['ports'])==set(source['fixed_numerals']),name+': complete four-port domain')
    for port, historical_name in source['coefficient_binding']['ports'].items():
        actual=(packet_dir/cb['ports'][port]).resolve()
        expected=(HERE/binding['ports'][port]).resolve()
        require(actual==expected==(HERE/'coefficients'/(historical_name+'.bin')).resolve(),name+': coherent actual payload '+port)
    require(cb['encoding']=='minimal unsigned little-endian',name+': explicit payload encoding')
    require(d['source_sha256']==sha((HERE/'source/octic30.json').read_bytes()),name+': source hash')
    for k in range(12): eq(rr[k],sr[k],name+': arithmetic row '+str(k+1))
    t,u=S.symbols('pair_root second_root'); guard=G(x,y,t)
    expected_vars=set(source['variables'])-{p+str(i) for p in ['FA_pos','FC_pos'] for i in [1,2,3]}
    if count==26:
        expected_vars-={'EZ_pos'+str(i) for i in [1,2,3]}; expected_vars.add('second_root'); guard=G(guard,z,u)
    else: eq(rr[13],sr[14],name+': retained third guard')
    expected_vars|={'pair_root','pair_pos1','pair_pos2','pair_pos3'}
    require(set(d['variables'])==expected_vars,name+': exact deletion and addition of variables')
    eq(rr[12],guard-pos('pair_pos'),name+': exact new guard identity')
    require(count==d['variable_count'] and degree==d['exact_degree'],name+': claimed dimensions')
    require(max(d['residual_degrees'])*2==degree,name+': degree upper bound')
    if count==28:
        a,f=S.symbols('a f'); total=S.Poly(S.expand(sum(r*r for r in rr)),*map(S.Symbol,d['variables']))
        mon=[0]*count; mon[d['variables'].index('a')]=4;mon[d['variables'].index('f')]=4
        require(total.coeff_monomial(tuple(mon))==1,name+': exact coefficient [a^4 f^4]=1 on every coefficient slice')
        metrics[name]={'variables':count,'residuals':len(rr),'degree':degree,'expanded_terms_over_coefficient_ring':len(total.terms())}
    else:
        require(S.Poly(rr[12],t).coeff_monomial(t**8)==-1,name+': guard coefficient [t^8]=-1')
        require(all(t not in r.free_symbols for r in rr[:12]),name+': t absent from all other rows')
        metrics[name]={'variables':count,'residuals':len(rr),'degree':degree,'guard_terms':len(S.Poly(rr[12],*map(S.Symbol,d['variables'])).terms()),'degree_certificate':'[pair_root^16]=1'}
# Independent reconstruction directly from the published bounded recipe, not a builder import.
cf=HERE/'coefficients'; manifest=read(cf/'COEFFICIENT_BINDING.json'); values={}
for name,rec in manifest['payloads'].items():
    raw=(cf/(name+'.bin')).read_bytes(); zipped=(cf/(name+'.bin.gz')).read_bytes(); value=int.from_bytes(raw,'little');values[name]=value
    require(sha(raw)==rec['sha256'] and sha(zipped)==rec['gzip_sha256'],name+': raw and compressed hashes')
    require(gzip.decompress(zipped)==raw,name+': gzip exact roundtrip')
    require(len(raw)==rec['bytes'] and len(zipped)==rec['gzip_bytes'] and value.bit_length()==rec['bits'],name+': sizes and bits')
    require(value.to_bytes((value.bit_length()+7)//8,'little')==raw,name+': minimal unsigned little-endian')
b=121; L=8801; d=b*L; B=1<<d
powrho=lambda n:1<<(b*n)
tiles=read(cf/'wang943_tiles.json');require(len(tiles)==943 and all(len(t)==4 and all(type(x)is int and 0<=x<512 for x in t) for t in tiles),'943 ordered four-label tiles')
W=lambda n:1<<(10+2*n)
coeff={i:1+sum(W(10*t+j) for t in range(4) for j in range(10) if ((tile[t]+512)>>j)&1)+sum(W(j) for j in range(40,44)) for i,tile in enumerate(tiles)}
for t,o in enumerate([1020,1000,980,960]):
    for j0 in range(10): coeff[o+2*j0]=W(10*t+j0)
for i,n in enumerate([1095,1096,2195,3296]):coeff[n]=W(40+i)
coeff[1063]=coeff[1064]=0
DC=sum(powrho(e) for e in [40,41,1100,2200])+sum(v*(powrho(4393-e)+powrho(5495-e)) for e,v in coeff.items())
MC=B-1-sum(powrho(e) for e in coeff if e!=1)-2*powrho(1063)
mu=1022+sum(W(j0) for j0 in range(44)); Z=((1<<119)-1)*sum(powrho(e) for e in range(8792,8799))+((1<<27)-1)*powrho(8799)
MF=4+mu*(powrho(4393)+powrho(5495))+sum(powrho(1000+2*j0)+powrho(1021+2*j0) for j0 in range(10))+powrho(2195)+powrho(3296)+Z+B-1
for name,value in {'beta':B-1,'K':DC+B*powrho(1),'MC':MC,'MF_source':MF}.items():require(value==values[name],name+': independent bounded-recipe exact reconstruction')
# Finite diagnostics supplement, never replace, the universal proof.
for xx in range(1,250):
    for yy in range(1,250):
        N=xx+yy-1;m=math.isqrt(N);t=m if N-m*m<=m else m+1
        if xx*yy-(t*t-xx-yy+1)**2<=0:raise ValueError('positive witness regression')
require(True,'62001 nearest-square constructive regressions')
for xx in range(-30,31):
    for yy in range(-30,31):
        for t in range(-20,21):
            if xx*yy-(t*t-xx-yy+1)**2>0 and not(xx>0 and yy>0):raise ValueError('signed soundness regression')
require(True,'152561 signed soundness regressions')
print(json.dumps({'status':'PASS','checks':len(checks),'conditions':checks,'metrics':metrics,'scope':'Exact finite identities and complete coefficient payloads; mathematical positivity proof and inherited unbounded compiler/Pell theorems are separate. No upstream program executed.'},indent=2))

"""Independent exact/literal audit of the four round12 norm circuits.
Imports no producer, circuit, formula, or checker module. Run from any directory.
Every requirement is an explicit exception, and survives python -O.
"""
from pathlib import Path
from collections import Counter, defaultdict
from functools import lru_cache
import gzip, hashlib, json, math, random, sys
import sympy as s
R=Path(__file__).resolve().parent
N=R.parent/'norm'
VARS='t g0 c0 k0 l w x y z m'.split()
MODES={'polar':(471,1245324),'center0':(485,1179788),'center1':(496,1114252),'center2':(545,1080888)}

def need(ok,why):
    if not ok: raise ValueError(why)
def sha(data): return hashlib.sha256(data).hexdigest()
def load(name): return json.loads((N/name).read_text())
def zero(expr,label): need(s.expand(expr)==0, 'polynomial identity: '+label)
source=load('data/source.json'); code=load('data/code.json'); kernels=load('data/kernels.json')
manifest=load('FIXED_COEFFICIENTS.json'); binding=load('data/coefficients_binding.json')
fixed={}; payloads={}
for name,row in manifest.items():
    packed=(N/row['file']).read_bytes(); raw=gzip.decompress(packed)
    need(raw[0] in (0,1) and len(raw)>1,('signed numeral encoding',name))
    val=(-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')
    need(sha(packed)==row['gzip_sha256'] and sha(raw)==row['raw_sha256'],('fixed hashes',name))
    need(abs(val).bit_length()==row['bit_length'],('fixed bit length',name))
    fixed[name]=val;payloads[name]={'raw_sha256':sha(raw),'gzip_sha256':sha(packed)}
ports=[]
for name in ['beta','K','MC','MF_source']:
    row=next(r for r in binding['files'] if r['name']==name)
    packed=(N/'data'/f'{name}.bin.gz').read_bytes();raw=gzip.decompress(packed)
    value=int.from_bytes(raw,'little')
    need(sha(packed)==row['gzip_sha256'] and sha(raw)==row['sha256'],('source port hashes',name))
    need(len(raw)==row['bytes'] and value.bit_length()==row['bit_length'],('source port size',name))
    ports.append(value)
need(fixed['radix']==1<<2134940 and fixed['threshold']==1<<34159017,'actual radix/threshold')
# Authenticate all supplied upstream files, including the pinned native numerals.
pins=load('provenance/BASELINE_SOURCE_PINS.json');checked_pins=[]; inherited_missing=[]
for item in pins['files']:
    p=N/'provenance'/item['local_path'] if item['local_path'].startswith('upstream/') else N/item['local_path']
    if not p.exists():
        inherited_missing.append(item['local_path']);continue
    need(sha(p.read_bytes())==item['sha256'],('upstream pin',item['local_path']))
    checked_pins.append(item['local_path'])
# Reconstruct every target coefficient from the actual sparse kernels, using
# independent polynomial coefficient accumulation, not the placement builder.
n=len(source['variables']); weights=code['weights']; targets=code['targets_by_row']
need(n==31 and len(weights)==31 and len(set(weights))==31 and min(weights)>0,'source coordinates/weights')
need(len(targets)==22 and len(set(targets))==22,'source targets')
need(kernels['variables']==source['variables'] and kernels['ports']==source['constants'],'source interface')
W=max(weights); H=max(t['exponent']+row['degree']*W for row in kernels['kernels'] for t in row['terms'])
need((W,H)==(116,1868),'packing height')
by_target={q:defaultdict(int) for q in targets}; interactions=0
for row in kernels['kernels']:
    d=row['degree'];need(d in (0,1,2),'kernel degree')
    monomials=[((),0,1)] if d==0 else [((i,),w,1) for i,w in enumerate(weights)] if d==1 else [((i,j),weights[i]+weights[j],1 if i==j else 2) for i in range(n) for j in range(i,n)]
    for term in row['terms']:
        need(type(term['exponent']) is int and term['exponent']>=0,'kernel exponent')
        for inds,exponent,factor in monomials:
            interactions+=1
            out=by_target.get(exponent+term['exponent'])
            if out is None:continue
            powers=[0]*n
            for i in inds:powers[i]+=1
            for c in term['coefficient']:
                out[tuple(powers)+tuple(c['powers'])]+=factor*c['coefficient']
for i,row in enumerate(source['equations']):
    wanted=defaultdict(int)
    for term in row['terms']:wanted[tuple(term['powers'])]+=2*code['row_orientations'][i]*term['coefficient']
    got={k:v for k,v in by_target[targets[i]].items() if v}
    need(got=={k:v for k,v in wanted.items() if v},('exact source target identity',i+1))
need(interactions==20466,'complete source convolution count')
# Top-digit proof is bound to THIS actual source and THIS actual layout.
vs=s.symbols(' '.join(source['variables']+source['constants'])); vsd=dict(zip(source['variables']+source['constants'],vs))
row4=sum(t['coefficient']*s.prod(x**e for x,e in zip(vs,t['powers'])) for t in source['equations'][3]['terms'])
zero(row4-(vsd['a']-vsd['E']-(vsd['N']+1)*vsd['s']),'canonical top digit row')
need(weights[source['variables'].index('a')]==116,'canonical top digit weight')
layout=json.loads((R.parent/'source/short_guard/layout.json').read_text())
need(layout['weights']==weights,'short-guard layout binding')
need(json.loads((R.parent/'source/source_original.json').read_text())==source,'short-guard source binding')
# Universal identities. Work over Z[h,c,xi,B,y], with A=2h throughout.
h,c,xi,B,y=s.symbols('h c xi B y'); A=2*h;c2=c*c
D=(A*A-4)*c2+4; E0=c2*xi;E=D*E0;F=1+4*(A*A-4)*c2*c2*D*xi*xi
G=(h-1)*(F-1)-1;Omega=16*E;Hh=c+F*(B-c+Omega*y);GH=G*Hh
A1=D*F*((G*G-1)*Hh*Hh+1)
R00=2*A*E; J00=D-16*E*E
R01=2*A*E0*(D-2*c2);J01=D+16*E0*E0*((3*c2-4)*D-4*c2*(c2-1))
zero(D*F-R00**2-J00,'center0 square defect')
zero(D*F-R01**2-J01,'center1 square defect')
for root,defect,label in [(R00,J00,'center0'),(R01,J01,'center1')]:
    zero(A1-(root*GH)**2-(defect*GH**2-D*F*(Hh**2-1)),label+' total square defect')
LL=1+16*E0**2*(3*c2-4);F0=1+64*E0**2*(c2-1);Om0=-64*E0*(c2-1)
H0=c+F0*(B-c+Om0*y);GH0=-F0*H0
Jf=E0*(c2*A*A+4-8*c2);Warg=B-c+Omega*y
Q=(2*h*h-2)*E*Hh-A*(Jf*(c+(F+F0)*Warg)+4*c2*F0**2*y)
qpoly=s.Poly(s.expand(Q),h,c,xi,B,y,domain=s.ZZ)
zero(4*c2*xi*A*Q-(GH-GH0),'division-free correction identity')
J0=-4*(c2-1)-256*E0**2*(c2-1)**2
zero(J01-(c2*LL*A*A+J0),'center2 defect factor')
P2=R01*GH+LL*Q
J2=J0*GH**2+c2*LL*A*GH*(A*GH0-4*xi*(4-6*c2)*Q)-(LL*Q)**2-D*F*(Hh*Hh-1)
zero(A1-P2**2-J2,'center2 total square defect')
z,S,a0,a1,p=s.symbols('z S a0 a1 p')
Nold=((z+S*p)**2-S*S*(a0+a1))**2-4*S**4*a0*a1
Nnew=(z*z+2*S*p*z+S*S*(a0-(a1-p*p)))**2-4*S*S*a0*(z+S*p)**2
zero(Nold-Nnew,'universal norm translation')
zero((z*z-S*S*(a0+a1))**2-4*S**4*a0*a1-((z*z+S*S*(a0-a1))**2-4*S*S*a0*z*z),'polarization')
g,cap,k,e=s.symbols('g cap k e')
zero(4*g*(cap-g)-(cap**2-(cap-2*g)**2),'short-guard square bound')
# Polynomial formula specifications used to verify literal instructions by exact
# coefficient cancellation with already-proved register substitutions.
def specs(body,mode):
    names=set(body['named_nodes']); X={name:s.Symbol('r_'+name) for name in names}
    X.update({name:s.Symbol('v_'+name) for name in VARS})
    # named 'x/y/z/m' never occur, so these namespaces remain disjoint.
    q=lambda name:X[name]
    fs={name:s.Symbol('f_'+name) for name in fixed}
    recipe_names={json.dumps(v,sort_keys=True):k for k,v in body['fixed_recipes'].items()}
    f={}
    f['b']=6*q('t')+4;f['g']=q('b')*q('g0');f['twice_k']=q('b')*(6*q('k0')+4)
    f['base']=fs['radix']*q('b')**2
    f['ell']=sum(q('base')**w for w in weights)
    for row in kernels['kernels']:
        total=0
        for term in row['terms']:
            co=term['coefficient']
            cv=s.Integer(co[0]['coefficient']) if len(co)==1 and not any(co[0]['powers']) else fs[recipe_names[json.dumps(co,sort_keys=True)]]
            total+=cv*q('base')**term['exponent']
        f['Dcode'+str(row['degree'])]=total
    f['word']=q('ell')+q('g');f['coded']=q('Dcode0')+q('Dcode1')*q('word')+q('Dcode2')*q('word')**2
    f['n0']=q('base')**117;f['nn']=q('base')**1986
    f['targets']=sum(q('base')**v for v in targets)
    f['mask']=q('n0')-1-(q('b')-1)*q('ell')
    f['tc_original']=q('mask')+q('n0')*(q('base')-2)*q('targets');f['tc']=q('tc_original')-2
    f['jc']=2*q('coded')+q('targets');f['sc']=q('g')+q('n0')*q('jc')
    f['X']=q('nn')*(q('sc')+q('tc')+1)-q('sc')-1
    f['Y']=fs['threshold']*q('b')*q('base')**2109;f['cap']=q('b')*q('base')**116
    f['L']=q('l')*q('Y');f['halfU']=q('L')*q('X');f['U']=2*q('halfU');f['V']=4*q('g')*q('w')*q('Y');f['W']=q('b')*q('w')
    f['uv']=q('halfU')*q('V')
    f['halfA']=q('halfU')*(q('V')+1);f['A']=2*q('halfA');f['B1']=2*q('X')+1;f['C']=6*q('c0')-1
    f['Phalf']=q('halfU')*q('U')*q('V');f['K']=q('X')+1+q('twice_k')*(q('Phalf')-1)
    f['S']=2*q('A')-5;f['T']=3*q('W')*q('C')-2*(q('W')**2-1)
    f['Q']=(q('Phalf')**2-1)*q('K')**2+1;f['CKL']=q('C')-q('K')*q('L')
    f['Delta']=q('g')*(q('cap')-q('g'))*q('K')**2-q('cap')**2*q('CKL')**2
    f['xi']=q('z')*q('x');f['D']=(q('A')**2-4)*q('C')**2+4
    f['E0']=q('C')**2*q('xi');f['E']=q('D')*q('E0');f['E2']=q('E0')*q('E')
    f['Fm1']=4*(q('A')**2-4)*q('E2');f['F']=1+q('Fm1');f['G']=(q('halfA')-1)*q('Fm1')-1
    f['Omega']=16*q('E');f['H']=q('C')+q('F')*(q('B1')-q('C')+q('Omega')*q('y'))
    if 'I' in names:f['I']=(q('G')**2-1)*q('H')**2+1
    f['Sigma']=q('xi')*q('S')**5;f['rho']=q('T')+q('S')*q('y')
    f['Theta']=(q('rho')**3-q('rho')*q('S')**2-q('S')**3)*(q('rho')**2+23*q('S')**2)
    f['r']=q('b')*q('Q');f['guard']=q('r')+(9*q('Delta')-3)*(q('r')*q('z'))**2
    if 'lucas' in names:f['lucas']=q('D')*q('F')*q('I')
    f['center']=q('Sigma')*q('m')-q('Theta')
    if mode=='polar':
        f['inner']=q('center')**2+q('Sigma')**2*(q('guard')-q('lucas'))
        f['F10']=q('inner')**2-4*q('Sigma')**2*q('guard')*q('center')**2
    else:
        f['R0']=2*q('A')*q('E') if mode=='center0' else 2*q('A')*q('E0')*(q('D')-2*q('C')**2)
        f['R']=q('R0')*q('G')*q('H')
        if mode!='center2':
            f['J']=q('D')-16*q('E')**2 if mode=='center0' else q('D')+16*q('E0')**2*((3*q('C')**2-4)*q('D')-4*q('C')**2*(q('C')**2-1))
            f['remainder']=q('J')*q('G')**2*q('H')**2-q('D')*q('F')*(q('H')**2-1)
            root=q('R');rem=q('remainder')
        else:
            cc=q('C')**2
            f['F0']=1+64*q('E0')**2*(cc-1);f['Om0']=-64*q('E0')*(cc-1)
            f['H0']=q('C')+q('F0')*(q('B1')-q('C')+q('Om0')*q('y'));f['GH0']=-q('F0')*q('H0')
            f['Jf']=q('E0')*(cc*q('A')**2+4-8*cc)
            f['Qdiv']=(2*q('halfA')**2-2)*q('E')*q('H')-q('A')*(q('Jf')*(q('C')+(q('F')+q('F0'))*(q('B1')-q('C')+q('Omega')*q('y')))+4*cc*q('F0')**2*q('y'))
            f['LL']=1+16*q('E0')**2*(3*cc-4);f['J0']=-4*(cc-1)-256*q('E0')**2*(cc-1)**2
            f['GH']=q('G')*q('H');f['correction']=q('LL')*q('Qdiv');f['Rfinal']=q('R')+q('correction')
            f['remainder_final']=q('J0')*q('GH')**2+cc*q('LL')*q('A')*q('GH')*(q('A')*q('GH0')-4*q('xi')*(4-6*cc)*q('Qdiv'))-q('correction')**2-q('D')*q('F')*(q('H')**2-1)
            root=q('Rfinal');rem=q('remainder_final')
        f['translated_center']=q('center')+q('Sigma')*root
        f['inner']=q('center')**2+2*q('Sigma')*root*q('center')+q('Sigma')**2*(q('guard')-rem)
        f['F10']=q('inner')**2-4*q('Sigma')**2*q('guard')*q('translated_center')**2
    need(set(f)==names,('full named formula coverage',mode,set(f)^names))
    return X,fs,f

receipts=[];rng=random.Random(12102401)
for mode,(want_ops,want_degree) in MODES.items():
    print('Checking',mode,flush=True)
    body=load('integer10_'+mode+'.json');nodes=body['nodes'];named=body['named_nodes']
    need(body['domain']=='Z' and body['variables']==VARS,'unrestricted ten-variable interface')
    need(body['output']==len(nodes)-1,'output position')
    for key,rows in body['fixed_recipes'].items():
        value=sum(row['coefficient']*math.prod(v**e for v,e in zip(ports,row['powers'])) for row in rows)
        need(value==fixed[key],('actual recipe',mode,key))
    need({n['name'] for n in nodes if n['kind']=='fixed'}==set(fixed),'fixed leaf coverage')
    counts=Counter();degrees=[];depends=[]
    for i,node in enumerate(nodes):
        op=node['kind']
        if op in ('add','sub','mul'):
            u,v=node['left'],node['right'];need(type(u)is int and type(v)is int and 0<=u<i and 0<=v<i,('DAG topology',mode,i))
            counts[op]+=1;degrees.append(degrees[u]+degrees[v] if op=='mul' else max(degrees[u],degrees[v]));depends.append(depends[u]|depends[v])
        else:
            need(op in ('variable','literal','fixed'),('forbidden operation',op))
            if op=='literal':need(type(node['value'])is int,'noninteger literal')
            degrees.append(1 if op=='variable' else 0);depends.append({node['name']} if op=='variable' else set())
    need([n['name'] for n in nodes if n['kind']=='variable']==VARS,'exact variable leaves')
    live=set();stack=[body['output']]
    while stack:
        i=stack.pop()
        if i in live:continue
        live.add(i);node=nodes[i]
        if node['kind'] in ('add','sub','mul'):stack += [node['left'],node['right']]
    need(len(live)==len(nodes),'dead graph nodes')
    need(sum(counts.values())==want_ops and dict(counts)==body['operation_counts'],'literal binary count')
    need(degrees[-1]==want_degree==body['degree_upper_bound'],'syntactic degree bound')
    if mode!='polar':need('m' not in depends[named['Rfinal' if mode=='center2' else 'R']],'translation depends on m')
    # Verify EVERY named register, not just finite assignments. Exact reduction
    # may unfold a previously proved relation when CSE has bypassed its name.
    symbols,fs,formula=specs(body,mode);cuts={};proven={};proof_count=0
    for name,idx in sorted(named.items(),key=lambda kv:kv[1]):
        @lru_cache(None)
        def expand_node(i):
            if i in cuts:return cuts[i]
            node=nodes[i];op=node['kind']
            if op=='variable':return symbols[node['name']]
            if op=='literal':return s.Integer(node['value'])
            if op=='fixed':return fs[node['name']]
            u,v=expand_node(node['left']),expand_node(node['right'])
            return u+v if op=='add' else u-v if op=='sub' else u*v
        diff=s.expand(expand_node(idx)-formula[name])
        for old,oidx in sorted(named.items(),key=lambda kv:-kv[1]):
            if diff==0:break
            if old in proven and symbols[old] in diff.free_symbols:
                # Foundational small coordinates must remain variables while
                # the radix power identities are expanded.
                if old in ('base','b','g','twice_k'):continue
                diff=s.expand(diff.subs(symbols[old],formula[old]))
        need(diff==0,('literal exact formula',mode,name,str(diff)[:500]))
        cuts[idx]=symbols[name];proven[name]=True;proof_count+=1
    leaders=[]
    for modulus in (1000000007,1000000009,998244353):
        need(s.isprime(modulus),'degree modulus prime')
        slopes={v:rng.randrange(1,modulus) for v in VARS};vals=[]
        for i,node in enumerate(nodes):
            op=node['kind']
            if op=='variable':value=slopes[node['name']]
            elif op=='literal':value=node['value']
            elif op=='fixed':value=fixed[node['name']]
            else:
                u,v=node['left'],node['right']
                if op=='mul':value=vals[u]*vals[v]
                else:value=(vals[u] if degrees[u]==degrees[i] else 0)+(1 if op=='add' else -1)*(vals[v] if degrees[v]==degrees[i] else 0)
            vals.append(value%modulus)
        need(vals[-1]!=0,('actual degree attainment',mode,modulus))
        leaders.append({'modulus':modulus,'slopes':slopes,'leading_coefficient':vals[-1]})
    finite_cases=0
    for modulus in (2,3,5,101,1000003,1000033,1000037):
        fmod={key:value%modulus for key,value in fixed.items()}
        for trial in range(64):
            inputs={v:rng.randrange(-100,101) for v in VARS}
            if trial<10: inputs[VARS[trial]]=0
            if trial==10:inputs={v:0 for v in VARS}
            vals=[]
            for node in nodes:
                op=node['kind']
                if op=='variable':value=inputs[node['name']]
                elif op=='literal':value=node['value']
                elif op=='fixed':value=fmod[node['name']]
                else:
                    u,v=vals[node['left']],vals[node['right']]
                    value=u+v if op=='add' else u-v if op=='sub' else u*v
                vals.append(value%modulus)
            get=lambda name:vals[named[name]]
            aa,cc,xx,bb,yy=get('A'),get('C'),get('xi'),get('B1'),inputs['y']
            dd,ff,gg,hh=get('D'),get('F'),get('G'),get('H')
            root=0
            if mode!='polar':
                root=2*aa*cc**2*xx*(dd if mode=='center0' else dd-2*cc**2)*gg*hh
            if mode=='center2':
                qq=sum(int(co)*math.prod(pow(v,e,modulus) for v,e in zip([get('halfA'),cc,xx,bb,yy],powers)) for powers,co in qpoly.terms())%modulus
                need(qq==get('Qdiv'),('expanded integral correction replay',modulus,trial))
                root+=(1+16*cc**4*xx*xx*(3*cc*cc-4))*qq
            sig,theta,guard=get('Sigma'),get('Theta'),get('guard')
            lucas=dd*ff*((gg*gg-1)*hh*hh+1)
            zshift=(sig*(inputs['m']+root)-theta)%modulus
            expected=((zshift*zshift-sig*sig*(guard+lucas))**2-4*sig**4*guard*lucas)%modulus
            need(vals[-1]==expected,('complete modular translated-norm replay',mode,modulus,trial))
            finite_cases+=1
    receipts.append({'mode':mode,'sha256':sha((N/('integer10_'+mode+'.json')).read_bytes()),'operations':want_ops,'exact_total_degree':want_degree,'all_named_register_exact_identities':proof_count,'modular_signed_and_degenerate_replays':finite_cases,'translation_independent_of_m':True,'leading_coefficients':leaders})
# Exact prefix comparison binds changes to the fixed inherited source files;
# this is a check when the parent round is present, not a release dependency.
prior=R.parents[1]/'diophantine_zfc_round11/lucas_h1868'
inherited=[]
if prior.exists():
    for fn in ['data/source.json','data/code.json','data/kernels.json','OPTIMIZED_POWER_PLAN.json']:
        need((N/fn).read_bytes()==(prior/fn).read_bytes(),('inherited source byte binding',fn));inherited.append(fn)
result={'status':'PASS','audit_imports_no_producer_code':True,'optimization_enabled':not __debug__,'source_targets_exact':22,'source_kernel_interactions':interactions,'top_digit':{'coordinate':'a','weight':116,'source_identity':'a = E + (N + 1) s'},'universal_identity_count':10,'correction_polynomial_ring':'Z[halfA,C,xi,B,y]','correction_expanded_terms':len(qpoly.terms()),'actual_fixed_payloads':payloads,'verified_upstream_pins':checked_pins,'pinned_files_not_in_component':inherited_missing,'inherited_byte_bindings':inherited,'candidates':receipts,'scope':'Exact arithmetic/formula/source binding audit. The established source-to-refutation calibration and Lucas/Pell/interpolation theorems remain ordinary mathematical dependencies; no new formal kernel certificate.'}
out=R/('INDEPENDENT_CHECKS_OPTIMIZED.json' if not __debug__ else 'INDEPENDENT_CHECKS.json');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

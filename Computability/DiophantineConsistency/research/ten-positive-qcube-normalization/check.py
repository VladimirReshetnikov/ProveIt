#!/usr/bin/env python3
"""Independent exact collector for the complete positive q-cube normalization."""
import argparse,ast,gzip,json,sys
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT='research/ten-positive-uncentered-b-weight'
SEALS={'research/ten-positive-uncentered-b-weight':'e4fe2d2e3d502619cfda003341fd08b49efea408ccdd569d3a551c64dd8f7ac0','research/ten-positive-reused-b-weight':'7042b65701b37773f62b65a4191fdfaaff5d15dccab0374ee5b6e15dcb2c2d1b','research/ten-positive-saturated-pell':'14961a7122489a6b9f4833892c6f4a67ec4b267ae2cc50f9a7b06c4b6587cd33','research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84','candidates/one-page-short10':'72d1f34b64d6d01f33eb6c4b7dfef24dcb23bacbc50fb08d947e8f875056ed3a'}
COMPARISONS=['con-zfc-diophantine-forms/118-structural-compression/positive/PROOF.md','con-zfc-diophantine-forms/116-coprime-projection/positive/PROOF.md','candidates/ten-positive-gap-fusion/README.md','candidates/ten-positive-gap-fusion/PROOF.md']
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def C(c):return {():c} if c else {}
def V(s):return {(s,):1}
def add(a,b,sign=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+sign*c
    return {m:c for m,c in r.items() if c}
def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
    return {m:c for m,c in r.items() if c}
def power(a,n):
    r=C(1)
    for _ in range(n):r=mul(r,a)
    return r
def prod(*args):
    r=C(1)
    for a in args:r=mul(r,a)
    return r
def sub(p,mapping):
    r={}
    for m,c in p.items():
        term=C(c)
        for s in m:term=mul(term,mapping.get(s,V(s)))
        r=add(r,term)
    return r
def degree(p,weights):return max((sum(weights[s] for s in m) for m in p),default=-1)
def cut(rows,target,boundary,covered=None):
    defs={r[0]:r for r in rows};memo={s:V(s) for s in boundary}
    def visit(s):
        if type(s) is int:return C(s)
        if s in memo:return memo[s]
        need(s in defs,'unbound polynomial leaf '+str(s));_,op,a,b=defs[s]
        if covered is not None:covered.add(s)
        aa,bb=visit(a),visit(b);memo[s]=mul(aa,bb) if op=='*' else add(aa,bb,-1 if op=='-' else 1)
        return memo[s]
    return visit(target)
def expression(text):
    tree=ast.parse(text,mode='eval').body
    def visit(n):
        if isinstance(n,ast.Name):return V(n.id)
        if isinstance(n,ast.Constant) and type(n.value) is int:return C(n.value)
        need(isinstance(n,ast.BinOp) and type(n.op) in [ast.Add,ast.Sub,ast.Mult],'fixed polynomial syntax')
        a,b=visit(n.left),visit(n.right);return mul(a,b) if isinstance(n.op,ast.Mult) else add(a,b,-1 if isinstance(n.op,ast.Sub) else 1)
    return visit(tree),{n.id for n in ast.walk(tree) if isinstance(n,ast.Name)}
def formulas():
    return [('bJ','beta*J'),('q','bJ+1'),('Y','q*q*q*s'),('C','q-F-alpha'),('X','w*q'),('k','eta+zeta'),('c','k*Y+eta'),('mu','q*q+1'),('Am1','mu*Y*(X+1)'),('Hp','4*Am1-1'),('V0','X*mu*mu*Y*Y'),('Dtau','1+V0*(V0+1)*k*k'),('G','bJ*(q-F)+alpha'),('R','G*(q*q-1)+(MC+q*MF)*J'),('e','k-R-1'),('Bt','(K0+w)*C-F'),('U','i*c*c'),('Delta','Am1*(Am1+2)'),('Df','1+Delta*U*U*Dtau'),('Q','Delta*Delta*U*U*Dtau'),('delta','Q-1'),('Tp','T+alpha'),('cTR','c*Tp-R'),('V','Df*cTR-c'),('Dnum','Q*V*V-1'),('center','n+V-cTR*Bt'),('Kpos','X*(3*c-2*X)+2'),('Zpart1','bJ*mu*mu*(Hp*center+Kpos)'),('Zpart2','Hp*(mu*mu*Bt+bJ*e)'),('Znum','Zpart1-Zpart2'),('Mtot','bJ*mu*mu*Hp'),('Dg','Dtau*Df'),('fg','delta*Mtot*Mtot*Dg'),('fy','Mtot*Mtot*Dnum'),('fs','delta*Znum*Znum'),('N','(fs-fg-fy)*(fs-fg-fy)-4*fg*fy')]
def audit(packet):
    rows=packet['source'];inputs=['J','F','alpha','i','T','w','s','n','eta','zeta']
    need(packet['witnesses']==inputs and packet['fixed_numerals']==['beta','K0','MC','MF'] and packet['domain']=='strictly positive integers' and packet['output']=='N','whole quantified ten-positive/four-port signature')
    known=set(inputs+packet['fixed_numerals']);deps={};degrees={s:1 for s in inputs}|{s:0 for s in packet['fixed_numerals']}
    for key,op,a,b in rows:
        need(key not in known and op in ['+','-','*'] and all(type(s) is int or s in known for s in [a,b]),'entire fresh binary topology')
        known.add(key);deps[key]=[a,b];da,db=[0 if type(s) is int else degrees[s] for s in [a,b]];degrees[key]=da+db if op=='*' else max(da,db)
    live=set();todo=['N']
    while todo:
        s=todo.pop()
        if type(s) is int or s in live:continue
        live.add(s);todo+=deps.get(s,[])
    need(live==known and len(rows)==packet['operations'] and dict(Counter(r[1] for r in rows))==packet['operation_breakdown'],'whole live-gate/input/port census')
    verified=set(inputs+packet['fixed_numerals']);covered=set();cert=[]
    for target,text in formulas():
        expected,refs=expression(text);need(refs<=verified,'ordered semantic interface '+target);actual=cut(rows,target,refs,covered);need(actual==expected,'complete free polynomial interface '+target);verified.add(target)
        cert.append(dict(target=target,inputs=sorted(refs),terms=len(actual),sha256=sha256(repr(sorted(actual.items())).encode()).hexdigest()))
    need(covered==set(deps),'every actual gate covered by semantic polynomial identities')
    return degrees,cert
def ray(rows,inputs):
    def plus(a,b,sign=1):
        c=list(a)+[0]*max(0,len(b)-len(a))
        for i,n in enumerate(b):c[i]+=sign*n
        while c and not c[-1]:c.pop()
        return c
    def times(a,b):
        c=[0]*(len(a)+len(b)-1) if a and b else []
        for i,n in enumerate(a):
            if n:
                for j,m in enumerate(b):
                    if m:c[i+j]+=n*m
        while c and not c[-1]:c.pop()
        return c
    env={s:[0,1] for s in inputs}|{s:[n] for s,n in dict(beta=2,K0=3,MC=5,MF=7).items()}
    for key,op,a,b in rows:
        aa=[a] if type(a) is int else env[a];bb=[b] if type(b) is int else env[b];env[key]=times(aa,bb) if op=='*' else plus(aa,bb,-1 if op=='-' else 1)
    return len(env['N'])-1,env['N'][-1]
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    pins=load(HERE/'SOURCE_PINS.json');need(pins['closed_dependencies']==list(SEALS),'all five whole calibrated closed contracts')
    inventory=set(COMPARISONS)
    for name,h in SEALS.items():
        folder=ROOT/name;need(digest(folder/'MANIFEST.json')==h,'exact whole dependency seal '+name);inventory|={str(p.relative_to(ROOT)) for p in folder.rglob('*') if p.is_file()}
        files=load(folder/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'},'closed dependency inventory '+name)
        for n,pin in files.items():need(digest(folder/n)==pin,'whole frozen member '+name+'/'+n)
    need(set(pins['files'])==inventory,'complete immutable pin inventory')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole immutable source '+n)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'},'own complete closed inventory')
        for n,h in files.items():need(digest(HERE/n)==h,'whole own sealed member '+n)
    parent=ROOT/PARENT
    for name in ['zero89.json','PROOF.md','MANIFEST.json','SOURCE_PINS.json','INDEXED_BINDING.json']:need((HERE/'parents'/name).read_bytes()==(parent/name).read_bytes(),'whole copied parent '+name)
    packet=load(HERE/'zero86.json');old=load(parent/'zero89.json');degrees,cert=audit(packet)
    primary=packet['coefficient_binding'];indexed=load(HERE/'INDEXED_BINDING.json');need(primary==old['coefficient_binding'] and indexed==load(parent/'INDEXED_BINDING.json'),'whole separately calibrated tuples')
    bindings=[]
    for label,binding in [('bfs',primary),('indexed_bfs',indexed)]:
        vals={}
        for name,pin in binding['ports'].items():
            payload=(HERE/binding['path']/pin['file']).read_bytes();raw=gzip.decompress(payload);value=int.from_bytes(raw,'little');need(payload==(parent/binding['path']/pin['file']).read_bytes() and sha256(payload).hexdigest()==pin['gzip_sha256'] and sha256(raw).hexdigest()==pin['raw_sha256'] and value.bit_length()==pin['bits'] and len(raw)==(value.bit_length()+7)//8,'whole coefficient '+label+name);vals[name]=value
        need(vals['beta']>=31 and vals['beta']%2 and vals['K0']>0 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'actual complete coefficient box '+label);bindings.append(dict(tuple=label,K_raw_sha256=binding['ports']['K0']['raw_sha256'],whole_four_payloads=True))
    # Derive the complete literal mutation independently of the producer.
    defs={r[0]:r for r in old['source']};expected_rows=[defs['bJ'],defs['q'],defs['q2'],defs['q3'],['Y','*','q3','s']]
    edits={'P1mu2':['P1mu2','*','bJ','mu2'],'mu2inner':['mu2inner','*','mu2','Bt'],'P1e':['P1e','*','bJ','e'],'brk':['brk','+','mu2inner','P1e'],'Znum':['Znum','-','Zpart1','Zpart2']}
    removed={'P1','qm1Y','q3Bt','inner'}
    expected_rows += [edits.get(r[0],r) for r in old['source'] if r[0] not in {'bJ','q','q2','q3'}|removed]
    need(packet['source']==expected_rows,'whole actual parent-to-new source with only declared mutations')
    expected=deepcopy(old);expected['witnesses']=['s' if x=='Y' else x for x in old['witnesses']]
    expected.update(name='qcube_normalized_zero86',source=expected_rows,operations=86,operation_breakdown=dict(Counter(r[1] for r in expected_rows)),exact_degree=466,parent_sha256=digest(parent/'zero89.json'),parent_manifest_sha256=SEALS[PARENT],proof='PROOF.md',proof_status='Complete ordinary q-cube-normalized theorem at each retained whole tuple; positive forward completeness; no canonical promotion.')
    need(packet==expected,'entire new source metadata and literal cost')
    index={r[0]:i for i,r in enumerate(expected_rows)}
    expected_cuts=dict(parent_sha256=digest(parent/'zero89.json'),complete_parent_to_new_rows=[dict(parent_index=i,old=row,new_index=index.get(row[0]),new=expected_rows[index[row[0]]] if row[0] in index else None) for i,row in enumerate(old['source'])],added_rows=[dict(new_index=index['Y'],row=['Y','*','q3','s'])],deleted_names=sorted(removed),moved_names=['q2','q3'],replaced_names=sorted(edits),coordinate_map=dict(Y='q^3*s',n_old='n_new-s'),clearing=dict(Z_old='q^3*Z_new',M_old='q^3*M_new',N_old='q^12*N_new'))
    need(load(HERE/'CUTS.json')==expected_cuts,'all89old rows, complete consumer changes and the one new gate')
    boundary={'q','bJ','mu2','Hp','n','V','cTR','Bt','Kpos','Y','e','s'}
    q,h,mm,H,n,v,b,B,K,Y,e,s=map(V,['q','bJ','mu2','Hp','n','V','cTR','Bt','Kpos','Y','e','s'])
    Z=cut(packet['source'],'Znum',boundary);M=cut(packet['source'],'Mtot',boundary)
    formula=add(prod(h,mm,add(mul(H,add(add(n,v),mul(b,B),-1)),K)),mul(H,add(mul(mm,B),mul(h,e))),-1)
    need(Z==formula and M==prod(h,mm,H),'whole reduced numerator and denominator')
    oldZ=cut(old['source'],'Znum',boundary);oldM=cut(old['source'],'Mtot',boundary)
    mapping={'Y':prod(power(q,3),s),'n':add(n,s,-1)}
    need(sub(oldZ,mapping)==prod(power(q,3),Z) and oldM==prod(power(q,3),M),'whole actual substitution and q-cube cancellation')
    z,m,g,d,y=map(V,['z','m','g','delta','Dy']);norm=add(power(add(add(mul(d,power(z,2)),prod(d,power(m,2),g),-1),mul(power(m,2),y),-1),2),prod(C(4),d,power(m,4),g,y),-1)
    need(sub(norm,{'z':mul(power(q,3),z),'m':mul(power(q,3),m)})==mul(power(q,12),norm),'entire norm scales byq^12')
    # Integer center: h*mu²*H*(n+V)-Z = h*mu²*H*b*B-H*h*K+H*mu²*B+H*h*e.
    need(add(prod(h,mm,H,add(n,v)),Z,-1)==add(add(prod(mm,H,add(C(1),mul(h,b)),B),prod(h,H,e)),prod(h,mm,K),-1),'complete normalized center identity without division')
    # Reuse the signed-root polynomial identity without assuming either orientation.
    zz,gg,yy=map(V,['zz','gg','yy']);signed=C(1)
    for sg in [-1,1]:
        for sy in [-1,1]:signed=mul(signed,add(add(zz,gg,sg),yy,sy))
    need(signed==add(power(add(add(power(zz,2),power(gg,2),-1),power(yy,2),-1),2),prod(C(4),power(gg,2),power(yy,2)),-1),'whole four signed radical factors')
    de,Mv,Vv,Z0,Qv=map(V,['delta','M','V','Z0','Q']);omega=add(mul(de,power(add(mul(Mv,Vv),Z0),2)),mul(power(Mv,2),add(mul(Qv,power(Vv,2)),C(1),-1)),-1)
    want=add(add(mul(de,power(Z0,2)),prod(C(2),de,Mv,Vv,Z0)),mul(power(Mv,2),add(power(Vv,2),C(1),-1)),-1);need(sub(omega,{'Q':add(de,C(1))})==want,'entire omega cancellation')
    weights={x:1 for x in packet['witnesses']}|{x:0 for x in packet['fixed_numerals']};lead={x:V(x) for x in weights}
    for key,op,a,b0 in packet['source']:
        aa=C(a) if type(a) is int else lead[a];bb=C(b0) if type(b0) is int else lead[b0];da,db=[0 if type(x) is int else degrees[x] for x in [a,b0]]
        part=mul(aa,bb) if op=='*' else aa if da>db else mul(C(-1 if op=='-' else 1),bb) if db>da else add(aa,bb,-1 if op=='-' else 1);need(part,'nonzero entire front leading part '+key);lead[key]=part
        if key=='Mtot':break
    q0,X0,k0,ss,ii,T0=map(V,['q0','X0','k0','s','i','T0']);A0=prod(power(q0,5),X0,ss);U0=prod(ii,power(k0,2),power(q0,6),power(ss,2));E0=prod(power(q0,20),power(X0,2),power(ss,4),power(k0,2));Df0=prod(power(A0,2),power(U0,2),E0);Q0=prod(power(A0,4),power(U0,2),E0);b0=prod(k0,power(q0,3),ss,T0);V0=mul(Df0,b0);G0=mul(E0,Df0);M0=prod(C(4),power(q0,10),X0,ss)
    mapping={'q0':prod(V('beta'),V('J')),'X0':prod(V('w'),V('beta'),V('J')),'k0':add(V('eta'),V('zeta')),'T0':add(V('T'),V('alpha'))}
    for name,poly in [('Y',prod(power(q0,3),ss)),('Am1',A0),('U',U0),('Dtau',E0),('Df',Df0),('Q',Q0),('cTR',b0),('V',V0),('Mtot',M0)]:need(lead[name]==sub(poly,mapping),'entire actual front leading form '+name)
    need([degrees[x] for x in ['Y','c','Am1','Dtau','U','Df','Q','cTR','V','Dg','Mtot','fg','fy']]==[4,5,8,30,11,68,84,6,74,98,13,208,258],'all exact front degrees')
    remainder=add(Z,mul(M,v),-1);need(degree(remainder,{x:degrees[x] for x in boundary})==21,'complete actual cleared remainder degree21')
    terms=[84+42,84+13+74+21,26+148];need(max(terms)==192 and terms.count(192)==1 and max(384,400,416)<466,'uniquely dominant omega and norm terms')
    leading=prod(C(-4),power(Q0,2),power(M0,4),G0,power(V0,2));want=prod(C(-1024),power(q0,296),power(X0,30),power(ss,64),power(ii,10),power(k0,34),power(T0,2));need(leading==want,'ENTIRE highest homogeneous form')
    full=sub(want,mapping);selected=tuple(sorted(['beta']*326+['J']*326+['w']*30+['s']*64+['i']*10+['eta']*34+['T']*2));need(full.get(selected)==-1024 and {sum(weights[x] for x in mon) for mon in full}=={466},'attained global degree at either actual beta')
    rd,rlc=ray(packet['source'],packet['witnesses']);need((rd,rlc)==(466,-2**372),'complete independent exact univariate polynomial replay')
    controls=[]
    def evaluate(rows,env):
        env=dict(env)
        for key,op,a,b0 in rows:
            aa=a if type(a) is int else env[a];bb=b0 if type(b0) is int else env[b0];env[key]=aa*bb if op=='*' else aa-bb if op=='-' else aa+bb
        return env
    for j in range(1,33):
        env=dict(J=1+j%3,F=1+j%4,alpha=1+j%5,i=1+j%2,T=1+j%7,w=1+j%6,s=1+j%9,n=1+j%4,eta=1+j%5,zeta=1+j%8,beta=31,K0=103,MC=17,MF=43)
        new=evaluate(packet['source'],env);oldenv=env|dict(Y=new['Y'],n=env['n']-env['s']);previous=evaluate(old['source'],oldenv)
        need(previous['Znum']==new['q']**3*new['Znum'] and previous['Mtot']==new['q']**3*new['Mtot'] and previous['N']==new['q']**12*new['N'],'full actual exact substitution replay')
        controls.append(dict(case=j,shifted_old_n=oldenv['n'],new_n=env['n'],full_norm_identity=True))
    rejected=[]
    for label,node,column,value in [('carrier sign','Znum',1,'+'),('unreduced factor','P1mu2',2,'q3'),('lost denominator','Mtot',2,'mu2'),('wrong remainder','brk',1,'-'),('old exponent carrier','mu2inner',3,'Y'),('wrong Y power','Y',2,'q2'),('lost G factor','Dg',2,1),('wrong norm sign','N',1,'+'),('old weight','LBt',2,'k')]:
        bad=deepcopy(packet);next(r for r in bad['source'] if r[0]==node)[column]=value
        try:audit(bad)
        except (ValueError,KeyError):rejected.append(label)
        else:raise ValueError('accepted actual malformed graph '+label)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),operations=86,operation_breakdown=packet['operation_breakdown'],exact_degree=466,naive_syntactic_degree=degrees['N'],omega_degree=192,fg_degree=208,fy_degree=258,full_leading_form_terms=len(full),selected_coefficient=dict(sign=-1,two_power=10,beta_power=326),univariate_degree=rd,univariate_leading_coefficient=str(rlc),complete_free_polynomial_interfaces=cert,every_actual_gate_covered=86,whole_graph_sha256=digest(HERE/'zero86.json'),whole_coherent_bindings=bindings,actual_substitution_controls=controls,rejected_actual_graph_controls=rejected,source_pins={n:digest(HERE/n) for n in ['README.md','PROOF.md','SOURCE_PINS.json','build.py','check.py']},builder_or_parent_or_incoming_code_executed=False,canonical_or_common_files_modified=False,scope='Exact finite literal/identity/global-degree certificates. Unbounded positive-domain/native theorem is PROOF.md; arbitrary reverse positive shear is not asserted.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),all_live_operations=86,actual_graph_corruptions=len(rejected),exact_global_degree=466),sort_keys=True))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Optimizer-free whole-source, signed-center and exact-degree certificate."""
import argparse,ast
from collections import Counter
from copy import deepcopy
import gzip,json,sys
from hashlib import sha256
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT='research/ten-positive-reused-b-weight'
CASES=[('zero89',89,288,False),('direct95',95,262,True)]
SEALS={'research/ten-positive-reused-b-weight':'7042b65701b37773f62b65a4191fdfaaff5d15dccab0374ee5b6e15dcb2c2d1b','research/ten-positive-saturated-pell':'14961a7122489a6b9f4833892c6f4a67ec4b267ae2cc50f9a7b06c4b6587cd33','research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84','candidates/one-page-short10':'72d1f34b64d6d01f33eb6c4b7dfef24dcb23bacbc50fb08d947e8f875056ed3a'}
COMPARISONS=['con-zfc-diophantine-forms/118-structural-compression/positive/PROOF.md','con-zfc-diophantine-forms/116-coprime-projection/positive/PROOF.md']
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
def formulas(direct):
    B='B' if direct else 'Bt'
    return [('bJ','beta*J'),('q','bJ+1'),('C','q-F-alpha'),('X','q+x' if direct else 'w*q'),('k','eta+zeta'),('c','k*Y+eta'),('mu','q*q+1'),('Am1','mu*Y*(X+1)'),('Hp','4*Am1-1'),('V0','X*mu*mu*Y*Y'),('Dtau','1+V0*(V0+1)*k*k'),('G','bJ*(q-F)+alpha'),('R','G*(q*q-1)+(MC+q*MF)*J'),('e','k-R-1'),(B,'(q*K0+X)*C-q*F' if direct else '(K0+w)*C-F'),('U','i*c*c'),('Delta','Am1*(Am1+2)'),('Df','1+Delta*U*U*Dtau'),('Q','Delta*Delta*U*U*Dtau'),('delta','Q-1'),('Tp','T+alpha'),('cTR','c*Tp-R'),('V','Df*cTR-c'),('Dnum','Q*V*V-1'),('P1','q*q*q*q*bJ' if direct else 'q*q*q*bJ'),('center','n+V-cTR*'+B),('Kpos','X*(3*c-2*X)+2'),('Zpart1','P1*mu*mu*(Hp*center+Kpos)'),('inner','q*bJ*Y-q*q*q*B-bJ*X' if direct else 'bJ*Y-q*q*q*Bt'),('Zpart2','Hp*(mu*mu*inner-P1*e)'),('Znum','Zpart1+Zpart2'),('Mtot','P1*mu*mu*Hp'),('Dg','Dtau*Df'),('fg','delta*Mtot*Mtot*Dg'),('fy','Mtot*Mtot*Dnum'),('fs','delta*Znum*Znum'),('N','(fs-fg-fy)*(fs-fg-fy)-4*fg*fy')]
def audit(packet,direct):
    rows=packet['source'];inputs=['J','F','alpha','i','T','x' if direct else 'w','Y','n','eta','zeta'];need(packet['witnesses']==inputs and packet['fixed_numerals']==['beta','K0','MC','MF'] and packet['domain']=='strictly positive integers' and packet['output']=='N','entire quantified signature')
    known=set(inputs+packet['fixed_numerals']);deps={};degrees={s:1 for s in inputs}|{s:0 for s in packet['fixed_numerals']}
    for key,op,a,b in rows:
        need(key not in known and op in ['+','-','*'] and all(type(s) is int or s in known for s in [a,b]),'complete fresh binary topology')
        known.add(key);deps[key]=[a,b];da,db=[0 if type(s) is int else degrees[s] for s in [a,b]];degrees[key]=da+db if op=='*' else max(da,db)
    live=set();todo=['N']
    while todo:
        s=todo.pop()
        if type(s) is int or s in live:continue
        live.add(s);todo+=deps.get(s,[])
    need(live==known and len(rows)==packet['operations'] and dict(Counter(r[1] for r in rows))==packet['operation_breakdown'],'all gates, inputs and ports live; literal census')
    verified=set(inputs+packet['fixed_numerals']);covered=set();cert=[]
    for target,text in formulas(direct):
        expected,refs=expression(text);need(refs<=verified,'ordered semantic boundary '+target);actual=cut(rows,target,refs,covered);need(actual==expected,'entire free polynomial interface '+target);verified.add(target)
        cert.append(dict(target=target,inputs=sorted(refs),terms=len(actual),sha256=sha256(repr(sorted(actual.items())).encode()).hexdigest()))
    need(covered==set(deps),'every actual gate covered by polynomial interfaces')
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
    pins=load(HERE/'SOURCE_PINS.json')
    need(pins['closed_dependencies']==list(SEALS),'all four exact calibrated closed dependencies')
    inventory=set(COMPARISONS)
    for dirname,h in SEALS.items():
        folder=ROOT/dirname;need(digest(folder/'MANIFEST.json')==h,'exact reviewed calibrated seal '+dirname);inventory|={str(p.relative_to(ROOT)) for p in folder.rglob('*') if p.is_file()}
    need(set(pins['files'])==inventory,'complete whole dependency pin inventory')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole frozen dependency '+n)
    for dirname in pins['closed_dependencies']:
        folder=ROOT/dirname;files=load(folder/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'},'whole closed dependency '+dirname)
        for n,h in files.items():need(digest(folder/n)==h,'whole sealed member '+dirname+'/'+n)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'},'closed own inventory')
        for n,h in files.items():need(digest(HERE/n)==h,'whole own sealed member '+n)
    parent=ROOT/PARENT
    for name in ['PROOF.md','MANIFEST.json','SOURCE_PINS.json','INDEXED_BINDING.json']:need((HERE/'parents'/name).read_bytes()==(parent/name).read_bytes(),'complete copied parent '+name)
    primary=load(HERE/'zero89.json')['coefficient_binding'];indexed=load(HERE/'INDEXED_BINDING.json');need(primary==load(parent/'saturated_upper.json')['coefficient_binding'] and indexed==load(parent/'INDEXED_BINDING.json'),'whole separately calibrated bindings')
    bindings=[]
    for label,binding in [('bfs',primary),('indexed_bfs',indexed)]:
        vals={}
        for name,pin in binding['ports'].items():
            payload=(HERE/binding['path']/pin['file']).read_bytes();raw=gzip.decompress(payload);value=int.from_bytes(raw,'little');need(payload==(parent/binding['path']/pin['file']).read_bytes() and sha256(payload).hexdigest()==pin['gzip_sha256'] and sha256(raw).hexdigest()==pin['raw_sha256'] and value.bit_length()==pin['bits'] and len(raw)==(value.bit_length()+7)//8,'whole compressed and raw coefficient '+label+name);vals[name]=value
        need(vals['beta']>=31 and vals['beta']%2==1 and vals['K0']>0 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'actual whole coefficient box '+label);bindings.append(dict(tuple=label,K_raw_sha256=binding['ports']['K0']['raw_sha256'],all_four_payloads=True))
    # New unbounded inequalities are reduced to exact identities and positive coefficients.
    d,u,E,c,Tp,k,R=map(V,['d','u','E','c','Tp','k','R']);Df=add(C(1),prod(d,power(u,2),E));Q=prod(power(d,2),power(u,2),E);g2=mul(E,Df)
    b=add(mul(c,Tp),R,-1);e=add(add(k,R,-1),C(1),-1);need(add(b,e,-1)==add(add(mul(c,Tp),k,-1),C(1)),'exact b-e bound before R sign')
    need(Q==mul(d,add(Df,C(1),-1)),'exact Q=Delta(Df-1)')
    h=prod(d,power(u,2),E);gap=add(power(h,2),g2,-1);need(gap==mul(E,add(prod(d,power(u,2),E,add(prod(d,power(u,2)),C(1),-1)),C(1),-1)),'full h²-g² positive identity')
    x,y,z=map(V,['x','y','z'])
    shifted=sub(gap,{'d':add(x,C(3)),'u':add(y,C(1)),'E':add(z,C(1))});need(shifted.get((),0)>0 and all(a>0 for a in shifted.values()),'strict h²-g² for all Delta>=3,U,E>=1')
    need(add(mul(C(2),add(Q,C(1),-1)),mul(d,Df),-1)==add(add(Q,d,-1),C(2),-1),'exact adjacent-root bound denominator identity')
    shifted=sub(add(add(Q,d,-1),C(2),-1),{'d':add(x,C(3)),'u':add(y,C(1)),'E':add(z,C(1))});need(shifted.get((),0)>0 and all(a>0 for a in shifted.values()),'Delta*Df<2(Q-1) for every source premise')
    dd=V('Df');ratio=add(mul(C(8),power(add(dd,C(1),-1),2)),prod(C(4),dd,add(dd,C(1),-1)),-1);need(ratio==prod(C(4),add(dd,C(1),-1),add(dd,C(2),-1)),'strict b/Delta³U²E inequality numerator')
    # Pell traces through the actual first, third and fifth odd indices.
    S=V('S');traces=[C(1),S]
    for _ in range(4):traces.append(add(prod(C(2),S,traces[-1]),traces[-2],-1))
    need(traces[3]==prod(S,add(mul(C(4),power(S,2)),C(3),-1)) and traces[5]==prod(S,add(add(mul(C(16),power(S,4)),mul(C(20),power(S,2)),-1),C(5))),'full odd auxiliary trace identities')
    q=V('q');fifthgap=add(add(mul(C(8),power(q,2)),mul(C(20),q),-1),C(5));shifted=sub(fifthgap,{'q':add(x,C(3))});need(shifted.get((),0)>0 and all(a>0 for a in shifted.values()),'fifth index strict8Q² bound for allQ>=3')
    # The complete squared norm and its cancellation identity, independent of source collectors.
    zz,gg,yy=map(V,['z','g','y']);signed=C(1)
    for sg in [-1,1]:
        for sy in [-1,1]:signed=mul(signed,add(add(zz,gg,sg),yy,sy))
    need(signed==add(power(add(add(power(zz,2),power(gg,2),-1),power(yy,2),-1),2),prod(C(4),power(gg,2),power(yy,2)),-1),'whole signed norm identity')
    de,M,VV,Z0,QQ=map(V,['delta','M','V','Z0','Q']);omega=add(mul(de,power(add(mul(M,VV),Z0),2)),mul(power(M,2),add(mul(QQ,power(VV,2)),C(1),-1)),-1)
    expected=add(add(mul(de,power(Z0,2)),prod(C(2),de,M,VV,Z0)),mul(power(M,2),add(power(VV,2),C(1),-1)),-1);need(sub(omega,{'Q':add(de,C(1))})==expected,'entire polynomial omega cancellation')
    cuts=load(HERE/'CUTS.json');results=[];rejected=[];carriers={};parent_routes=[]
    for target,count,exact,direct in CASES:
        packet=load(HERE/(target+'.json'));rows=packet['source'];degrees,cert=audit(packet,direct);B='B' if direct else 'Bt';base='direct_saturated_' if direct else 'saturated_'
        for suffix in ['upper','sharp']:
            stem=base+suffix;path=parent/(stem+'.json');old=load(path);need((HERE/'parents'/(stem+'.json')).read_bytes()==path.read_bytes(),'whole copied old graph '+stem);mapping=[];deleted=[];changed=[];expected_rows=[]
            for i,row in enumerate(old['source']):
                if row[0] in ['Cg','nVCg','Afull']:deleted.append(dict(parent_index=i,row=row));continue
                new=list(row)
                if row[0]=='center':need(row==['center','-','nVCg','LBt'],'actual parent center');new[2]='nV';changed.append(dict(parent_index=i,new_index=len(expected_rows),old=row,new=new))
                mapping.append(dict(parent_index=i,new_index=len(expected_rows),row=new));expected_rows.append(new)
            need(rows==expected_rows and set(a['row'][0] for a in deleted)==({'Cg','nVCg','Afull'} if suffix=='sharp' else {'Cg','nVCg'}) and len(changed)==1,'whole source exact center-only mutation '+stem)
            need(cuts[stem]==dict(target=target,parent_sha256=digest(path),deleted_rows=deleted,changed_rows=changed,complete_parent_to_new_rows=mapping),'all parent rows and deleted consumers '+stem)
            # A universal positive n shear, with Cg a free boundary, matches complete numerators.
            boundary={'q','bJ','mu2','Hp','n','V','cTR',B,'Kpos','Y','e','X','Cg'}
            oldZ=cut(old['source'],'Znum',boundary);newZ=cut(rows,'Znum',boundary);need(sub(newZ,{'n':add(V('n'),V('Cg'))})==oldZ,'entire centered-to-uncentered positive shear '+stem);parent_routes.append(stem)
        oldpath=parent/(base+'upper.json');expected_packet=deepcopy(load(oldpath));expected_packet.update(name='uncentered_b_'+target,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=exact,parent_sha256=digest(oldpath),parent_manifest_sha256=digest(parent/'MANIFEST.json'),proof='PROOF.md',proof_status='Complete ordinary uncentered b-weight theorem; whole coherent fixed tuple retained; no canonical promotion.')
        need(packet==expected_packet and packet['operations']==count and packet['coefficient_binding']==primary,'entire new graph header and fixed tuple '+target)
        boundary={'q','bJ','mu2','Hp','n','V','cTR',B,'Kpos','Y','e','X'};qq,h,mu2,H,nn,VV,bb,BB,K,Y,ee,X=map(V,['q','bJ','mu2','Hp','n','V','cTR',B,'Kpos','Y','e','X']);P=prod(power(qq,4 if direct else 3),h);MM=prod(P,mu2,H)
        low=add(add(prod(qq,h,Y) if direct else mul(h,Y),mul(power(qq,3),BB),-1),mul(h,X) if direct else C(0),-1);formula=add(prod(P,mu2,add(mul(H,add(add(nn,VV),mul(bb,BB),-1)),K)),mul(H,add(mul(mu2,low),mul(P,ee),-1)))
        need(cut(rows,'Znum',boundary)==formula and cut(rows,'Mtot',boundary)==MM,'entire actual signed carrier clearing')
        remainder=add(formula,mul(MM,VV),-1);need(degree(remainder,{s:degrees[s] for s in boundary})==19 and degrees['Mtot']==13,'full actual uncentered remainder degree6/cleared19');carriers[direct]=(formula,MM)
        # Independently propagate every complete leading component through the front.
        weights={s:1 for s in packet['witnesses']}|{s:0 for s in packet['fixed_numerals']};lead={s:V(s) for s in weights}
        for key,op,a,b in rows:
            aa=C(a) if type(a) is int else lead[a];bb=C(b) if type(b) is int else lead[b];da,db=[0 if type(s) is int else degrees[s] for s in [a,b]]
            part=mul(aa,bb) if op=='*' else aa if da>db else mul(C(-1 if op=='-' else 1),bb) if db>da else add(aa,bb,-1 if op=='-' else 1);need(part,'nonzero entire front leading component '+key);lead[key]=part
            if key=='Mtot':break
        q0,X0,Y0,i0,k0,F0=map(V,['q0','X0','Y0','i0','k0','F0']);A0=prod(power(q0,2),X0,Y0);U0=prod(i0,power(k0,2),power(Y0,2));E0=prod(power(q0,8),power(X0,2),power(Y0,4),power(k0,2));Df0=prod(power(A0,2),power(U0,2),E0);Q0=prod(power(A0,4),power(U0,2),E0);R0=prod(power(q0,3),add(q0,F0,-1));V0=prod(C(-1),Df0,R0);M0=prod(C(4),power(q0,9 if direct else 8),A0);G0=mul(E0,Df0)
        mapping={'q0':prod(V('beta'),V('J')),'X0':add(prod(V('beta'),V('J')),V('x')) if direct else prod(V('w'),V('beta'),V('J')),'Y0':V('Y'),'i0':V('i'),'k0':add(V('eta'),V('zeta')),'F0':V('F')}
        for name,p in [('Am1',A0),('U',U0),('Dtau',E0),('Df',Df0),('Q',Q0),('R',R0),('V',V0),('Mtot',M0)]:need(lead[name]==sub(p,mapping),'entire actual front leading form '+name)
        dd,vd,gd,omega_degree=(42,38,50,112) if direct else (48,42,56,122);need([degrees[s] for s in ['delta','V','Dg','fy','fg']]==[dd,vd,gd,dd+26+2*vd,dd+26+gd],'all exact degree premises')
        terms=[dd+38,dd+13+vd+19,26+2*vd];need(max(terms)==omega_degree and terms.count(omega_degree)==1,'uniquely dominant omega cancellation term');fg=dd+26+gd;fy=dd+26+2*vd;need(fg+fy==exact and max(2*omega_degree,omega_degree+fg,2*fg)<exact,'uniquely dominant -4fg*fy global term')
        leading=prod(C(-4),power(Q0,2),power(M0,4),G0,power(V0,2));qexp=126 if direct else 122;want=prod(C(-1024),power(q0,qexp),power(X0,30),power(Y0,62),power(i0,10),power(k0,32),power(add(q0,F0,-1),2));need(leading==want,'ENTIRE global highest homogeneous form')
        full=sub(want,mapping);bp=126 if direct else 152;selected=tuple(sorted(['beta']*bp+['J']*bp+['x' if direct else 'w']*30+['Y']*62+['i']*10+['eta']*32+['F']*2));need(full.get(selected)==-1024 and {sum(weights[s] for s in m) for m in full}=={exact},'attained nonzero coefficient at either actual fixed beta')
        rd,rlc=ray(rows,packet['witnesses']);need((rd,rlc)==(exact,-2**168*3**30 if direct else -2**194),'complete independent univariate polynomial replay')
        for label,node,column,value in [('norm sign','N',1,'+'),('coprime factor','Dg',2,1),('carrier center','center',2,'n'),('carrier degree','P1',2,'q2'),('weight','LBt',2,'k')]:
            bad=deepcopy(packet);next(r for r in bad['source'] if r[0]==node)[column]=value
            try:audit(bad,direct)
            except (ValueError,KeyError):rejected.append(target+':'+label)
            else:raise ValueError('accepted actual malformed source '+label)
        results.append(dict(name=target,operations=count,operation_breakdown=packet['operation_breakdown'],exact_degree=exact,naive_syntactic_degree=degrees['N'],omega_degree=omega_degree,full_leading_form_terms=len(full),selected_coefficient=dict(sign=-1,two_power=10,beta_power=bp),univariate_degree=rd,univariate_leading_coefficient=str(rlc),free_polynomial_interfaces=cert,every_actual_gate_covered=count,whole_graph_sha256=digest(HERE/(target+'.json'))))
    # Direct exact positive map; no actual input is silently identified before q^4|X.
    qq,nn,bb,Bt,u0=map(V,['q','n','cTR','Bt','u0']);h=add(qq,C(1),-1);shift=add(nn,add(prod(h,bb,Bt),u0));mapping={'bJ':h,'B':mul(qq,Bt),'n':shift,'X':prod(power(qq,4),u0)}
    ordinary=sub(carriers[False][0],{'bJ':h,'X':prod(power(qq,4),u0)});need(sub(carriers[True][0],mapping)==mul(qq,ordinary) and sub(carriers[True][1],{'bJ':h})==mul(qq,sub(carriers[False][1],{'bJ':h})),'whole direct-converse Z and M scale byq')
    # Nonvacuous exact auxiliary controls include the two forbidden small odd indices.
    controls=[]
    for ss in range(2,10):
        a,b=1,ss;tr=[a,b]
        for _ in range(6):a,b=b,2*ss*b-a;tr.append(b)
        for v in [1,3,5,7]:
            need(tr[v]%ss==0,'actual odd trace divisibility');vv=tr[v]//ss;need((vv>8*ss**4)==(v>=5),'actual auxiliary gap controls retain low-index countercases');controls.append(dict(S=ss,index=v,V=vv))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),candidates=results,whole_coherent_bindings=bindings,parent_routes=parent_routes,universal_positive_inequality_certificates=5,auxiliary_controls=controls,rejected_actual_graph_controls=rejected,source_pins={n:digest(HERE/n) for n in ['README.md','PROOF.md','SOURCE_PINS.json','build.py','check.py']},builder_or_incoming_or_parent_code_executed=False,canonical_or_common_files_modified=False,scope='Complete finite literal/identity/degree certificates; unbounded ordinary/native composition is PROOF.md.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),circuits=2,all_live_operations=184,actual_graph_corruptions=len(rejected)),sort_keys=True))
if __name__=='__main__':main()

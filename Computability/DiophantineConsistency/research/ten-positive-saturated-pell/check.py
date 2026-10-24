#!/usr/bin/env python3
"""Independent whole-source/free-port/leading-form audit; executes no incoming code."""
import argparse,ast
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import io,json,subprocess,sys,zipfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
CASES=[('saturated_upper',92,283,False,False),('saturated_sharp',93,278,False,True),('direct_saturated_upper',98,258,True,False),('direct_saturated_sharp',99,254,True,True)]
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
def prod(*parts):
    r=C(1)
    for p in parts:r=mul(r,p)
    return r
def degree(poly,weights):return max((sum(weights[s] for s in m) for m in poly),default=-1)
def sub(p,mapping):
    r={}
    for monomial,c in p.items():
        term=C(c)
        for s in monomial:term=mul(term,mapping.get(s,V(s)))
        r=add(r,term)
    return r
def cut(rows,target,boundary,covered=None):
    defs={r[0]:r for r in rows};memo={s:V(s) for s in boundary}
    def visit(s):
        if type(s) is int:return C(s)
        if s in memo:return memo[s]
        need(s in defs,'unbound cut leaf '+str(s));_,op,a,b=defs[s]
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
def formulas(direct,sharp):
    B='B' if direct else 'Bt'
    return [('bJ','beta*J'),('q','bJ+1'),('C','q-F-alpha'),('X','q+x' if direct else 'w*q'),('k','eta+zeta'),('c','k*Y+eta'),('mu','q*q+1'),('Am1','mu*Y*(X+1)'),('Hp','4*Am1-1'),('V0','X*mu*mu*Y*Y'),('Dtau','1+V0*(V0+1)*k*k'),('G','bJ*(q-F)+alpha'),('R','G*(q*q-1)+(MC+q*MF)*J'),('e','k-R-1'),(B,'(q*K0+X)*C-q*F' if direct else '(K0+w)*C-F'),('U','i*c*c'),('Cg','(Am1+'+('1' if sharp else '2')+')*U*Dtau'),('Delta','Am1*(Am1+2)'),('Df','1+Delta*U*U*Dtau'),('Q','Delta*Delta*U*U*Dtau'),('delta','Q-1'),('Tp','T+alpha'),('V','Df*(c*Tp-R)-c'),('Dnum','Q*V*V-1'),('L','k*Tp'),('P1','q*q*q*q*bJ' if direct else 'q*q*q*bJ'),('center','n+V+Cg-L*'+B),('Kpos','X*(3*c-2*X)+2'),('Zpart1','P1*mu*mu*(Hp*center+Kpos)'),('inner','q*bJ*Y-q*q*q*B-bJ*X' if direct else 'bJ*Y-q*q*q*Bt'),('Zpart2','Hp*(mu*mu*inner-P1*e)'),('Znum','Zpart1+Zpart2'),('Mtot','P1*mu*mu*Hp'),('Dg','Dtau*Df'),('fg','delta*Mtot*Mtot*Dg'),('fy','Mtot*Mtot*Dnum'),('fs','delta*Znum*Znum'),('N','(fs-fg-fy)*(fs-fg-fy)-4*fg*fy')]
def audit(packet,direct,sharp):
    rows=packet['source'];known=set(packet['witnesses']+packet['fixed_numerals']);deps={};degrees={s:1 for s in packet['witnesses']}|{s:0 for s in packet['fixed_numerals']}
    for key,op,a,b in rows:
        need(key not in known and op in ['+','-','*'] and all(type(s) is int or s in known for s in [a,b]),'complete fresh binary topology')
        known.add(key);deps[key]=[a,b];da,db=[0 if type(s) is int else degrees[s] for s in [a,b]];degrees[key]=da+db if op=='*' else max(da,db)
    live=set();todo=[packet['output']]
    while todo:
        s=todo.pop()
        if type(s) is int or s in live:continue
        live.add(s);todo+=deps.get(s,[])
    need(live==known and len(rows)==packet['operations'] and dict(Counter(r[1] for r in rows))==packet['operation_breakdown'],'all gates/ports/inputs live and literal census')
    expected_inputs=['J','F','alpha','i','T','x' if direct else 'w','Y','n','eta','zeta']
    need(packet['witnesses']==expected_inputs and packet['domain']=='strictly positive integers' and packet['fixed_numerals']==['beta','K0','MC','MF'] and packet['output']=='N','complete quantified signature')
    verified=set(packet['witnesses']+packet['fixed_numerals']);covered=set();cert=[]
    for target,formula in formulas(direct,sharp):
        expected,refs=expression(formula);need(refs<=verified,'ordered semantic interfaces');actual=cut(rows,target,refs,covered)
        need(actual==expected,'actual complete free polynomial '+target);verified.add(target)
        cert.append(dict(target=target,inputs=sorted(refs),terms=len(actual),coefficient_sha256=sha256(repr(sorted(actual.items())).encode()).hexdigest()))
    need(covered==set(deps),'EVERY live gate covered by free-port interfaces')
    return degrees,cert

def ray(rows,witnesses):
    # Independent exact univariate expansion of the complete literal graph.
    def plus(a,b,sign=1):
        c=list(a)+[0]*max(0,len(b)-len(a))
        for i,n in enumerate(b):c[i]+=sign*n
        while c and c[-1]==0:c.pop()
        return c
    def times(a,b):
        c=[0]*(len(a)+len(b)-1) if a and b else []
        for i,n in enumerate(a):
            if n:
                for j,m in enumerate(b):
                    if m:c[i+j]+=n*m
        while c and c[-1]==0:c.pop()
        return c
    env={s:[0,1] for s in witnesses}|{s:[n] for s,n in dict(beta=2,K0=3,MC=5,MF=7).items()}
    for key,op,a,b in rows:
        aa=[a] if type(a) is int else env[a];bb=[b] if type(b) is int else env[b]
        env[key]=times(aa,bb) if op=='*' else plus(aa,bb,-1 if op=='-' else 1)
    return len(env['N'])-1,env['N'][-1]
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'complete immutable dependency '+name)
    for dirname in pins['closed_dependencies']:
        folder=ROOT/dirname;files=load(folder/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'},'closed calibrated dependency '+dirname)
        for name,h in files.items():need(digest(folder/name)==h,'whole calibrated member '+name)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'},'closed own inventory')
        for name,h in files.items():need(digest(HERE/name)==h,'whole sealed member '+name)
    ap=pins['archive'];p=ROOT.parents[1]/ap['path'];blob=p.read_bytes() if p.exists() else subprocess.check_output(['git','show',ap['commit']+':'+ap['path']],cwd=ROOT.parents[1]);need(sha256(blob).hexdigest()==ap['sha256'] and len(blob)==ap['bytes'],'whole pinned historical archive')
    archive=zipfile.ZipFile(io.BytesIO(blob));members=load(HERE/'INCOMING_MEMBERS.json');need(set(members)=={i.filename for i in archive.infolist() if not i.is_dir()},'all133 archive members')
    for name,pin in members.items():
        data=archive.read(name);need(sha256(data).hexdigest()==pin['sha256'] and len(data)==pin['bytes'],'whole incoming member '+name)
    for stem in ['saturation_semantics','saturated_degree_proof','complete_constants']:
        need((HERE/'source'/(stem+'.tex')).read_bytes()==archive.read(ap['root']+'report_parts/'+stem+'.tex'),'whole copied primary source proof '+stem)
    need((HERE/'source/INCOMING_SOURCE_PINS.json').read_bytes()==archive.read(ap['root']+'SOURCE_PINS.json'),'whole copied incoming source dependency ledger')
    for mode in ['','_OPTIMIZED']:
        need((HERE/('REVIEWED_INCOMING_VERIFICATION'+mode+'.json')).read_bytes()==archive.read(ap['root']+'checks/VERIFICATION'+mode+'.json'),'whole reviewed incoming replay record '+mode)
    original_binding=load(HERE/'saturated_upper.json')['coefficient_binding'];indexed_binding=load(HERE/'INDEXED_BINDING.json');ports=[]
    need(original_binding==load(ROOT/'candidates/one-page-short10/polynomial.json')['coefficient_binding']|{'path':'coefficients/compact44_bfs/'},'WHOLE original calibrated BFS binding')
    expected_indexed=deepcopy(load(ROOT/'research/indexed-tile-enumeration/coefficients/BINDING.json'));expected_indexed['path']='coefficients/indexed_bfs/';need(indexed_binding==expected_indexed,'WHOLE separately regenerated indexed binding')
    for label,binding,parent in [('bfs',original_binding,ROOT/'candidates/one-page-short10'),('indexed_bfs',indexed_binding,ROOT/'research/indexed-tile-enumeration')]:
        values={}
        for name,pin in binding['ports'].items():
            payload=(HERE/binding['path']/pin['file']).read_bytes();raw=gzip.decompress(payload);n=int.from_bytes(raw,'little')
            need(payload==(parent/'coefficients'/pin['file']).read_bytes() and sha256(payload).hexdigest()==pin['gzip_sha256'] and sha256(raw).hexdigest()==pin['raw_sha256'] and n.bit_length()==pin['bits'] and len(raw)==(n.bit_length()+7)//8,'all compressed/raw numeral bytes '+label+name);values[name]=n
        need(values['beta']>=31 and values['beta']%2==1 and values['K0']>0 and 0<values['MC']<values['beta']<values['MF']<2*values['beta'],'complete calibrated port box '+label)
        ports.append(dict(tuple=label,all_four_compressed_and_raw_bytes=True,K_raw_sha256=binding['ports']['K0']['raw_sha256']))
    # Universal norm/root-recovery, anti-cancellation, and rational descent identities.
    z,a,b=map(V,['z','a','b']);four=C(1)
    for sa in [-1,1]:
        for sb in [-1,1]:four=mul(four,add(add(z,a,sa),b,sb))
    N2=add(power(add(add(power(z,2),power(a,2),-1),power(b,2),-1),2),prod(C(4),power(a,2),power(b,2)),-1);need(four==N2,'entire four-signed-factor norm identity')
    q,v,y=map(V,['q','v','y']);vp=add(mul(add(mul(C(2),q),C(1),-1),v),prod(C(2),add(q,C(1),-1),y),-1);yp=add(mul(add(mul(C(2),q),C(1),-1),y),prod(C(2),q,v),-1)
    need(add(mul(q,power(vp,2)),mul(add(q,C(1),-1),power(yp,2)),-1)==add(mul(q,power(v,2)),mul(add(q,C(1),-1),power(y,2)),-1),'full adjacent-Pell rational-descent isometry')
    E,t,d,VV=map(V,['E','t','d','V']);Q=mul(E,t);Df=add(C(1),mul(E,d));delta=add(Q,C(1),-1)
    need(add(add(mul(Q,power(VV,2)),C(1),-1),prod(delta,E,Df),-1)==add(mul(E,add(mul(t,power(VV,2)),mul(delta,Df),-1)),C(1),-1),'entire -1 moduloE anti-cancellation identity')
    A,U,EE=map(V,['A','U','E']);need(add(power(prod(A,U,EE),2),mul(EE,add(C(1),prod(add(power(A,2),C(1),-1),power(U,2),EE))),-1)==add(prod(power(U,2),power(EE,2)),EE,-1),'full sharp-center defect identity')
    results=[];rejected=[];carriers={}
    for name,count,exact,direct,sharp in CASES:
        path=HERE/(name+'.json');packet=load(path);need(path.read_bytes()==archive.read(ap['root']+'equations/'+name+'.json'),'exact complete exported equation '+name)
        need(packet['coefficient_binding']==original_binding and packet['operations']==count and packet['exact_degree']==exact,'actual fixed binding and claimed metric '+name)
        degrees,cert=audit(packet,direct,sharp);rows=packet['source'];B='B' if direct else 'Bt'
        boundary={'q','bJ','mu2','Hp','n','V','Cg','L',B,'Kpos','Y','e','X'}
        qq,g,mu2,H,nn,VV,Cg,L,BB,K,Y,ee,X=map(V,['q','bJ','mu2','Hp','n','V','Cg','L',B,'Kpos','Y','e','X']);P=prod(power(qq,4 if direct else 3),g);M=prod(P,mu2,H)
        low=add(add(prod(qq,g,Y) if direct else mul(g,Y),mul(power(qq,3),BB),-1),mul(g,X) if direct else C(0),-1)
        formula=add(prod(P,mu2,add(mul(H,add(add(add(nn,VV),Cg),mul(L,BB),-1)),K)),mul(H,add(mul(mu2,low),mul(P,ee),-1)))
        need(cut(rows,'Znum',boundary)==formula and cut(rows,'Mtot',boundary)==M,'complete normalized-carrier clearing identity '+name)
        remainder=add(formula,mul(M,add(VV,Cg)),-1)
        need(degree(remainder,{s:degrees[s] for s in boundary})-degrees['Mtot']==4,'actual complete normalized rational remainder degree4')
        carriers[direct]=(formula,M)
        # Whole actual homogeneous components preceding the finalizer.
        weights={s:1 for s in packet['witnesses']}|{s:0 for s in packet['fixed_numerals']};lead={s:V(s) for s in weights}
        for key,op,aa,bb in rows:
            aa0=C(aa) if type(aa) is int else lead[aa];bb0=C(bb) if type(bb) is int else lead[bb];da,db=[0 if type(s) is int else degrees[s] for s in [aa,bb]]
            part=mul(aa0,bb0) if op=='*' else aa0 if da>db else mul(C(-1 if op=='-' else 1),bb0) if db>da else add(aa0,bb0,-1 if op=='-' else 1)
            need(part,'nonzero actual leading component '+key);lead[key]=part
            if key=='Mtot':break
        q0,X0,Y0,i0,k0,F0=map(V,['q0','X0','Y0','i0','k0','F0']);A0=prod(power(q0,2),X0,Y0);U0=prod(i0,power(k0,2),power(Y0,2));E0=prod(power(q0,8),power(X0,2),power(Y0,4),power(k0,2));Df0=prod(power(A0,2),power(U0,2),E0);Q0=prod(power(A0,4),power(U0,2),E0);R0=prod(power(q0,3),add(q0,F0,-1));V0=prod(C(-1),Df0,R0);M0=prod(C(4),power(q0,9 if direct else 8),A0);G0=prod(A0,U0,E0)
        mapping={'q0':prod(V('beta'),V('J')),'X0':add(prod(V('beta'),V('J')),V('x')) if direct else prod(V('w'),V('beta'),V('J')),'Y0':V('Y'),'i0':V('i'),'k0':add(V('eta'),V('zeta')),'F0':V('F')}
        for target,poly in [('Am1',A0),('U',U0),('Dtau',E0),('Df',Df0),('Q',Q0),('R',R0),('V',V0),('Cg',G0),('Mtot',M0)]:need(lead[target]==sub(poly,mapping),'entire actual homogeneous component '+target)
        # Formal defects: upper U*E, sharp U*E/(2A), auxiliary y-V.
        Ad=4 if direct else 5;Ed=16 if direct else 18;Vd=38 if direct else 42;Dd=42 if direct else 48;Gd=Ad+5+Ed;defect=5+Ed if not sharp else 5+Ed-Ad
        need(degrees['Am1']==Ad and degrees['U']==5 and degrees['Dtau']==Ed and degrees['V']==Vd and degrees['delta']==Dd and degrees['Mtot']==13 and degrees['Cg']==Gd,'all literal Laurent-degree premises')
        need(defect>4 and Vd-Dd==(-4 if direct else -6),'strict defect/remainder/auxiliary-gap degree comparisons')
        need(2*Dd+52+2*Vd+Gd+defect==exact,'global four-factor Laurent upperdegree and attainment')
        leading=prod(C(4),power(Q0,2),power(M0,4),power(V0,2),power(U0,2),power(E0,2)) if sharp else prod(C(8),power(Q0,2),power(M0,4),power(V0,2),G0,U0,E0)
        qexp=(122 if sharp else 124) if direct else (118 if sharp else 120);xexp=28 if sharp else 29;yexp=60 if sharp else 61;twopower=10 if sharp else 11
        expectedlead=prod(C(2**twopower),power(q0,qexp),power(X0,xexp),power(Y0,yexp),power(i0,10),power(k0,32),power(add(q0,F0,-1),2));need(leading==expectedlead,'ENTIRE global highest homogeneous form')
        full=sub(expectedlead,mapping);betaexp=qexp if direct else qexp+xexp;selected=tuple(sorted(['beta']*betaexp+['J']*betaexp+['x' if direct else 'w']*xexp+['Y']*yexp+['i']*10+['eta']*32+['F']*2));need(full.get(selected)==2**twopower,'nonzero actual selected fixed-beta coefficient')
        need({sum(weights[s] for s in m) for m in full}=={exact},'entire leading form has actual totaldegree')
        raydegree,rayLC=ray(rows,packet['witnesses']);raywant=(2**(164 if sharp else 167)*3**(28 if sharp else 29)) if direct else 2**(188 if sharp else 192);need((raydegree,rayLC)==(exact,raywant),'independent COMPLETE exact polynomial ray '+name)
        for label,target,column,value in [('normsign','N',1,'+'),('saturationfactor','Dg',2,1),('center','Cg',2,'U'),('carrierpower','P1',2,'q2')]:
            bad=deepcopy(packet);next(r for r in bad['source'] if r[0]==target)[column]=value
            try:audit(bad,direct,sharp)
            except (ValueError,KeyError):rejected.append(name+':'+label)
            else:raise ValueError('semantic collector accepted actual corrupted graph '+name+label)
        results.append(dict(name=name,operations=count,operation_breakdown=packet['operation_breakdown'],exact_degree=exact,naive_syntactic_degree=degrees['N'],actual_normalized_remainder_degree=4,free_polynomial_interfaces=cert,all_gates_covered=count,whole_actual_leading_forms=True,selected_coefficient={'two_power':twopower,'beta_power':betaexp},exact_ray_degree=raydegree,exact_ray_leading_coefficient=str(rayLC),equation_sha256=digest(path)))
    # Direct positive converse: physical X=q^4*u0 and B=q*Bt, n'=n+(q-1)L*Bt+u0.
    qq,nn,LL,Bt,u0=map(V,['q','n','L','Bt','u0']);g=add(qq,C(1),-1)
    shift=add(nn,add(prod(g,LL,Bt),u0));mapping={'bJ':g,'B':mul(qq,Bt),'n':shift,'X':prod(power(qq,4),u0)}
    ordinary=sub(carriers[False][0],{'bJ':g,'X':prod(power(qq,4),u0)})
    need(sub(carriers[True][0],mapping)==mul(qq,ordinary) and sub(carriers[True][1],{'bJ':g})==mul(qq,sub(carriers[False][1],{'bJ':g})),'ENTIRE direct-converse numerator and carrier scale byq')
    ss,gg,yy=map(V,['s','g','y']);tail=add(power(add(add(ss,gg,-1),yy,-1),2),prod(C(4),gg,yy),-1)
    need(sub(tail,{s:prod(power(qq,2),V(s)) for s in ['s','g','y']})==prod(power(qq,4),tail),'ENTIRE norm scales byq^4 in direct converse')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),candidates=results,whole_archive_members=133,whole_coherent_bindings=ports,universal_four_factor_norm=True,universal_sharp_defect=True,universal_adjacent_descent=True,anti_cancellation_mod_E=True,rejected_actual_graph_controls=rejected,source_pins={n:digest(HERE/n) for n in ['README.md','PROOF.md','SOURCE_PINS.json','INCOMING_MEMBERS.json','build.py','check.py']},builder_or_incoming_or_parent_code_or_lean_executed=False,canonical_or_common_files_modified=False,scope='Complete finite literal premises and exact leading-form identities. Unbounded ordinary arithmetic/native composition is PROOF.md, not finite testing.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),circuits=len(results),semantic_interfaces=sum(len(r['free_polynomial_interfaces']) for r in results),rejected_actual_graph_controls=len(rejected)),sort_keys=True))
if __name__=='__main__':main()

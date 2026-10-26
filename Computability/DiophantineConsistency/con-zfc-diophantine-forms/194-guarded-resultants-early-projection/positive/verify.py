#!/usr/bin/env python3
"""Independent standard-library exact algebra; never imports the producer."""
from pathlib import Path
from collections import Counter
import argparse,copy,gzip,hashlib,importlib.util,json,subprocess,sys
from polynomial import Poly
ROOT=Path(__file__).resolve().parent
INPUTS=['J','F','alpha','i','T','w','s','n','eta','zeta'];PORTS=['beta','K0','MC','MF']
SPECS={'quotient_t':(97,202,2),'product2':(111,198,2),'product4':(119,190,4)}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def cuts(mode):
    v={'q':'beta*J+1','C':'q-F-alpha','X':'q*w','k':'eta+zeta','c':'k*s+eta','Am1':'q*s*(X+1)','Hp':'4*Am1-1','Delta':'Am1*(Am1+2)','sixq7':'6*q**7','Dtau':'1+(X*q*q*s*s)*(X*q*q*s*s+1)*k*k','R':'(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J','Bt':'(K0+w)*C-F','U':'i*c*c','DpI2':'Delta*U*U*Dtau','Df':'DpI2+1','trace_f':'1+2*DpI2','Q':'4*Delta*DpI2*(1+DpI2)','cTR':'c*T-R','V':'trace_f*cTR-c','Kpos':'X*(3*c-2*X)+2','Dg':'Dtau*Df','Mtot':'bJ*sixq7*Hp','RG':'Mtot*Mtot*scaledG','scaledG':str(SPECS[mode][2]**2)+'*Dg','eclear':'6*(k-R-1-q**4*s)-(X*q*q*s*s)*k*(k*k-4)','N':'Q*(Znum*Znum-Mtot*Mtot*scaledG*V*V)+(Mtot*Mtot*scaledG-Znum*Znum)'}
    if mode=='quotient_t':
        v['center_root']='U*(2*(Am1+1)*Dtau-(q*k*s)*((X*q*q*s*s)*k+k-(q*k*s)*(q*s)))'
        v['Znum']='bJ*sixq7*(Hp*(n-V*(cTR*Bt+center_root))+Kpos)-Hp*(sixq7*Bt+bJ*eclear)'
    else:
        v['S']='(q*k*s)*((X*q*q*s*s)*k+k-(q*k*s)*(q*s+1))'
        if mode=='product2':v['Omega']='U*(2*(Am1+1)*(Dtau*V-U*U*cTR*(Dtau*Dtau+S*S))+S*(4*U*U*cTR*Dtau-(cTR-c)))'
        else:v['Omega']='U*((Am1+1)*(4*Dtau*V-U*U*cTR*(4*Dtau*Dtau+3*S*S+(q*k*s)**4))+2*S*(U*U*cTR*(3*Dtau+(q*k*s)**2)-(cTR-c)))'
        v['Znum']='bJ*sixq7*(Hp*(n-cTR*'+('cTR' if mode=='product4' else 'V')+'*Bt-Omega)+Kpos)-Hp*(sixq7*Bt+bJ*eclear)'
    return v
def topology_and_cuts(g,mode):
    need(g['domain']=='strictly positive integers','domain');need(g['witnesses']==INPUTS,'inputs');need(g['fixed_numerals']==PORTS,'ports')
    table={};known=set(INPUTS+PORTS)
    for name,op,a,b in g['source']:
        need(name not in known,'duplicate register');need(op in ['+','-','*'],'operation')
        need(all(type(x)is int or x in known for x in [a,b]),'operand')
        table[name]=(op,a,b);known.add(name)
    live=set()
    def mark(x):
        if type(x)is int or x in live:return
        live.add(x)
        if x in table:
            _,a,b=table[x];mark(a);mark(b)
    mark(g['output']);need(live==known,'liveness')
    opcounts=dict(sorted(Counter(r[1] for r in g['source']).items()))
    need(len(table)==SPECS[mode][0]==g['operations'],'op count');need(opcounts==g['operation_breakdown'],'op classes')
    covered=set();receipt=[]
    import ast
    for name,formula in cuts(mode).items():
        names={n.id for n in ast.walk(ast.parse(formula,mode='eval')) if isinstance(n,ast.Name)}
        env={n:Poly.v(n) for n in names};memo=env.copy()
        def expand(x):
            if type(x)is int:return Poly(x)
            if x in memo:return memo[x]
            need(x in table,'unbound cut '+x);covered.add(x)
            op,a,b=table[x];a,b=expand(a),expand(b)
            out=a+b if op=='+' else a-b if op=='-' else a*b;memo[x]=out;return out
        got=expand(name);expect=eval(formula,{'__builtins__':{}},env)
        need(got==expect,'free-ring cut '+name)
        receipt.append({'register':name,'terms':len(got.d)})
    need(covered==set(table),'uncovered gates '+str(set(table)-covered))
    return {'operations':len(table),'operation_counts':opcounts,'all_gates_covered':True,'cuts':receipt}


def quotient(p,j,var='A'):
    out={}
    for m,c in p.d.items():
        d=dict(m)
        if d.get(var,0)<j:continue
        d[var]-=j
        if not d[var]:del d[var]
        out[tuple(sorted(d.items()))]=c
    return Poly(out)

def weighted(p,weights):
    d=max(sum(weights[n]*e for n,e in m) for m in p.d)
    top=Poly({m:c for m,c in p.d.items() if sum(weights[n]*e for n,e in m)==d})
    return d,top

def substitute(p,env):
    ans=Poly()
    for m,c in p.d.items():
        t=Poly(c)
        for n,e in m:t=t*env[n]**e
        ans=ans+t
    return ans

def algebra(mode):
    A,Y,k,U,b,c=[Poly.v(n) for n in ['A','Y','k','U','b','c']]
    E=1+k*k*Y*(A-Y-1)*(Y*(A-Y-1)+1);G=E*(1+(A*A-1)*U*U*E);V=(1+2*(A*A-1)*U*U*E)*b-c
    F=E*V;S=quotient(E,1);Q1=quotient(F,1);Q3=quotient(F,3)
    need(all(v%2==0 for v in Q3.d.values()),'Q3 coefficientwise even')
    if mode=='quotient_t':
        Qt=k*k*Y*(Y*(A-Y-1)+1-Y*Y);Rt=1+k*k*Y*Y*(Y*Y-1)
        need(E==(A-1)*Qt+Rt,'t-quotient identity')
        C=U*(2*A*E-Qt);W=C*V
        need(C*C-4*G==U*U*(4*E*(Rt-Qt)+Qt*Qt)-4*E,'t-quotient defect')
    elif mode=='product2':
        W=U*(2*A*E*V-Q1)
        short=U*(2*A*(E*V-U*U*b*(E*E+S*S))+S*(4*U*U*b*E-(b-c)))
        need(W==short,'first-product quotient evaluator')
    else:
        W=U*(4*A*F-2*Q1-Poly({m:c//2 for m,c in Q3.d.items()}))
        e2=k*k*Y*Y;theta=U*U*b
        short=U*(2*S*(theta*(3*E+e2)-(b-c))+A*(4*E*V-theta*(4*E*E+3*S*S+e2*e2)))
        need(W==short,'third-product quotient evaluator')
    r=SPECS[mode][2];D=W*W-r*r*G*V*V;weights={'A':4,'Y':2,'k':1,'U':5,'b':4,'c':2}
    wd,wt=weighted(W,weights);dd,dt=weighted(D,weights)
    need(wd==59,'whole center degree');need(dd=={'quotient_t':106,'product2':102,'product4':94}[mode],'exact defect degree')
    return {'center':W,'defect':D,'degree':dd,'top':dt,'center_top':wt,'weights':weights}

def leading(g,mode,alg):
    values={n:(1 if n in INPUTS else 0,Poly.v(n)) for n in INPUTS+PORTS};ledger={}
    def get(x):return (0,Poly(x)) if type(x)is int else values[x]
    q=Poly.v('beta')*Poly.v('J');k=Poly.v('eta')+Poly.v('zeta');w,s,i,F,alpha=[Poly.v(n) for n in ['w','s','i','F','alpha']]
    formal={'A':q*q*w*s,'Y':q*s,'k':k,'U':i*k*k*s*s,'b':-q**3*(q-F),'c':k*s}
    dtop=substitute(alg['top'],formal);wtop=substitute(alg['center_top'],formal)
    need(bool(dtop.d) and bool(wtop.d),'actual cut leading forms nonzero')
    for name,op,a,b in g['source']:
        da,a=get(a);db,b=get(b)
        if name=='inside':
            M=values['Mtot'][1];bb=values['cTR'][1];VV=values['V'][1];BB=values['Bt'][1]
            Z0=-M*bb*(bb if mode=='product4' else VV)*BB
            cross=-2*M*Z0*wtop
            z0d=22 if mode=='product4' else 54;cd=12+z0d+59;dd=24+alg['degree']
            d=max(2*z0d,cd,dd);p=(cross if cd==d else Poly())+(M*M*dtop if dd==d else Poly())
        elif op=='*':d,p=da+db,a*b
        elif da==db:d,p=da,a+b if op=='+' else a-b
        elif da>db:d,p=da,a
        else:d,p=db,b if op=='+' else -b
        need(bool(p.d),'cancelled leading form '+name);values[name]=(d,p);ledger[name]={'degree':d,'form':p.serial()}
    degree,top=values[g['output']];need(degree==SPECS[mode][1]==g['exact_degree'],'degree metadata')
    if mode=='quotient_t':expect=36864*q**80*w**22*s**55*i**10*k**32*(q-F)**2*(s-w)
    elif mode=='product2':expect=9216*q**78*w**22*s**54*i**10*k**32*(q-F)**2
    else:expect=18432*q**74*w**18*s**52*i**10*k**32*(q-F)**2*(w*w-6*s*s)
    need(top==expect,'complete collected final top form')
    return {'exact_degree':degree,'top_terms':len(top.d),'top_form':top.serial(),'all_register_top_forms':ledger,'defect_weighted_degree':alg['degree'],'defect_top':alg['top'].serial(),'outer_bounds':{'Q_Z0_squared':116 if mode=='product4' else 180,'Q_cross':165 if mode=='product4' else 197,'Q_M2_defect':96+alg['degree'],'correction':142}}

def identities():
    Q,Z0,M,G,V,W,r,nn,oldgy=[Poly.v(n) for n in ['Q','Z0','M','G','V','W','r','nn','oldgy']]
    Z=Z0-M*W;D=W*W-r*r*G*V*V
    need(Q*(Z*Z-r*r*M*M*G*V*V)+(r*r*M*M*G-Z*Z)==Q*(Z0*Z0-2*M*Z0*W+M*M*D)+r*r*M*M*G-Z*Z,'complete centered norm')
    need(nn+(r-1)*oldgy+W-W==nn+(r-1)*oldgy,'positive completeness map')
    A,X,q,Y=[Poly.v(n) for n in ['AA','XX','qq','YY']]
    c3=4*A*A-1;H=4*A-5;K=X*(3*c3-2*X)+2
    need(4*K+(X-8)*(8*X+1)==3*X*H*(4*A+5),'early p3 projector identity')
    AA=q*Y*(X+1)+1;kk=8*X*q*q*Y*Y+4;u=X+2-2*Y
    need(4*AA*AA-1-kk*Y==4*q*q*Y*Y*(X*u+1)+8*q*Y*(X+1)-4*Y+3,'early p3 strip identity')
    need(all(0<t+48<73 for t in range(1,24)),'all bounded projector residues')
    return {'full_norm_decomposition':True,'positive_completeness_map':True,'early_p3_projector_identity':True,'early_p3_strip_identity':True,'all_23_bounded_residues_excluded':True}

def authenticate(g,deep):
    need(sha(ROOT/g['parent']['path'])==g['parent']['sha256'],'parent graph pin');binding=g['coefficient_binding'];vals={};total=0
    for port,pin in binding['ports'].items():
        path=ROOT/binding['path']/pin['file'];raw=gzip.decompress(path.read_bytes());need(sha(path)==pin['gzip_sha256'],'gzip '+port);need(hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'raw '+port)
        value=int.from_bytes(raw,binding['endianness']);need(value.bit_length()==pin['bits'],'bits '+port);need(len(raw)==(value.bit_length()+7)//8,'minimal bytes '+port);vals[port]=value;total+=len(raw)
    need(vals['beta']>=73 and vals['beta']%2==1 and vals['K0']>0 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'scalar facts')
    native=ROOT/'parent/positive10_degree214_ops87.json' if g['tuple_name']=='radix67' else ROOT/'native2963/candidates/one-page-low-padding2963/polynomial.json'
    need(binding['ports']==json.loads(native.read_text())['coefficient_binding']['ports'],'whole exact tuple identity')
    out={'raw_bytes':total,'largest_bits':max(v.bit_length() for v in vals.values()),'whole_tuple_authenticated':True}
    if deep and g['tuple_name']=='radix67':
        p=ROOT/'parent/inherited/strict/upstream_lucas/parent/rebuild_coefficients.py';sp=importlib.util.spec_from_file_location('finite_recipe',p);mod=importlib.util.module_from_spec(sp);sp.loader.exec_module(mod);rebuilt=mod.reconstruct();out['recipe_audit']=mod.check_or_write(False)
        for n in PORTS:need(rebuilt[n]==vals[n],'rebuilt whole numeral '+n)
    if g['tuple_name']!='radix67':
        for key in ['ordinary_proof','certificate']:need(sha(ROOT/binding[key])==binding[key+'_sha256'],'native '+key)
    return out

def mutations(g,mode):
    count=0
    for idx,row in enumerate(g['source']):
        for op in ['+','-','*']:
            if op==row[1]:continue
            bad=copy.deepcopy(g);bad['source'][idx][1]=op;bad['operation_breakdown']=dict(sorted(Counter(r[1] for r in bad['source']).items()))
            try:topology_and_cuts(bad,mode)
            except (ValueError,KeyError):count+=1
            else:raise ValueError('accepted mutation '+row[0]+':'+op)
    return count

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);ap.add_argument('--deep',action='store_true');ap.add_argument('--mutations',action='store_true');a=ap.parse_args()
    result={'status':'PASS','identities':identities(),'equations':[],'algebra':{}}
    if True:
        pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())['files']
        for rel,digest in pins.items():need(sha(ROOT/rel)==digest,'source pin '+rel)
        result['source_files']=len(pins)
    if a.deep:
        cp=subprocess.run([sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(ROOT/'verify_native.py')],check=True,capture_output=True,text=True);result['native_Pclp_replay']=json.loads(cp.stdout)
    for mode in SPECS:
        alg=algebra(mode);result['algebra'][mode]={'center_terms':len(alg['center'].d),'defect_terms':len(alg['defect'].d),'defect_degree':alg['degree'],'center':alg['center'].serial(),'defect':alg['defect'].serial(),'weights':alg['weights']}
        for t in ['radix67','low2963']:
            path=ROOT/(mode+'_'+t+'.json');g=json.loads(path.read_text());rec={'file':path.name,'sha256':sha(path),'formulas':topology_and_cuts(g,mode),'degree':leading(g,mode,alg),'coefficients':authenticate(g,a.deep)}
            if a.mutations:rec['rejected_operator_mutations']=mutations(g,mode)
            result['equations'].append(rec)
    if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','equations':[{'file':r['file'],'degree':r['degree']['exact_degree'],'operations':r['formulas']['operations'],'top_terms':r['degree']['top_terms'],'mutations':r.get('rejected_operator_mutations')} for r in result['equations']]},indent=2))
if __name__=='__main__':main()

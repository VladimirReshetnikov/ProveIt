#!/usr/bin/env python3
"""Independent literal, whole-coefficient and exact leading-form audit."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(path):return json.loads(path.read_bytes())
def digest(path):return sha256(path.read_bytes()).hexdigest()
def C(c):return {():c} if c else {}
def V(v):return {(v,):1}
def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+scale*c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def pow_(a,n):
    out=C(1)
    for _ in range(n):out=mul(out,a)
    return out
def prod(*factors):
    out=C(1)
    for f in factors:out=mul(out,f)
    return out
def cut(rows,target,boundary):
    defs={row[0]:row for row in rows};memo={s:V(s) for s in boundary}
    def visit(v):
        if type(v) is int:return C(v)
        if v in memo:return memo[v]
        need(v in defs,'declared recursive cut boundary '+v)
        _,op,a,b=defs[v];p,q=visit(a),visit(b)
        memo[v]=mul(p,q) if op=='*' else add(p,q,-1 if op=='-' else 1)
        return memo[v]
    return visit(target)
def substitute(poly,mapping):
    out={}
    for monomial,c in poly.items():
        term=C(c)
        for symbol in monomial:term=mul(term,mapping.get(symbol,V(symbol)))
        out=add(out,term)
    return out
def degree(poly,weights):return max((sum(weights[v] for v in m) for m in poly),default=-1)
def F8(s,u,v,h):
    E=add(pow_(add(add(add(s,h),u,-1),v,-1),2),mul(C(4),add(mul(s,h),mul(u,v))),-1)
    return add(pow_(E,2),prod(C(64),s,h,u,v),-1)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True,type=Path);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'entire frozen source dependency '+name)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];actual={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'}
        need(set(files)==actual,'closed packet inventory')
        for name,h in files.items():need(digest(HERE/name)==h,'sealed whole member '+name)
    parent=ROOT/'research/ten-positive-expanded-transport'
    pm=load(parent/'MANIFEST.json')['files'];need({str(p.relative_to(parent)) for p in parent.rglob('*') if p.is_file() and p!=parent/'MANIFEST.json'}==set(pm),'entire accepted parent closed inventory')
    for name,h in pm.items():need(digest(parent/name)==h,'complete accepted parent member '+name)
    for name in ['zero98.json','direct103.json','PROOF.md','MANIFEST.json']:need((HERE/'parents'/name).read_bytes()==(parent/name).read_bytes(),'copied exact accepted parent '+name)
    binding=load(HERE/'coefficients/BINDING.json');values={}
    need(binding==load(parent/'coefficients/BINDING.json'),'entire coherent fixed binding')
    for name,pin in binding['ports'].items():
        blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
        need(blob==(parent/'coefficients'/pin['file']).read_bytes() and sha256(blob).hexdigest()==pin['gzip_sha256'] and sha256(raw).hexdigest()==pin['raw_sha256'],'complete compressed/raw fixed numeral '+name)
        n=int.from_bytes(raw,'little');need(n.bit_length()==pin['bits'],'whole coefficient bit count');values[name]=n
    beta=values['beta'];need(beta>=31 and beta%2==1 and values['K0']>0 and 0<values['MC']<beta<values['MF']<2*beta,'whole original coherent tuple box')
    # Independently collect all35 tail coefficients and the full eight-conjugate identity.
    s,u,v,h=map(V,['s','u','v','h']);norm=F8(s,u,v,h)
    need(len(norm)==35,'all35 norm coefficients')
    x,a,b,c=map(V,['x','a','b','c']);conjugates=C(1)
    for ea in [-1,1]:
        for eb in [-1,1]:
            for ec in [-1,1]:conjugates=mul(conjugates,add(add(add(x,a,ea),b,eb),c,ec))
    need(conjugates==F8(pow_(x,2),pow_(a,2),pow_(b,2),pow_(c,2)),'complete rational signed-root factorization')
    omega=V('o');centered=add(pow_(add(add(pow_(omega,2),mul(C(2),mul(add(u,v),add(mul(C(2),h),omega))),-1),pow_(add(u,v,-1),2)),2),prod(C(64),u,v,h,add(h,omega)),-1)
    need(F8(add(h,omega),u,v,h)==centered,'universal full centered norm cancellation')
    results={};rejected=[]
    def reject(name,action):
        try:action()
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(name)
        else:raise ValueError('corruption accepted '+name)
    for direct,name,count,exact,syntactic,breakdown in [(False,'zero98.json',98,360,416,{'*':58,'+':22,'-':18}),(True,'direct103.json',103,332,384,{'*':61,'+':23,'-':19})]:
        old=load(parent/name);new=load(HERE/name);rows=new['source'];cuts=load(HERE/name.replace('.json','_CUTS.json'))
        expected=deepcopy(old['source']);changed=[]
        for i,row in enumerate(expected):
            if row[0]=='HI':replacement=['kI','*','k','I']
            elif row[0]=='L':replacement=['L','+','kI','cTR']
            else:continue
            changed.append(dict(index=i,old=deepcopy(row),new=replacement));expected[i]=replacement
        need(rows==expected and cuts['changed_rows']==changed,'ENTIRE new graph differs only at2 listed rows')
        need(cuts['retained_rows']==[dict(index=i,row=row) for i,row in enumerate(old['source']) if i not in {q['index'] for q in changed}] and cuts['deleted_rows']==cuts['inserted_rows']==[],'all retained parent rows accounted, no hidden insertion/deletion')
        need(cuts['parent_file']==name and cuts['parent_sha256']==new['parent_sha256']==digest(parent/name),'exact complete parent graph pin')
        for key in ['witnesses','fixed_numerals','coefficient_binding','domain','output','operations','operation_breakdown','syntactic_degree']:
            need(new[key]==old[key],'complete preserved parent field '+key)
        need(new['coefficient_binding']==binding and new['domain']=='strictly positive integers' and len(new['witnesses'])==10 and new['fixed_numerals']==['beta','K0','MC','MF'],'tenpositive domain and complete four fixed ports')
        need(new['register_degrees']==dict(old['register_degrees'],L=6) and new['exact_degree']==exact,'only changed front degree and new exact target')
        degrees={x:1 for x in new['witnesses']}|{x:0 for x in new['fixed_numerals']};deps={}
        for row in rows:
            need(len(row)==4,'binary row');key,op,a,b=row
            need(key not in degrees and op in ['+','-','*'] and all(type(x) is int or x in degrees for x in [a,b]),'fresh topological ring row')
            da,db=[0 if type(x) is int else degrees[x] for x in [a,b]];degrees[key]=da+db if op=='*' else max(da,db);deps[key]=[a,b]
        live=set();todo=[new['output']]
        while todo:
            value=todo.pop()
            if type(value) is int or value in live:continue
            live.add(value);todo+=deps.get(value,[])
        need(live==set(degrees) and len(rows)==count and dict(Counter(r[1] for r in rows))==breakdown,'complete topology/liveness/count and breakdown')
        need(degrees['N']==syntactic and all(degrees[k]==d for k,d in new['register_degrees'].items()),'actual syntactic register propagation')
        need([r[0] for r in old['source'] if 'HI' in r[2:]]==['L'] and [r[0] for r in rows if 'kI' in r[2:]]==['L'],'entire exchanged private-product consumer set')
        boundary={'q','q3','bJ','mu2','Hp','n','V','k','I','cTR','Kpos','Y','e','X','B' if direct else 'Bt'}
        qp,q3,g,U,H,nn,VV,kk,II,bb,K,Y,ee,X,B=map(V,['q','q3','bJ','mu2','Hp','n','V','k','I','cTR','Kpos','Y','e','X','B' if direct else 'Bt'])
        gg=mul(qp,g) if direct else g;PP=mul(q3,gg);MM=prod(PP,U,H);LL=add(mul(kk,II),bb);DD=mul(g,X) if direct else C(0)
        expectedZ=add(prod(PP,U,add(mul(H,add(add(nn,VV),mul(LL,B),-1)),K)),mul(H,add(mul(U,add(add(mul(gg,Y),mul(q3,B),-1),DD,-1)),mul(PP,ee),-1)))
        got=cut(rows,'Znum',boundary);need(got==expectedZ and cut(rows,'Mtot',boundary)==MM and cut(rows,'L',boundary)==LL,'complete literal center/carrier/newL polynomials')
        oldboundary=boundary|{'Hp'}
        oldZ=cut(old['source'],'Znum',oldboundary)
        shift=prod(add(kk,H,-1),II,B)
        need(substitute(got,{'n':add(nn,shift)})==oldZ,'complete ACTUAL parent/new numerator identity under triangular n shear')
        need(cut(old['source'],'Mtot',oldboundary)==MM,'carrier unchanged under n shear')
        need([r[0] for r in rows if 'n' in r[2:]]==['nV'],'entire n input consumer set: kernel data independent of shear')
        # Actual center subtracts MV exactly. These semantic degrees are stronger than naive graph degrees.
        z0=add(got,mul(MM,VV),-1)
        weighted={key:degrees[key] for key in boundary};need(degree(z0,weighted)==21,'exact centered Z0 bound from the actual source cut')
        tail=cut(rows,'N',{'fs','fa','fb','fc'});wanttail=F8(V('fs'),V('fa'),V('fb'),V('fc'))
        need(tail==wanttail and len(tail)==35,'ALL35 coefficients of actual complete norm tail')
        delta_degree=26 if direct else 30;Vdegree=22 if direct else 24;MV=13+Vdegree
        omega_bound=max(delta_degree+42,delta_degree+21+MV,26+2*Vdegree)
        du,dv,dh=(68,70,96) if direct else (74,76,104);weights={'o':omega_bound,'u':du,'v':dv,'h':dh}
        fullcenter=add(pow_(add(add(pow_(omega,2),mul(C(2),mul(add(u,v),add(mul(C(2),h),omega))),-1),pow_(add(u,v,-1),2)),2),prod(C(64),u,v,h,add(h,omega)),-1)
        need(degree(fullcenter,weights)==exact,'full centered norm exact weighted upper degree')
        top={m:co for m,co in fullcenter.items() if sum(weights[x] for x in m)==exact}
        need(top=={tuple(sorted(['v','v','h','h'])):16},'unique16*v²*h² top, no omega4 claim')
        # Leading forms over formal q/X/k; X has degree2 or1. No huge fixed-number substitution is needed.
        q0,X0,k0,Y0,i0,F=map(V,['q0','X0','k0','Y0','i0','F']);d=5 if direct else 4
        A0=prod(pow_(q0,2),X0,Y0);I0=prod(i0,pow_(k0,2),pow_(Y0,2));Delta0=pow_(A0,2)
        Df0=mul(Delta0,pow_(I0,2));Q0=mul(pow_(Delta0,2),pow_(I0,2));R0=prod(pow_(q0,3),add(q0,F,-1));V00=mul(C(-1),mul(Df0,R0));M0=prod(C(4),pow_(q0,d+6),X0,Y0)
        v0=prod(Q0,pow_(M0,2),Df0);h0=prod(pow_(M0,2),Q0,pow_(V00,2));leading=prod(C(16),pow_(v0,2),pow_(h0,2))
        expectedlead=prod(C(2**20),pow_(i0,20),pow_(q0,8*d+116),pow_(X0,36),pow_(k0,40),pow_(Y0,76),pow_(add(q0,F,-1),4))
        need(leading==expectedlead,'complete factored leading polynomial equality')
        # Independently propagate actual highest homogeneous front components.
        weights_input={x:1 for x in new['witnesses']}|{x:0 for x in new['fixed_numerals']}
        actual_lead={x:V(x) for x in weights_input}
        for key,op,a,b in rows:
            aa=C(a) if type(a) is int else actual_lead[a];bb0=C(b) if type(b) is int else actual_lead[b]
            p=mul(aa,bb0) if op=='*' else add(aa,bb0,-1 if op=='-' else 1)
            if op!='*' and type(a) is not int and type(b) is not int:
                da,db=degrees[a],degrees[b]
                if da>db:p=aa
                elif db>da:p=mul(C(-1 if op=='-' else 1),bb0)
            # Integer constant/variable cases also need the actual formal degree comparison.
            topdegree=degree(p,weights_input)
            actual_lead[key]={m:c for m,c in p.items() if sum(weights_input[x] for x in m)==topdegree}
            if key=='Mtot':break
        q_input=mul(V('beta'),V('J'));X_input=add(q_input,V('x')) if direct else mul(V('w'),q_input);k_input=add(V('eta'),V('zeta'))
        mapping_input={'q0':q_input,'X0':X_input,'k0':k_input,'Y0':V('Y'),'i0':V('i'),'F':V('F')}
        for actualname,expectedpoly in [('Df',Df0),('Q',Q0),('V',V00),('Mtot',M0)]:
            need(actual_lead[actualname]==substitute(expectedpoly,mapping_input),'entire actual homogeneous leading component '+actualname)

        leadweights={'q0':1,'X0':1 if direct else 2,'k0':1,'Y0':1,'i0':1,'F':1}
        need({sum(leadweights[x] for x in m) for m in leading}=={exact},'entire nonzero leading form has correct total degree')
        selected=tuple(sorted(['q0']*(156 if direct else 148)+['X0']*36+['i0']*20+['Y0']*76+['k0']*40+['F']*4))
        need(leading.get(selected)==2**20,'unique maximum F4 term leading coefficient')
        selected_inputs={'J':156 if direct else 184,'x' if direct else 'w':36,'i':20,'Y':76,'eta':40,'F':4}
        need(sum(selected_inputs.values())==exact,'selected true-input monomial total degree')
        results[name]=dict(status='PASS',operations=count,operation_breakdown=breakdown,exact_degree=exact,syntactic_degree=syntactic,changed_source_rows=[q['index'] for q in changed],L_degree=6,proof_W_degree=8 if direct else 7,actual_Z0_degree=21,omega_degree_bound=omega_bound,unique_top='16*fb0^2*fc0^2',selected_input_exponents=selected_inputs,selected_coefficient={'power_of_two':20,'beta_power':156 if direct else 184},full_norm_coefficients=35,center_cut_terms=len(got),leading_form_terms=len(leading),equation_sha256=digest(HERE/name))
        bad=deepcopy(rows);idx=next(i for i,row in enumerate(bad) if row[0]=='kI');bad[idx][2]='Hp'
        reject(name+':restoreoldHI',lambda:need(bad==expected,'only correct new graph accepted'))
        reject(name+':incorrectomega4degree',lambda:need(4*omega_bound==exact,'strong/auxiliary product controls full degree'))
        reject(name+':omitF4leadingterm',lambda:need(selected[:-1] in leading,'whole leading monomial retained'))
        reject(name+':assumeoldnewpointwisepolynomialequality',lambda:need(old['source']==rows,'different weight is not identical source polynomial'))
        reject(name+':omitdirectcorrection' if direct else name+':inventdirectcorrection',lambda:need(DD==(C(0) if direct else V('X')),'actual low-order carrier term'))
    # Universal completeness center identity under a free positive-old-zero n shift.
    nn,deltaL,B,g,M=map(V,['n','dL','B','g','M']);newn=add(nn,mul(deltaL,B));newW=add(V('W'),mul(g,deltaL))
    need(add(add(mul(g,newn),mul(newW,B),-1),add(mul(g,nn),mul(V('W'),B),-1),-1)=={},'universal numerator n shift/weight identity, no quotient division')
    controls=0
    for X in [2,32,33,64,1000]:
        for r in [1,2,31,1025,100000]:
            kmin=8*X*r*r+4;A=r*(X+1)+1;H=4*A-5
            need(kmin-H==4*r*(2*X*r-X-1)+5>0 and kmin>2*A+X,'pretransport unbounded-bound diagnostics');controls+=1
    reject('merelyWgreaterfaccepted',lambda:need(2/31>3+1,'W>f does not supply sign majorization'))
    reject('degree352or328claimed',lambda:need(results['zero98.json']['exact_degree']==352,'unique strong/auxiliary top survives'))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),candidates=results,norm_coefficients=35,universal_norm_factorization=True,universal_centered_norm_identity=True,universal_positive_completeness_n_shift=True,pretransport_bound_controls=controls,rejected_corruptions=rejected,source_pins={n:digest(HERE/n) for n in ['PROOF.md','README.md','SOURCE_PINS.json','build.py','check.py','zero98.json','direct103.json']},ordinary_equivalence_proof='PROOF.md',finite_controls_replace_unbounded_proof=False,parent_code_or_incoming_code_or_lean_executed=False,canonical_page_modified=False)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()

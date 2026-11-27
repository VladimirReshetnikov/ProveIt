#!/usr/bin/env python3
"""Reproduce a dominated positive q-cube input normalization; no parent code import."""
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
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def C(n):return {():n} if n else {}
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
def sub(p,mapping):
    r={}
    for monomial,c in p.items():
        term=C(c)
        for s in monomial:term=mul(term,mapping.get(s,V(s)))
        r=add(r,term)
    return r
def cut(rows,target,boundary):
    definitions={r[0]:r for r in rows};memo={s:V(s) for s in boundary}
    def visit(s):
        if type(s) is int:return C(s)
        if s in memo:return memo[s]
        need(s in definitions,'declared cut boundary '+s)
        _,op,a,b=definitions[s];aa,bb=visit(a),visit(b)
        memo[s]=mul(aa,bb) if op=='*' else add(aa,bb,-1 if op=='-' else 1)
        return memo[s]
    return visit(target)
def degree(p,weights):return max((sum(weights[x] for x in m) for m in p),default=-1)
def norm(s,u,v,h):
    e=add(power(add(add(add(s,h),u,-1),v,-1),2),prod(C(4),add(mul(s,h),mul(u,v))),-1)
    return add(power(e,2),prod(C(64),s,u,v,h),-1)
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'whole immutable dependency '+name)
    for dirname in pins['closed_parents']:
        parent=ROOT/dirname;manifest=load(parent/'MANIFEST.json')['files']
        need(set(manifest)=={str(p.relative_to(parent)) for p in parent.rglob('*') if p.is_file() and p!=parent/'MANIFEST.json'},'complete accepted parent inventory '+dirname)
        for name,h in manifest.items():need(digest(parent/name)==h,'whole accepted parent member '+name)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];need(set(files)=={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'},'closed own inventory')
        for name,h in files.items():need(digest(HERE/name)==h,'whole sealed member '+name)
    parent=ROOT/'research/ten-positive-index-weight';old=load(parent/'zero98.json');new=load(HERE/'normalized97.json');rows=new['source'];oldrows=old['source'];byname={r[0]:r for r in oldrows}
    # Independently account every row: two existing powers move before Y's first use,
    # one product is inserted, two private products disappear, four consumers rebind.
    expected=[]
    replacements={'P1mu2':['P1mu2','*','bJ','mu2'],'qm1Y':['qm1Y','*','bJ','y'],'inner':['inner','-','qm1Y','Bt'],'P1e':['P1e','*','bJ','e']}
    for row in oldrows:
        if row[0]=='kY':expected.extend([byname['q2'],byname['q3'],['Y','*','q3','y']])
        if row[0] in ['q2','q3','P1','q3WBt']:continue
        expected.append(replacements.get(row[0],row))
    need(rows==expected,'ENTIRE exact source transformation')
    need(new['witnesses']==['y' if s=='Y' else s for s in old['witnesses']] and new['domain']==old['domain']=='strictly positive integers','whole ten-positive input substitution')
    binding=deepcopy(old['coefficient_binding']);binding['path']='../ten-positive-index-weight/coefficients/'
    need(new['fixed_numerals']==old['fixed_numerals'] and new['coefficient_binding']==binding and new['parent_sha256']==digest(parent/'zero98.json'),'entire accepted four-port binding')
    for name,pin in binding['ports'].items():
        blob=(HERE/binding['path']/pin['file']).read_bytes();raw=gzip.decompress(blob)
        need(sha256(blob).hexdigest()==pin['gzip_sha256'] and sha256(raw).hexdigest()==pin['raw_sha256'] and int.from_bytes(raw,'little').bit_length()==pin['bits'],'every byte of coherent fixed port '+name)
    inputweights={s:1 for s in new['witnesses']}|{s:0 for s in new['fixed_numerals']};degrees=dict(inputweights);deps={}
    for key,op,a,b in rows:
        need(key not in degrees and op in ['+','-','*'] and all(type(x) is int or x in degrees for x in [a,b]),'fresh topological binary row')
        da,db=[0 if type(x) is int else degrees[x] for x in [a,b]];degrees[key]=da+db if op=='*' else max(da,db);deps[key]=[a,b]
    live=set();todo=[new['output']]
    while todo:
        n=todo.pop()
        if type(n) is int or n in live:continue
        live.add(n);todo+=deps.get(n,[])
    breakdown=dict(Counter(r[1] for r in rows));need(live==set(degrees) and len(rows)==new['operations']==97 and breakdown==new['operation_breakdown']=={'*':57,'+':22,'-':18},'all rows and ports live; literal operation census')
    need(new['register_degrees']=={k:degrees[k] for k in deps} and new['syntactic_degree']==degrees['N']==672 and new['exact_degree']==572,'complete degree metadata')
    boundary={'q3','bJ','mu2','Hp','n','V','L','Bt','Kpos','Y','y','e'}
    q3,g,U,H,n,VV,L,B,K,Y,y,e=map(V,['q3','bJ','mu2','Hp','n','V','L','Bt','Kpos','Y','y','e'])
    oldZ=cut(oldrows,'Znum',boundary);newZ=cut(rows,'Znum',boundary);oldM=cut(oldrows,'Mtot',boundary);newM=cut(rows,'Mtot',boundary)
    formula=add(prod(g,U,add(mul(H,add(add(n,VV),mul(L,B),-1)),K)),mul(H,add(mul(U,add(mul(g,y),B,-1)),mul(g,e),-1)))
    need(newZ==formula and newM==prod(g,U,H),'entire actual normalized numerator and carrier')
    need(sub(oldZ,{'Y':mul(q3,y)})==mul(q3,newZ) and oldM==mul(q3,newM),'universal WHOLE center/carrier identities under Y=q3*y')
    s,u,v,h,t=map(V,['s','u','v','h','t']);tail=cut(rows,'N',{'fs','fa','fb','fc'});f8=norm(s,u,v,h)
    need(tail==sub(f8,{'s':V('fs'),'u':V('fa'),'v':V('fb'),'h':V('fc')}) and len(f8)==35,'all35 actual complete norm coefficients')
    need(sub(f8,{k:mul(t,V(k)) for k in ['s','u','v','h']})==mul(power(t,4),f8),'universal complete norm homogeneity; t=q^6 gives q^24')
    z0=add(newZ,mul(newM,VV),-1);need(degree(z0,{k:degrees[k] for k in boundary})==27,'actual centered numerator upperdegree27')
    omega=max(degrees['delta']+54,degrees['delta']+27+degrees['Mtot']+degrees['V'],2*degrees['Mtot']+2*degrees['V']);need(omega==138,'full omega bound from actual degree premises')
    o=V('o');centered=add(power(add(add(power(o,2),prod(C(2),add(u,v),add(mul(C(2),h),o)),-1),power(add(u,v,-1),2)),2),prod(C(64),u,v,h,add(h,o)),-1)
    need(norm(add(h,o),u,v,h)==centered,'universal full centered cancellation')
    weights={'o':138,'u':110,'v':118,'h':168};top={m:c for m,c in centered.items() if sum(weights[x] for x in m)==572}
    need(degree(centered,weights)==572 and top=={tuple(sorted(['v','v','h','h'])):16},'unique degree572 top16v²h²; final product at most564')
    q0,X0,k0,y0,i0,Ta=map(V,['q0','X0','k0','y0','i0','Ta']);Y0=prod(power(q0,3),y0);c0=mul(k0,Y0);I0=mul(i0,power(c0,2));A0=prod(power(q0,2),Y0,X0)
    Df0=prod(power(A0,2),power(I0,2));Q0=prod(power(A0,4),power(I0,2));b0=mul(c0,Ta);V0=mul(Df0,b0);M0=prod(C(4),power(q0,5),A0)
    leading={x:V(x) for x in inputweights}
    for key,op,a,b in rows:
        aa=C(a) if type(a) is int else leading[a];bb=C(b) if type(b) is int else leading[b]
        da,db=[0 if type(x) is int else degrees[x] for x in [a,b]]
        term=mul(aa,bb) if op=='*' else (aa if da>db else mul(C(-1 if op=='-' else 1),bb) if db>da else add(aa,bb,-1 if op=='-' else 1))
        need(term,'nonzero actual leading component '+key);leading[key]=term
        if key=='Mtot':break
    mapping={'q0':mul(V('beta'),V('J')),'X0':prod(V('w'),V('beta'),V('J')),'k0':add(V('eta'),V('zeta')),'y0':V('y'),'i0':V('i'),'Ta':add(V('T'),V('alpha'))}
    for name,p in [('Y',Y0),('c',c0),('I',I0),('Df',Df0),('Q',Q0),('cTR',b0),('V',V0),('Mtot',M0)]:need(leading[name]==sub(p,mapping),'entire actual homogeneous front '+name)
    v0=prod(Q0,power(M0,2),Df0);h0=prod(power(M0,2),Q0,power(V0,2));lead=prod(C(16),power(v0,2),power(h0,2));want=prod(C(2**20),power(q0,352),power(X0,36),power(i0,20),power(y0,80),power(k0,44),power(Ta,4))
    need(lead==want,'complete factored degree572 leading polynomial')
    want_input=sub(want,mapping);selected=tuple(sorted(['beta']*388+['J']*388+['w']*36+['i']*20+['y']*80+['eta']*44+['T']*4))
    need(want_input.get(selected)==2**20 and {sum(inputweights[x] for x in m) for m in want_input}=={572},'actual selected nonzero coefficient2^20 beta^388')
    rejected=[]
    def reject(label,claim):
        try:need(claim,label)
        except ValueError:rejected.append(label)
        else:raise ValueError('corruption accepted '+label)
    wrong=deepcopy(rows);next(r for r in wrong if r[0]=='P1e')[2]='q3'
    reject('retainwrongcarrierinerrorwire',wrong==expected);reject('claim96operations',len(rows)==96);reject('claimdegree564',degree(centered,weights)==564);reject('claimq6carrierfactor',sub(oldZ,{'Y':mul(q3,y)})==mul(power(q3,2),newZ));reject('oldRleadingstilldominatesb',degrees['R']>=degrees['cTR']);reject('ordinaryequalityatunchangedinput',oldrows==rows)
    dominator=load(ROOT/'research/ten-positive-square-weight-tradeoff/zero97.json');need(dominator['operations']==97 and dominator['exact_degree']==368<572,'accepted complete97/368 strictly dominates operation-degree pair')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),verdict='DOMINATED; no new operation/degree frontier',operations=97,operation_breakdown=breakdown,exact_degree=572,syntactic_degree=672,full_norm_coefficients=35,whole_center_and_carrier_factor='q^3',whole_output_factor='q^24',omega_degree_bound=138,centered_numerator_degree_bound=27,unique_top='16*fb0^2*fc0^2',selected_input_exponents={'J':388,'w':36,'i':20,'y':80,'eta':44,'T':4},selected_coefficient={'power_of_two':20,'beta_power':388},dominated_by={'operations':97,'exact_degree':368},rejected_claims=rejected,source_pins={n:digest(HERE/n) for n in ['README.md','SOURCE_PINS.json','normalized97.json','check.py']},parent_or_incoming_code_or_lean_executed=False,canonical_or_common_files_modified=False,finite_controls_replace_unbounded_proof=False)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()

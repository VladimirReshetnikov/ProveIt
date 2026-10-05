#!/usr/bin/env python3
"""Fresh245 static constructor plus independent hand-derived cut diagnostics.
No saved DAG is run, imported, symbolically evaluated or degree propagated.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS={
 'neary_woods_positive_first_production247_tesla.md':'9cb9da3c211fecbe3129421b23a16c747d8d1bf7b6365cf6320c426733ffd56a',
 'neary_woods_positive_first_production247_tesla.json':'85e91368ddb3b4764879cd8591d730a60ed95e569026ec8ad7a0b6600739968e',
 'neary_woods_positive_upper248_tesla.md':'f3329cf28090e39a219ac4e3d8882b99fc5bab72ae0507647a193cbdb514d557',
 'neary_woods_hierarchical_history250_tesla.md':'1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330',
}
def need(ok,label):
    if not ok:raise RuntimeError(label)
def digest(data):return hashlib.sha256(data).hexdigest()
def canon(rows):return digest(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def data_path(name):
    path=WIP/name
    return path if path.exists() else Path('/tmp')/name

def arguments(row):return {x for x in row[2:] if isinstance(x,str)}
def users(rows,name):return sorted(r[0] for r in rows if name in arguments(r))
def topo_and_ledger(rows,ports,output,recipes):
    pending=list(rows);ordered=[];seen=set(ports)
    while pending:
        available=[i for i,r in enumerate(pending) if arguments(r)<=seen]
        need(available,'acyclic metadata')
        row=pending.pop(available[0]);need(row[0] not in seen,'single producer')
        seen.add(row[0]);ordered.append(row)
    definitions={r[0]:r for r in ordered};live=set();stack=[output];roles=set()
    while stack:
        name=stack.pop()
        if name in live:continue
        live.add(name)
        if name in definitions:stack.extend(arguments(definitions[name]))
    need(set(definitions)<=live and set(ports)<=live,'every row and port live')
    for row in ordered:
        need(len(row)==4 and row[1] in ('+','-','*'),'instruction shape')
        for x in row[2:]:
            if isinstance(x,str) or type(x) is int:continue
            need(type(x) is dict and set(x)=={'fixed_numeral'},'fixed numerator shape')
            roles.add(x['fixed_numeral'])
    need(roles==set(recipes),'fixed numeral roles live')
    ledger={'total':len(ordered),'M':sum(r[1]=='*' for r in ordered),
      'A':sum(r[1]!='*' for r in ordered),'all_rows_and_ports_live':True,
      'fixed_numeral_roles':len(roles),'canonical_source_sha256':canon(ordered)}
    return ordered,ledger

def construct(parent):
    source=parent['source'];lookup={r[0]:r for r in source}
    need((len(source),parent['ledger']['M'],parent['ledger']['A'])==(247,129,118),'parent247')
    guards={
      'hist__Shat2':['hist__group_sum__58'],
      'hist__group_sum__58':['hist__linear_coefficient__165','hist__selector_sum__6','tree_group12'],
      'tree_group12':['hist__pack_sum__63','tree_mask_product'],
      'hist__linear_constant__168':['hist__U_update__36'],
      'hist__global_bound':['hist__P__10'],
    }
    for port,wanted in guards.items():need(users(source,port)==sorted(wanted),'private cut '+port)
    wanted={
      'hist__group_sum__58':['hist__group_sum__58','+','hist__Shat1','hist__Shat2'],
      'tree_group12':['tree_group12','-','hist__group_sum__58',2],
      'hist__linear_constant__168':['hist__linear_constant__168','-','hist__linear_sum__167',{'fixed_numeral':'upper_constant'}],
      'hist__J__7':['hist__J__7','-','hist__selector_sum__6',3],
      'hist__linear_sum__166':['hist__linear_sum__166','+','hist__linear0_sum__20','hist__linear_group__164'],
    }
    for name,row in wanted.items():need(lookup[name]==row,'literal '+name)
    recipes=dict(parent['fixed_numeral_recipes'])
    need(recipes['upper_offset']=='2^(beta+1)+1' and recipes['upper_constant']=='2^(beta+2)+3','fixed upper recipe')
    need([r[0] for r in source if {'fixed_numeral':'upper_offset'} in r[2:]]==['hist__linear_coefficient__165'],'offset consumer')
    del recipes['upper_constant'];recipes['upper_offset']='2^(beta+1)'
    removed={'hist__group_sum__58','tree_group12','hist__linear_constant__168'}
    aliases={'hist__group_sum__58':'hist__G12','tree_group12':'hist__G12','hist__linear_constant__168':'hist__linear_sum__167'}
    inserted=['group_global_slack','+','hist__global_bound','hist__Shat1']
    provisional=[inserted];edits=[]
    for row in source:
        if row[0] in removed:continue
        new=[aliases.get(x,x) if isinstance(x,str) else x for x in row]
        if row[0]=='hist__J__7':new=[row[0],'-','hist__selector_sum__6',1]
        elif row[0]=='hist__P__10':new=[row[0],'+','group_global_slack','hist__global_sum__14']
        elif row[0]=='hist__linear_sum__166':new=[row[0],'+','hist__linear0_sum__20','hist__J__7']
        if new!=row:edits.append({'before':row,'after':new})
        provisional.append(new)
    auxiliaries=['hist__G12' if x=='hist__Shat2' else x for x in parent['auxiliaries']]
    rows,ledger=topo_and_ledger(provisional,parent['parameters']+auxiliaries,parent['output'],recipes)
    need((ledger['total'],ledger['M'],ledger['A'],len(auxiliaries),len(edits))==(245,129,116,43,8),'full245 ledger')
    child={k:parent[k] for k in ['parameters','domains','merged','fixed_u9_recipe','output','comparisons','multiplier_port','scaled_factor_semantics']}
    child.update(source=rows,auxiliaries=auxiliaries,fixed_numeral_recipes=recipes,ledger=ledger,
      certificate={'total':244,'M':129,'A':115,'comparisons':1,'positive_witnesses':43},
      manual_degree_upper_bound=936,exact_degree_claimed=False,parent_source_sha256=canon(source),
      delta={'deleted':[lookup[n] for n in sorted(removed)],'added':[inserted],'edited':edits,
        'literal_retained_row_records':236,'topological_reorder':True,'consumer_guards':guards,
        'changed_numeral_role':'upper_offset','deleted_numeral_role':'upper_constant'},
      inverse_to_parent={'hist__Shat2':'hist__G12-hist__Shat1+2','hist__global_bound':'hist__global_bound+hist__Shat1',
        'upper_offset':'new upper_offset+1','upper_constant':'2*new upper_offset+3'},
      scope='Complete U9 positive-zero bijection; restore missing selector positivity via last controller lane before parent invocation.')
    return child

# Handwritten sparse cut identities. These functions never receive source rows.
N=10
def const(value):return {(0,)*N:value} if value else {}
def variable(i):
    p=[0]*N;p[i]=1;return {tuple(p):1}
def summation(*polys):
    answer={}
    for poly in polys:
        for mon,value in poly.items():answer[mon]=answer.get(mon,0)+value
    return {mon:value for mon,value in answer.items() if value}
def scale(poly,c):return {m:v*c for m,v in poly.items() if v*c}
def multiply(a,b):
    result={}
    for m,u in a.items():
        for n,v in b.items():
            e=tuple(x+y for x,y in zip(m,n));result[e]=result.get(e,0)+u*v
    return {m:v for m,v in result.items() if v}
def cut_checks():
    G,H,S0,S3,g,rest,P,L0,a,pstar=[variable(i) for i in range(N)]
    oldS2=summation(G,scale(H,-1),const(2))
    oldGroup=summation(H,oldS2);oldJ=summation(oldGroup,S0,S3,const(-3))
    newJ=summation(G,S0,S3,const(-1))
    oldGlobal=summation(rest,g,H);newGlobal=summation(rest,summation(g,H))
    oldTree=summation(oldGroup,const(-2));newTree=G
    oldUpper=summation(L0,S0,S3,multiply(summation(a,const(1)),oldGroup),scale(summation(scale(a,2),const(3)),-1))
    newUpper=summation(L0,newJ,multiply(a,G))
    pp=multiply(P,P);pack=summation(multiply(P,S0),multiply(pp,summation(H,const(-1))))
    oldController=summation(oldTree,pack);newController=summation(G,pack)
    oldMask=summation(oldJ,multiply(P,summation(oldJ,multiply(pstar,oldTree))))
    newMask=summation(newJ,multiply(P,summation(newJ,multiply(pstar,G))))
    pairs=[(oldJ,newJ),(oldGlobal,newGlobal),(oldTree,newTree),(oldUpper,newUpper),(oldController,newController),(oldMask,newMask)]
    for n,(left,right) in enumerate(pairs):need(left==right,'handwritten identity '+str(n))
    return {'identities':6,'independent_variables':N,'scope':'Selector,global,group,upper transport,controller and mask cuts only.'}

def scalar_and_lane_checks():
    signed=minus=height1=overflow_examples=dyadic=0
    for ch in [32,64]:
     for D in [1,2]:
      b=ch*D
      for J in range(2,6):
       for eps in [-1,1]:
        P=(b-1)*J+eps
        for G in range(1,J):
         for S0 in range(1,J-G+1):
          S3=J-G-S0
          for S1 in sorted({0,J,P//2,P-10}):
           g=P-S1-8
           need(g>0,'positive seven-summand input')
           C=G+P*S0+P*P*S1;Mtree=J+P*(J+(b-1)*J*G);Mb=(b-1)*C
           HU=HV=2;ZU=V0=1;V1=0
           Hb=HU+P*HV+P*P*HV;Zb=ZU+P*V0+P*P*V1;Hr=HU+P*HV;Mr=(1+P)*(D-1)*J;T=P**8
           H0=Hb+P**3*C+P**6*Hr;M0=Mb+P**3*Mtree+P**6*Mr;Z=Zb+P**3*C+P**6*Hr
           need(C<P**3 and Mtree<=(P-2)*(1+P+P*P),'raw masks')
           need(Mb<(P+1)*P**3 and Mb+P**3*Mtree<P**6,'new overflow bound')
           need(0<=H0<T and 0<=M0<T and 0<=Z<T,'native top fields')
           need(H0+2*T-Z>=T+1 and M0+T-Z>=1 and b*T-H0-M0-3*T+Z>=(b-5)*T+2,'positive truth margins')
           signed+=1;minus+=eps<0;height1+=D==1;overflow_examples+=Mb>=2*P**3
    for b in [32,64]:
     for t in [2,3]:
      P=b**t;J=(P-1)//(b-1)
      for G in sorted({1,J//2,J-1}):
       for S0 in sorted({1,J-G}):
        if S0<=0:continue
        G03=J-G
        for S1 in sorted({0,1,G,G+1,J,J+1,P//2,P-10}):
         if not 0<=S1<P:continue
         C=G+P*S0+P*P*S1;Mb=(b-1)*C;c=(b-1)*S1//P
         Mtree=J+P*G03+P*P*G
         need(Mb//P**3==c and 0<=c<=b-2 and J+c<P,'localized carry')
         need((Mtree+c)//P**2==G,'unaffected top controller lane')
         top=((P**3*C)&(Mb+P**3*Mtree))//P**5%P
         need(top==(S1&G),'exact bit extraction')
         if top==S1:need(c==0 and G-S1+1>0,'positive restored selector')
         dyadic+=1
    b,P,J,G,S0,S1=32,63,2,1,1,8
    C=G+P*S0+P*P*S1;Mb=(b-1)*C
    need(C==31816 and Mb==986296 and Mb>2*P**3,'retained failed smaller estimate')
    return {'signed_prefix_contexts':signed,'negative_sign_contexts':minus,'height_one_contexts':height1,
      'contexts_violating_old_Mb_bound':overflow_examples,'dyadic_top_lane_contexts':dyadic,
      'retained_cut_counterexample':{'b':b,'P':P,'J':J,'G12':G,'S0':S0,'S1':S1,'Ctree':C,'Mb':Mb,'twice_P3':2*P**3},
      'scope':'Handwritten scalar/bit identities; no actual compiler or Pell zeros.'}
def build():
    dependencies=[]
    for name,pin in PINS.items():
        data=data_path(name).read_bytes();need(digest(data)==pin,'dependency '+name)
        dependencies.append({'path':str((WIP/name).relative_to(ROOT)),'sha256':pin,'bytes':len(data)})
    parent=json.loads(data_path('neary_woods_positive_first_production247_tesla.json').read_text())
    forms=[construct(p) for p in parent['forms']];need(len(forms)==2,'both program interfaces')
    return {'status':'PASS','helper_sha256':digest(Path(__file__).read_bytes()),'dependencies':dependencies,
      'dependency_locator_policy':'Pinned repository path, with same-name frozen author /tmp fallback before installation.',
      'forms':forms,'handwritten_cuts':cut_checks(),'independent_scalar_checks':scalar_and_lane_checks(),
      'source_arrays_evaluated':False,'source_degree_propagation':False,'predecessor_or_frozen_code_executed_or_imported':False}
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');options=parser.parse_args()
    out=json.dumps(build(),sort_keys=True,indent=2)+'\n';path=Path(__file__).with_suffix('.json')
    if options.write:path.write_text(out)
    else:need(path.read_text()==out,'exact saved receipt')
    print('PASS: complete245 static arrays /490 rows; handwritten cut and carry checks; no arrays evaluated')
if __name__=='__main__':main()

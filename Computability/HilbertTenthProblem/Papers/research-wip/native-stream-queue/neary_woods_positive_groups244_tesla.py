#!/usr/bin/env python3
"""Fresh244 static source edit with independent handwritten cut/carry evidence.
No predecessor/frozen program imports, saved-array execution or degree propagation.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS={
 'neary_woods_positive_group245_tesla.md':'fad086d06813e2dc97eb0b18b68d064fdbc67d35f6352efbdee27c43a32d851c',
 'neary_woods_positive_group245_tesla.json':'d9ddce2c7581243ff18a2e36c694bb5dd321e12286388c995ee4bc6ddadf4d38',
 'neary_woods_positive_first_production247_tesla.md':'9cb9da3c211fecbe3129421b23a16c747d8d1bf7b6365cf6320c426733ffd56a',
 'neary_woods_hierarchical_history250_tesla.md':'1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330',
}
def require(value,reason):
    if not value:raise RuntimeError(reason)
def sha(data):return hashlib.sha256(data).hexdigest()
def rows_sha(rows):return sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def locate(name):
    p=WIP/name
    return p if p.exists() else Path('/tmp')/name

def inputs(row):return [x for x in row[2:] if isinstance(x,str)]
def consumers(rows,name):return sorted(r[0] for r in rows if name in inputs(r))
def static_audit(rows,ports,out,recipes):
    known=set(ports);pending=list(rows);ordered=[]
    while pending:
        for i,row in enumerate(pending):
            if set(inputs(row))<=known:
                require(row[0] not in known,'duplicate producer')
                ordered.append(pending.pop(i));known.add(row[0]);break
        else:raise RuntimeError('non-topological graph')
    by={r[0]:r for r in ordered};used=set();todo=[out];roles=set()
    while todo:
        name=todo.pop()
        if name in used:continue
        used.add(name)
        if name in by:todo.extend(inputs(by[name]))
    require(set(by)<=used and set(ports)<=used,'row/port liveness')
    for r in ordered:
        require(len(r)==4 and r[1] in ('+','-','*'),'gate shape')
        for x in r[2:]:
            if isinstance(x,str) or type(x) is int:continue
            require(type(x) is dict and set(x)=={'fixed_numeral'},'fixed role shape')
            roles.add(x['fixed_numeral'])
    require(roles==set(recipes),'all fixed numeral roles live')
    return ordered,{'total':len(ordered),'M':sum(r[1]=='*' for r in ordered),
      'A':sum(r[1]!='*' for r in ordered),'all_rows_and_ports_live':True,
      'fixed_numeral_roles':len(roles),'canonical_source_sha256':rows_sha(ordered)}
def transform(parent):
    source=parent['source'];by={r[0]:r for r in source}
    require((len(source),parent['ledger']['M'],parent['ledger']['A'])==(245,129,116),'parent245')
    guards={'hist__Shat3':['hist__linear_group__164'],
      'hist__linear_group__164':['hist__selector_sum__6'],
      'hist__selector_sum__6':['hist__J__7'],'group_global_slack':['hist__P__10']}
    for port,want in guards.items():require(consumers(source,port)==want,'private consumers '+port)
    expected=[
      ['hist__linear_group__164','+','hist__S0','hist__Shat3'],
      ['hist__selector_sum__6','+','hist__G12','hist__linear_group__164'],
      ['hist__J__7','-','hist__selector_sum__6',1],
      ['hist__P__10','+','group_global_slack','hist__global_sum__14'],
      ['group_global_slack','+','hist__global_bound','hist__Shat1'],
    ]
    for r in expected:require(by[r[0]]==r,'literal source binding')
    removed={'hist__linear_group__164','hist__selector_sum__6'}
    added=['groups_size_slack','+','group_global_slack','hist__S0']
    proposed=[added];edits=[]
    for row in source:
        if row[0] in removed:continue
        if row[0]=='hist__J__7':new=[row[0],'+','hist__G12','hist__G03']
        elif row[0]=='hist__P__10':new=[row[0],'+','groups_size_slack','hist__global_sum__14']
        else:new=row
        if new!=row:edits.append({'before':row,'after':new})
        proposed.append(new)
    aux=['hist__G03' if p=='hist__Shat3' else p for p in parent['auxiliaries']]
    rows,ledger=static_audit(proposed,parent['parameters']+aux,parent['output'],parent['fixed_numeral_recipes'])
    require((ledger['total'],ledger['M'],ledger['A'],len(aux),len(edits))==(244,129,115,43,2),'244 exact count')
    packet={k:parent[k] for k in ['parameters','domains','merged','fixed_numeral_recipes','fixed_u9_recipe','output','comparisons','multiplier_port','scaled_factor_semantics']}
    packet.update(source=rows,auxiliaries=aux,ledger=ledger,
      certificate={'total':243,'M':129,'A':114,'comparisons':1,'positive_witnesses':43},
      manual_degree_upper_bound=936,exact_degree_claimed=False,parent_source_sha256=rows_sha(source),
      delta={'deleted':[by[n] for n in sorted(removed)],'added':[added],'edited':edits,
        'literal_retained_row_records':241,'topological_reorder':True,'consumer_guards':guards,
        'fixed_numeral_recipes_changed':False},
      inverse_to_parent={'hist__Shat3':'hist__G03-hist__S0+1','hist__global_bound':'hist__global_bound+hist__S0'},
      scope='Complete positive-zero bijection on valid U9 slices; restore both controller conditions after nested carry localization.')
    return packet

# Independent polynomial cuts: no source record is an input to this code.
NV=10
def num(n):return {(0,)*NV:n} if n else {}
def v(i):
    p=[0]*NV;p[i]=1;return {tuple(p):1}
def add(*terms):
    out={}
    for t in terms:
        for e,c in t.items():out[e]=out.get(e,0)+c
    return {e:c for e,c in out.items() if c}
def neg(p):return {e:-c for e,c in p.items()}
def mul(p,q):
    out={}
    for e,a in p.items():
        for f,b in q.items():
            k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+a*b
    return {e:c for e,c in out.items() if c}
def cut_checks():
    G,H,S0,Sh1,g,rest,P,L,a,pstar=[v(i) for i in range(NV)]
    oldhat=add(H,neg(S0),num(1));oldgroup=add(S0,oldhat)
    oldJ=add(G,oldgroup,num(-1));newJ=add(G,H)
    oldslack=add(g,S0,Sh1);newslack=add(add(g,Sh1),S0)
    oldP=add(rest,oldslack);newP=add(rest,newslack)
    oldupper=add(L,oldJ,mul(a,G));newupper=add(L,newJ,mul(a,G))
    oldmask=add(oldJ,mul(P,add(oldJ,mul(pstar,G))))
    newmask=add(newJ,mul(P,add(newJ,mul(pstar,G))))
    identities=[(oldgroup,add(H,num(1))),(oldJ,newJ),(oldslack,newslack),(oldP,newP),(oldupper,newupper),(oldmask,newmask)]
    for i,(left,right) in enumerate(identities):require(left==right,'independent cut '+str(i))
    return {'exact_identities':6,'independent_variables':NV,
      'scope':'Group,selector,size-sum,upper-transport and controller-mask cuts only.'}
def diagnostics():
    signed=minus=height1=dyadic=nested=0
    for ch in [32,64]:
     for D in [1,2]:
      b=ch*D
      for J in range(2,6):
       for eps in [-1,1]:
        P=(b-1)*J+eps
        for G12 in range(1,J):
         G03=J-G12
         for S0 in sorted({1,J,P//2,P-10}):
          for S1 in sorted({0,J,P//3,P-10}):
           g=P-8-S0-S1
           if g<1:continue
           C=G12+P*S0+P*P*S1;Mt=J+P*(J+(b-1)*J*G12);Mb=(b-1)*C
           Hb=2+2*P+2*P*P;Zb=1+P;Hr=2+2*P;Mr=(1+P)*(D-1)*J;T=P**8
           H0=Hb+P**3*C+P**6*Hr;M0=Mb+P**3*Mt+P**6*Mr;Z=Zb+P**3*C+P**6*Hr
           require(C<P**3 and Mt<=P**3-P*P-P-2,'raw selector packing')
           require(Mb<(P+1)*P**3 and Mb+P**3*Mt<P**6,'possible physical carry bound')
           require(0<=H0<T and 0<=M0<T and 0<=Z<T,'whole lower blocks')
           require(H0+2*T-Z>=T+1 and M0+T-Z>=1 and b*T-H0-M0-3*T+Z>=(b-5)*T+2,'truth field positivity')
           signed+=1;minus+=eps<0;height1+=D==1
    for b in [32,64]:
     for t in [2,3]:
      P=b**t;m=b-1;J=(P-1)//m
      for G12 in sorted({1,J//2,J-1}):
       G03=J-G12
       for S0 in sorted({1,G03,G03+1,J,J+1,P//3}):
        for S1 in sorted({0,1,G12,G12+1,J,J+1,P//3}):
         if P-8-S0-S1<1:continue
         C=G12+P*S0+P*P*S1;Mb=m*C;Mt=J+P*G03+P*P*G12
         c1=m*S0//P;c2=(m*S1+c1)//P
         require(0<=c1<=b-2 and 0<=c2<=b-2 and Mb//P**3==c2,'nested carries')
         require(J+c2<P and (Mt+c2)//P%P==G03 and (Mt+c2)//P**2==G12,'two intact controller digits')
         actual=(P**3*C)&(Mb+P**3*Mt)
         middle=actual//P**4%P;top=actual//P**5%P
         require(middle==(S0&G03) and top==(S1&G12),'two exact AND extractions')
         if middle==S0 and top==S1:
             require(c1==c2==0 and G03-S0+1>=1,'restored old positive domain')
         dyadic+=1;nested+=c2!=m*S1//P
    b=32;P=1024;J=33;G12=1;G03=32;S0=34;S1=33;g=949
    require(P==2+2+1+1+1+g+(S1+1)+S0==(b-1)*J+1,'retained prefix sums')
    c1=(b-1)*S0//P;c2=((b-1)*S1+c1)//P
    require(c1==c2==1 and (b-1)*S1//P==0,'retained omitted-middle-carry error')
    return {'signed_prefix_contexts':signed,'negative_sign_contexts':minus,'height_one_contexts':height1,
      'dyadic_two_lane_contexts':dyadic,'cases_with_genuinely_nested_carry':nested,
      'retained_counterexample':{'b':b,'P':P,'J':J,'G12':G12,'G03':G03,'S0':S0,'S1':S1,'g':g,'c1':c1,'c2':c2,'omitted_c1_value':0},
      'scope':'New scalar and bit formulas only; no actual U9 or native Pell zero is materialized.'}
def build():
    dependencies=[]
    for name,pin in PINS.items():
        data=locate(name).read_bytes();require(sha(data)==pin,'dependency '+name)
        dependencies.append({'path':str((WIP/name).relative_to(ROOT)),'sha256':pin,'bytes':len(data)})
    parent=json.loads(locate('neary_woods_positive_group245_tesla.json').read_text())
    forms=[transform(p) for p in parent['forms']];require(len(forms)==2,'two complete interfaces')
    return {'status':'PASS','helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':dependencies,
      'dependency_locator_policy':'Pinned repository files, or identical same-name frozen /tmp author bytes before installation.',
      'forms':forms,'handwritten_polynomial_cuts':cut_checks(),'independent_diagnostics':diagnostics(),
      'source_arrays_evaluated':False,'source_degree_propagation':False,'predecessor_or_frozen_code_executed_or_imported':False}
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');arg=parser.parse_args()
    value=json.dumps(build(),sort_keys=True,indent=2)+'\n';path=Path(__file__).with_suffix('.json')
    if arg.write:path.write_text(value)
    else:require(path.read_text()==value,'exact receipt')
    print('PASS: two complete244 static arrays /488 rows, handwritten nested-carry checks; no arrays evaluated')
if __name__=='__main__':main()

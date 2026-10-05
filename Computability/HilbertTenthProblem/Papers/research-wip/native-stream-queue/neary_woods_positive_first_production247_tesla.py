#!/usr/bin/env python3
"""New static247 constructor and handwritten cut/word diagnostics only.
Saved arrays are inert: no interpreter, scientific replay or degree propagation.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS={
 'neary_woods_positive_upper248_tesla.md':'f3329cf28090e39a219ac4e3d8882b99fc5bab72ae0507647a193cbdb514d557',
 'neary_woods_positive_upper248_tesla.json':'bab6ba8d61e9fac494ca42124b043c358597d19bf1ebf8f8699b2c054ff476bc',
 'neary_woods_hierarchical_history250_tesla.md':'1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330',
 'binary_tag_four_tile_history.md':'2cb8d1736852d525d4668f40eacdc8fa090c426f100110421521c85910e1e4b2',
 'neary_woods_u9_tag_metadata.md':'c98383dc28e3757691727ec57a208ececd32d117e97155c3d33d8de5c675b01a',
 'neary_woods_universal_u9_tag_chain.md':'7159fbae99ca020c2f9a10eb8560c13f56e53b6f81cd2f17f045097480f8ff03',
 'binary_tag_fixed_halt_bridge.md':'1519d918fc8e8e71f341df56d4f724c5a23b4ee10af5fff8e258228f5971f3a8',
}
def check(condition,message):
    if not condition: raise RuntimeError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def signature(rows):return sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def row_inputs(row):return [v for v in row[2:] if isinstance(v,str)]
def consumers(rows,port):return sorted(r[0] for r in rows if port in row_inputs(r))
def audit(rows,free,out,recipes):
    seen=set(free); definitions={}; roles=set()
    for r in rows:
        check(len(r)==4 and r[1] in ('+','-','*'),'row format')
        check(r[0] not in seen,'distinct output')
        for op in r[2:]:
            if isinstance(op,str):check(op in seen,'topological operand')
            elif type(op) is int:pass
            else:
                check(isinstance(op,dict) and set(op)=={'fixed_numeral'},'literal numeral shape')
                roles.add(op['fixed_numeral'])
        seen.add(r[0]); definitions[r[0]]=r
    live=set(); stack=[out]
    while stack:
        port=stack.pop()
        if port in live:continue
        live.add(port)
        if port in definitions:stack.extend(row_inputs(definitions[port]))
    check(set(definitions)<=live and set(free)<=live,'all rows and inputs live')
    check(roles==set(recipes),'all fixed roles live')
    return {'total':len(rows),'M':sum(r[1]=='*' for r in rows),
      'A':sum(r[1]!='*' for r in rows),'all_rows_and_ports_live':True,
      'fixed_numeral_roles':len(roles),'canonical_source_sha256':signature(rows)}
def child(parent):
    old=parent['source']; by={r[0]:r for r in old}
    check((len(old),parent['ledger']['M'],parent['ledger']['A'])==(248,129,119),'parent ledger')
    guards={
      'hist__Shat0':['hist__linear1_coefficient__29','hist__linear_group__164','hist__pack_sum__61'],
      'hist__ZVhat0':['hist__global_sum__13','hist__linear1_coefficient__27','hist__pack_sum__71'],
      'hist__repunit_tail__64':['hist__unhat_pack__65','hist__unhat_pack__74'],
      'hist__global_bound':['hist__P__10'],
    }
    for p,wanted in guards.items():check(consumers(old,p)==sorted(wanted),'consumer '+p)
    check(by['hist__repunit_tail__64']==['hist__repunit_tail__64','+','hist__P2__51','hist__P__10'],'old tail')
    check(by['hist__J__7']==['hist__J__7','-','hist__selector_sum__6',4],'old J')
    recipes=dict(parent['fixed_numeral_recipes'])
    check(recipes['upper_constant']=='2^(beta+2)+4','upper constant')
    check(recipes['lower_constant']=='2^L+production_offset+10','lower constant')
    check(recipes['lower_difference']=='2^L-2','lower difference')
    for role,sole in [('upper_constant','hist__linear_constant__168'),('lower_constant','hist__linear_constant__173')]:
        check([r[0] for r in old if {'fixed_numeral':role} in r[2:]]==[sole],'constant consumers')
    rename={'hist__Shat0':'hist__S0','hist__ZVhat0':'hist__ZV0','hist__repunit_tail__64':'hist__P2__51'}
    new=[];edits=[]
    for r in old:
        if r[0]=='hist__repunit_tail__64':continue
        v=[rename.get(x,x) if isinstance(x,str) else x for x in r]
        if r[0]=='hist__J__7':v=[r[0],'-','hist__selector_sum__6',3]
        if v!=r:edits.append({'before':r,'after':v})
        new.append(v)
    aux=[rename.get(p,p) for p in parent['auxiliaries']]
    recipes['upper_constant']='2^(beta+2)+3';recipes['lower_constant']='12'
    ledger=audit(new,parent['parameters']+aux,parent['output'],recipes)
    check((ledger['total'],ledger['M'],ledger['A'],len(aux),len(edits))==(247,129,118,43,9),'complete247 ledger')
    result={k:parent[k] for k in ['parameters','domains','merged','fixed_u9_recipe','output','comparisons','multiplier_port','scaled_factor_semantics']}
    result.update(source=new,auxiliaries=aux,fixed_numeral_recipes=recipes,ledger=ledger,
      certificate={'total':246,'M':129,'A':117,'comparisons':1,'positive_witnesses':43},
      manual_degree_upper_bound=936,exact_degree_claimed=False,parent_source_sha256=signature(old),
      delta={'deleted':[by['hist__repunit_tail__64']],'edited':edits,
        'literal_retained_row_records':238,'new_rows':0,'topological_reorder':False,
        'changed_numeral_roles':['upper_constant','lower_constant'],'consumer_guards':guards},
      inverse_to_parent={'hist__Shat0':'hist__S0+1','hist__ZVhat0':'hist__ZV0+1',
        'hist__global_bound':'hist__global_bound-1','upper_constant':'new upper_constant+1',
        'lower_constant':'new lower_constant+lower_difference+production_offset'},
      scope='Complete positive-zero bijection on valid U9 slices, using the forced first P_c tile; no generic tag-language restriction.')
    return result

# The following independent polynomials use handwritten cut formulas only.
# No source row, producer name, or source evaluator enters this calculation.
NV=15
def c(n):return {(0,)*NV:n} if n else {}
def var(j):
    e=[0]*NV;e[j]=1;return {tuple(e):1}
def add(*args):
    out={}
    for a in args:
        for e,v in a.items():out[e]=out.get(e,0)+v
    return {e:v for e,v in out.items() if v}
def neg(a):return {e:-v for e,v in a.items()}
def mul(a,b):
    out={}
    for e,x in a.items():
        for f,y in b.items():
            ef=tuple(j+k for j,k in zip(e,f));out[ef]=out.get(ef,0)+x*y
    return {e:v for e,v in out.items() if v}
def cuts():
    P,HU,HV,ZU,V0,V1,G,S0,S1,S2,S3,A,D,Cup,Clow=[var(i) for i in range(NV)]
    p2=mul(P,P);oldS0=add(S0,c(1));oldV0=add(V0,c(1));tail=add(p2,P)
    identities=[
      (add(oldS0,S1,S2,S3,c(-4)),add(S0,S1,S2,S3,c(-3))),
      (add(HU,HV,ZU,oldV0,V1,G,c(-1)),add(HU,HV,ZU,V0,V1,G)),
      (add(S1,S2,c(-2),mul(P,add(oldS0,mul(P,S1))),neg(tail)),
       add(S1,S2,c(-2),mul(P,add(S0,mul(P,S1))),neg(p2))),
      (add(ZU,mul(P,add(oldV0,mul(P,V1))),neg(tail)),
       add(ZU,mul(P,add(V0,mul(P,V1))),neg(p2))),
      (add(oldS0,neg(add(Cup,c(1)))),add(S0,neg(Cup))),
      (add(mul(A,oldV0),mul(D,oldS0),neg(add(Clow,A,D))),
       add(mul(A,V0),mul(D,S0),neg(Clow))),
    ]
    for i,(left,right) in enumerate(identities):check(left==right,'handwritten cut '+str(i))
    return {'exact_polynomial_cuts':len(identities),'independent_variables':NV,
      'scope':'Selector sum, global sum, controller pack, selected pack, upper and lower transports only.'}
def diagnostics():
    contexts=negative=height1=typed=0
    for ch in [32,64]:
      for D in [1,2,3]:
       b=ch*D
       for J in range(1,7):
        for eps in [-1,1]:
         P=(b-1)*J+eps
         for s0 in range(1,J+1):
          for s1 in range(J-s0+1):
           s2=0;s3=J-s0-s1
           HU,HV,ZU,V0,V1=2,3,1,1,0
           g=P-HU-HV-ZU-V0-V1-1
           check(g>0 and V0+1<P,'positive prefix')
           C=s1+s2+P*s0+P**2*s1
           M=J+P*(J+(b-1)*J*(s1+s2))
           H=HU+P*HV+P**2*HV;Z=ZU+P*V0+P**2*V1
           Hr=HU+P*HV;Mr=(1+P)*(D-1)*J
           T=P**8;H0=H+P**3*C+P**6*Hr;M0=(b-1)*C+P**3*M+P**6*Mr;Z0=Z+P**3*C+P**6*Hr
           check(0<=H0<T and 0<=M0<T and 0<=Z0<T,'untyped field bounds')
           check(H0+2*T-Z0>=T+1 and M0+T-Z0>=1 and b*T-H0-M0-3*T+Z0>=(b-5)*T+2,'truth margins')
           contexts+=1;negative+=eps<0;height1+=D==1
    for D in [2,3,4]:
     b=32*D
     for n in range(2,5):
      for suffix in itertools.product(range(4),repeat=n-1):
       word=(0,)+suffix
       if not any(k in (1,2) for k in word):continue
       P=b**n;J=sum(b**j for j in range(n))
       U=[1+j%(D-1) for j in range(n)];V=[1+(j+1)%(D-1) for j in range(n)]
       HU=sum(u*b**j for j,u in enumerate(U));HV=sum(v*b**j for j,v in enumerate(V))
       ZU=sum(U[j]*b**j for j,k in enumerate(word) if k in (1,2))
       V0=sum(V[j]*b**j for j,k in enumerate(word) if k==0)
       V1=sum(V[j]*b**j for j,k in enumerate(word) if k==1)
       g=P-HU-HV-ZU-V0-V1-1
       check(V0>0 and ZU>0 and g>=((32-4)*D+3)*J>=31,'typed slack inverse')
       typed+=1
    # Retained non-U9 counterexample, using independently written word images.
    upper='1001'+'1001'+'100';lower='1001100'+'110'+'0'
    check(upper==lower=='10011001100','general tag boundary')
    return {'signed_prefix_contexts':contexts,'negative_repunit_contexts':negative,
      'height_one_contexts':height1,'typed_word_occupancies':typed,
      'retained_non_u9_no_Pc_match':{'beta':2,'u':'cb','w':'bb','tiles':['P_b','D_b'],'common_binary_word':upper},
      'scope':'Fresh scalar prefixes and typed finite occupancies, not genuine U9 runs or native Pell zeros.'}
def packet():
    deps=[]
    for name,pin in PINS.items():
        data=(WIP/name).read_bytes();check(sha(data)==pin,'pin '+name)
        deps.append({'path':str((WIP/name).relative_to(ROOT)),'sha256':pin,'bytes':len(data)})
    parent=json.loads((WIP/'neary_woods_positive_upper248_tesla.json').read_text())
    forms=[child(p) for p in parent['forms']];check(len(forms)==2,'two full interfaces')
    return {'status':'PASS','helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,
      'forms':forms,'handwritten_cut_checks':cuts(),'independent_diagnostics':diagnostics(),
      'source_arrays_evaluated':False,'source_degree_propagation':False,
      'predecessor_or_frozen_code_executed_or_imported':False}
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    output=json.dumps(packet(),sort_keys=True,indent=2)+'\n';path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(output)
    else:check(path.read_text()==output,'exact receipt')
    print('PASS: two complete static247 arrays /494 rows; six handwritten cuts; no arrays evaluated')
if __name__=='__main__':main()

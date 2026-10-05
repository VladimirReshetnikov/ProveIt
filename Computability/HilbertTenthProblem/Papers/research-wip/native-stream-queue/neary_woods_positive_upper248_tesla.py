#!/usr/bin/env python3
"""Fresh static248 construction and independently handwritten cut diagnostics.
No saved row array is evaluated, imported, or used for degree propagation.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS={
 'neary_woods_scaled_strong249_tesla.md':'2230f44faee7e2ecebb0ce29722462f121a49e85addf3740d8b8b54efd7bc8a4',
 'neary_woods_scaled_strong249_tesla.json':'e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c',
 'neary_woods_scaled_strong249_degree_correction_tesla.md':'ada1718ff4e93eb4b48e50d1362b8912973c6d629e1f724878a4e12804a39f11',
 'neary_woods_scaled_strong249_degree_correction_tesla.json':'573effd459ea14b1ca82b98cc3a61a5ba37e41ada68965200cf382f35ebe1366',
 'neary_woods_hierarchical_history250_tesla.md':'1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330',
 'neary_woods_universal_initial_bound254.md':'9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90',
 'binary_tag_four_tile_history.md':'2cb8d1736852d525d4668f40eacdc8fa090c426f100110421521c85910e1e4b2',
 'neary_woods_universal_u9_tag_chain.md':'7159fbae99ca020c2f9a10eb8560c13f56e53b6f81cd2f17f045097480f8ff03',
}
def require(t,message):
    if not t:raise RuntimeError(message)
def digest(b):return hashlib.sha256(b).hexdigest()
def rowhash(rows):return digest(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def operands(r):return [v for v in r[2:] if isinstance(v,str)]
def topology(rows,free,output,roles):
    known=set(free);by={};actual_roles=set()
    for r in rows:
        require(len(r)==4 and r[1] in ['+','-','*'] and r[0] not in known,'row format')
        for v in r[2:]:
            if isinstance(v,str):require(v in known,'predecessor')
            elif type(v) is int:pass
            else:
                require(isinstance(v,dict) and set(v)=={'fixed_numeral'},'numeral')
                actual_roles.add(v['fixed_numeral'])
        known.add(r[0]);by[r[0]]=r
    live=set();queue=[output]
    while queue:
        x=queue.pop()
        if x in live:continue
        live.add(x)
        if x in by:queue.extend(operands(by[x]))
    require(set(by)<=live and set(free)<=live,'all-row/port liveness')
    require(actual_roles==set(roles),'all fixed roles')
    return {'total':len(rows),'M':sum(r[1]=='*' for r in rows),
            'A':sum(r[1]!='*' for r in rows),'all_rows_and_ports_live':True,
            'fixed_numeral_roles':len(actual_roles),'canonical_source_sha256':rowhash(rows)}
def sorted_rows(rows,free):
    pending=list(rows);answer=[];known=set(free)
    while pending:
        for j,r in enumerate(pending):
            if set(operands(r))<=known:
                answer.append(r);known.add(r[0]);pending.pop(j);break
        else:raise RuntimeError('cyclic edits')
    return answer

def construct(p):
    require(p['cores_scaled']==['geo__'],'geometry-only parent')
    rows=p['source'];by={r[0]:r for r in rows}
    guards={
     'hist__group_hat__59':['hist__pack_sum__63'],
     'hist__repunit_tail__64':['hist__unhat_pack__65','hist__unhat_pack__74'],
     'hist__ZUhat0':['hist__linear0_coefficient__17','hist__global_sum__12','hist__pack_sum__73'],
     'hist__global_bound':['hist__P__10'],
    }
    for name,wanted in guards.items():
        actual=[r[0] for r in rows if name in operands(r)]
        require(sorted(actual)==sorted(wanted),'private consumer '+name)
    expected=[
      ['hist__group_hat__59','-','hist__group_sum__58',1],
      ['tree_group12','-','hist__group_sum__58',2],
      ['hist__repunit_tail__64','+','hist__P2__51','hist__repunit_factor__50'],
      ['hist__pack_sum__63','+','hist__group_hat__59','hist__pack_product__62'],
    ]
    for r in expected:require(by[r[0]]==r,'pack literal')
    require(p['fixed_numeral_recipes']['upper_constant']=='2^(beta+3)+2','old upper constant')
    require(p['fixed_numeral_recipes']['upper_difference']=='2^(beta+2)-2','upper difference')
    numeral_consumers=[r[0] for r in rows if {'fixed_numeral':'upper_constant'} in r[2:]]
    require(numeral_consumers==['hist__linear_constant__168'],'constant private role')
    new=[];edits=[];deleted=by['hist__group_hat__59']
    for r in rows:
        if r[0]==deleted[0]:continue
        s=[('hist__ZU0' if v=='hist__ZUhat0' else v) for v in r]
        if r[0]=='hist__repunit_tail__64':s=[r[0],'+','hist__P2__51','hist__P__10']
        if r[0]=='hist__pack_sum__63':s=[r[0],'+','tree_group12','hist__pack_product__62']
        if s!=r:edits.append({'before':r,'after':s})
        new.append(s)
    aux=['hist__ZU0' if a=='hist__ZUhat0' else a for a in p['auxiliaries']]
    recipes=dict(p['fixed_numeral_recipes']);recipes['upper_constant']='2^(beta+2)+4'
    new=sorted_rows(new,p['parameters']+aux)
    ledger=topology(new,p['parameters']+aux,p['output'],recipes)
    require((ledger['total'],ledger['M'],ledger['A'])==(248,129,119),'248 count')
    require(len(aux)==43 and len(edits)==5,'arity/delta')
    return {'source':new,'output':p['output'],'parameters':p['parameters'],
      'auxiliaries':aux,'domains':p['domains'],'fixed_numeral_recipes':recipes,
      'fixed_u9_recipe':p['fixed_u9_recipe'],'merged':p['merged'],
      'ledger':ledger,'certificate':{'total':247,'M':129,'A':118,'comparisons':1,'positive_witnesses':43},
      'comparisons':p['comparisons'],'multiplier_port':'geo__A',
      'scaled_factor_semantics':p['active_factor_note'],
      'manual_degree_upper_bound':936,'exact_degree_claimed':False,
      'parent_source_sha256':rowhash(rows),
      'delta':{'removed':[deleted],'edited':edits,'literal_retained_row_records':243,
               'new_rows':0,'topological_reorder':True,'consumer_guards':guards,
               'fixed_numeral_role_changed':'upper_constant'},
      'inverse_to_parent':{'hist__ZUhat0':'hist__ZU0+1','hist__global_bound':'hist__global_bound-1',
           'upper_constant':'new upper_constant+upper_difference'},
      'scope':'Bijection of complete positive zeros on inherited valid U9 slices; inverse positivity proved only at zeros.'}

# Independent sparse cuts: no code below consumes or interprets any source row.
NV=14
def constant(n):return {(0,)*NV:n} if n else {}
def variable(j):
    t=[0]*NV;t[j]=1;return {tuple(t):1}
def plus(a,b,sign=1):
    c=dict(a)
    for t,v in b.items():c[t]=c.get(t,0)+sign*v
    return {t:v for t,v in c.items() if v}
def times(a,b):
    c={}
    for t,u in a.items():
        for s,v in b.items():
            k=tuple(x+y for x,y in zip(t,s));c[k]=c.get(k,0)+u*v
    return {t:v for t,v in c.items() if v}
def total(*args):
    a={}
    for b in args:a=plus(a,b)
    return a
def cut_checks():
    P,HU,HV,Z,V0,V1,G,S0,S1,S2,S3,D,C,O=[variable(j) for j in range(NV)]
    one=constant(1);two=constant(2);P2=times(P,P)
    old_global=total(HU,HV,plus(Z,one),V0,V1,plus(G,one,-1))
    new_global=total(HU,HV,Z,V0,V1,G)
    require(old_global==new_global,'global affine cut')
    old_tail=total(P2,P,one);new_tail=total(P2,P)
    common=times(P,plus(S0,times(P,S1)))
    old_tree=plus(total(plus(total(S1,S2),one,-1),common),old_tail,-1)
    new_tree=plus(total(plus(total(S1,S2),two,-1),common),new_tail,-1)
    require(old_tree==new_tree,'controller cut')
    zupper=times(P,plus(V0,times(P,V1)))
    require(plus(total(Z,one,zupper),old_tail,-1)==plus(total(Z,zupper),new_tail,-1),'selected cut')
    rest=total(times(two,HU),S0,S3,times(O,total(S1,S2)))
    old_linear=plus(total(rest,times(D,plus(Z,one))),plus(C,D),-1)
    new_linear=plus(total(rest,times(D,Z)),C,-1)
    require(old_linear==new_linear,'upper transport cut')
    return {'exact_sparse_polynomial_cuts':4,'variable_count':NV,
            'scope':'Handwritten global,controller,selected-word and upper-linear formulas only.'}

def scalar_checks():
    count=0;negative=0;height1=0
    for ch in [32,64]:
        for D in [1,2,3]:
            b=ch*D
            for J in range(1,8):
                for eps in [-1,1]:
                    P=(b-1)*J+eps
                    for s0 in range(J+1):
                        for s1 in range(J-s0+1):
                            s2=0;s3=J-s0-s1
                            HU=1;HV=2;Z=1;V0hat=2;V1hat=3
                            G=P-HU-HV-Z-V0hat-V1hat
                            require(G>0 and Z+1<P,'raw positive domain')
                            ct=s1+s2+P*s0+P*P*s1
                            mt=J+P*(J+(b-1)*J*(s1+s2))
                            hb=HU+P*HV+P*P*HV;zb=Z+P*(V0hat-1)+P*P*(V1hat-1)
                            hr=HU+P*HV;rr=(D-1)*J;mr=(1+P)*rr;T=P**8
                            H0=hb+P**3*ct+P**6*hr
                            M0=(b-1)*ct+P**3*mt+P**6*mr
                            Z0=zb+P**3*ct+P**6*hr
                            require(0<=H0<T and 0<=M0<T and 0<=Z0<T,'untyped lower bounds')
                            H=H0+2*T;M=M0+T
                            require(H-Z0>=T+1 and M-Z0>=1 and b*T-H-M+Z0>=(b-5)*T+2,'truth field margins')
                            count+=1;negative+=eps<0;height1+=D==1
    word_cases=0
    for beta in [2,3,4]:
        for length in range(2,7):
            for mask in range(1<<(length-1)):
                w=''.join('b' if mask&(1<<j) else 'c' for j in range(length-1))+'b'
                if w.count('b')<2:continue
                enc=''.join('1'+'0'*beta+'1' if a=='b' else '1' for a in w)[:-1]
                starts=sum(c=='0' and (j==0 or enc[j-1]!='0') for j,c in enumerate(enc))
                require(starts==w.count('b')>=2,'word zero-run obstruction')
                word_cases+=1
    return {'signed_prefix_contexts':count,'negative_repunit_contexts':negative,
            'height_one_contexts':height1,'small_word_zero_run_cases':word_cases,
            'scope':'Fresh illustrative scalar/word formulas; no full compiler or native zeros.'}

def build():
    deps=[]
    for n,h in PINS.items():
        data=(WIP/n).read_bytes();require(digest(data)==h,'pin '+n)
        deps.append({'path':str((WIP/n).relative_to(ROOT)),'sha256':h,'bytes':len(data)})
    p=json.loads((WIP/'neary_woods_scaled_strong249_tesla.json').read_text())
    parents=[f for f in p['forms'] if f['cores_scaled']==['geo__']]
    require(len(parents)==2,'two current interfaces')
    forms=[construct(f) for f in parents]
    return {'status':'PASS','helper_sha256':digest(Path(__file__).read_bytes()),'dependencies':deps,
      'forms':forms,'polynomial_cut_checks':cut_checks(),'independent_scalar_checks':scalar_checks(),
      'numbered_boundary':{'remark':1,'new_global_bound':1,'mapped_old_global_bound':0,
          'scope':'Off-zero supplied-domain boundary only, not a child zero.'},
      'source_arrays_evaluated':0,'source_degree_propagation':False,
      'predecessor_or_frozen_code_executed_or_imported':False}
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    path=Path(__file__).with_suffix('.json');text=json.dumps(build(),sort_keys=True,indent=2)+'\n'
    if args.write:path.write_text(text)
    else:require(path.read_text()==text,'receipt mismatch')
    print('PASS: two static248 sources /496 rows, four handwritten cuts and scoped scalar checks; no arrays evaluated')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact source/constructor/sign audit for a bootstrap-guard exchange.

No Lean, source emitter, author checker or optimizer is imported. Finite Pell
controls are diagnostics; the unbounded argument is in README.md.
"""
import argparse
from collections import Counter
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('independent_poly',ROOT/'reviews/main-root-modulus-signs-peer.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
P,C,V,add,mul,product=p.P,p.C,p.V,p.plus,p.times,p.product
def need(ok,message):
    if not ok:raise ValueError(message)
def load(path):return json.loads(path.read_bytes())
def sha(path):return sha256(path.read_bytes()).hexdigest()
def pell(a,k):
    x,y=1,0
    for _ in range(k):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    prior=ROOT/'research/main-root-and-modulus-signs'
    for relative,h in load(prior/'SOURCE_PINS.json')['files'].items():need(sha(ROOT/relative)==h,'whole frozen source '+relative)
    rawpath=ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json'
    raw=load(rawpath);rows=[P(r['terms'])for r in raw['rows']]
    cert=load(prior/'CERTIFICATE.json')
    oldpath=ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json'
    old=load(oldpath);oldguards={g['raw_variable']for g in old['guards']}
    newguards=(oldguards-{694})|{645}
    need(len(oldguards)==len(newguards)==78 and 694 in oldguards and 645 not in oldguards,'exact guard exchange, not a deletion')
    need(raw['variables'][645]==dict(kind='witness',name='shared.Zminus1'),'actual new guard identity')
    prefix=cert['prefix_proof'];known={v:0 for v in prefix['initial_semantic_guard_indices']}
    need(len(known)==61 and set(known)<=newguards and all(v<643 for v in known),'all61 semantic guards retained without T0')
    combinations=0
    def combine(obj,expected=None,prefix_only=False):
        nonlocal combinations
        result={}
        for term in obj['row_combination']:
            m=P(term['multiplier']);row=rows[term['row']]
            if prefix_only:need(p.vars_(m)|p.vars_(row)<=set(range(643)),'prefix proof independent of all private signs')
            result=add(result,mul(m,row))
        if expected is None:expected=P(obj.get('polynomial',obj.get('expanded_polynomial')))
        need(result==expected,'every coefficient of full original-row ideal');combinations+=1
        return result
    def positive_after_shift(q):
        need(p.vars_(q)<=set(known),'no missing sign/lower-bound dependency')
        shifted={}
        for m,c in q.items():shifted=add(shifted,product([C(c)]+[add(V(v),C(known[v]))for v in m]))
        need(all(c>=0 for c in shifted.values())and shifted.get((),0)>0,'strict positivity from only earlier lower bounds')
    def bound(obj):
        v,L,F,G=obj['variable'],obj['lower'],P(obj['factor']),P(obj['rhs'])
        need(v not in p.vars_(F)|p.vars_(G),'no target used to prove its own sign')
        combine(obj,add(mul(V(v),F),G,-1),True)
        positive_after_shift(F);positive_after_shift(add(G,mul(C(L-1),F),-1));known[v]=max(known.get(v,L),L)
    signs=0
    def sign(step):
        nonlocal signs
        v,c,R=step['variable'],step['coefficient'],P(step['rhs']);want=add(mul(C(c),V(v)),R,-1)
        need(c>0 and v<643 and p.vars_(rows[step['row']])<=set(range(643)),'literal prefix sign pivot')
        need(rows[step['row']]in[want,mul(C(-1),want)],'whole prefix sign row')
        if step['kind']=='positive_monomials':
            deps={i for m in R for i,n in Counter(m).items()if n%2}
            need(all(c>0 for c in R.values())and deps==set(step['dependencies'])and deps<=set(known),'all odd-power signs precede inference')
        else:need(step['kind']=='affine_square'and mul(P(step['square_root']),P(step['square_root']))==R,'whole square sign identity')
        known[v]=max(known.get(v,0),0);signs+=1
    for obj in prefix['preliminary_t_n_bounds']:bound(obj)
    for obj in prefix['five_stages']:
        for step in obj['preceding_sign_steps']:sign(step)
        bound(obj)
    for step in prefix['final_sign_steps']:sign(step)
    need(set(known)==set(range(643))and known[4]>=1 and known[5]>=2,'all643 signs without base0.T')
    pp=cert['positive_prefix'];combine(pp['canonical_modulus_cut'],prefix_only=True)
    positive_after_shift(add(P(pp['canonical_modulus_cut']['polynomial']),V(129)))
    positive={4,5,129}
    for step in pp['steps']:
        v=step['variable'];row=rows[step['row']]
        need(row.get((v,))==1 and all(v not in m or m==(v,)for m in row),'positive constructor unit pivot')
        rhs={m:-c for m,c in row.items()if m!=(v,)};monomial=tuple(step['positive_monomial'])
        need(all(c>0 for c in rhs.values())and p.vars_(rhs)<=set(known)and rhs.get(monomial,0)>0 and set(monomial)<=positive,'constructor positivity without private signs')
        positive.add(v)
    need(positive==set(pp['known_after'])and {s['exponent'][1]for s in raw['seeds']}<=positive,'all15 exact seed exponents positive')
    # The literal raw86 formula; no assumption that a square is even.
    gate_by_var={r['gate']:i for i,r in enumerate(raw['rows'])if r.get('gate')is not None}
    sum63={}
    for i in (47,48,49,50):sum63=add(sum63,rows[i])
    need(sum63==P([[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]]),'raw63=t+x+y+M0+2')
    for v in range(64,87):need(rows[gate_by_var[v]]==add(V(v),mul(V(v-1),V(v-1)),-1),'exact23 squarings fromraw63 to86')
    need(rows[gate_by_var[531]]==add(add(V(531),V(530),-1),C(-1))and 530 in positive,'selected base531 at least2')
    # Critical shared-call and parity constructors.
    wanted=[(0,5,4,6),(1,92,86,93),(2,103,4,104),(9,531,122,560)]
    for i,n,k,m in wanted:
        call=raw['powers'][i];bound_call=cert['power_calls'][i]
        need([call[x]for x in('base','exponent','output')]==[['v',v]for v in(n,k,m)],'actual critical power call')
        need((bound_call['base'],bound_call['exponent'],bound_call['output'])==(n,k,m),'whole certified actual call binding')
        combine(bound_call['cut'])
    need(cert['power_calls'][0]['X']==cert['power_calls'][2]['X']==670 and cert['power_calls'][0]['Y']==cert['power_calls'][2]['Y']==671,'call2 shares the originalt seed pair')
    need(add(rows[86],rows[87])==P([[1,[103]],[-1,[]],[-1,[5,87]]]),'raw103=1+(t+1)f0')
    need(add(rows[88],rows[101])==P([[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]]),'raw122=t+raw104+2')
    need(add(add(rows[77],rows[75]),mul(V(87),rows[74]))==P([[1,[92]],[-1,[]],[-1,[87,86,86]]]),'raw92=1+f0*raw86 squared')
    factorial=prefix['five_stages'][0];combine(factorial,add(mul(V(87),P(factorial['factor'])),P(factorial['rhs']),-1),True)
    need(P(factorial['rhs'])==add(V(93),V(95))and P(factorial['factor'])==add(add(C(1),V(94)),V(95)),'early f0 positive consequence uses actualoutput93 and retainedslacks')
    for obj in [cert['frame_cut'],cert['bootstrap_norm'],cert['unit_norm_cut'],cert['positive_V_product'],cert['comparison_base_constructor'],cert['comparison_base_congruence']]:combine(obj)
    for seed in cert['seeds']:
        need(seed['aliases']['YminusK']in newguards,'all15 YminusK hypotheses retained')
        for cut in seed['cuts'].values():combine(cut)
    for modulus in cert['moduli']:combine(modulus['cut'])
    # Full use boundary for the converse Z-sign normalization.
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
    gate_rows=set(interfaces['all_gate_rows']);changed={645};changed_gates=[]
    for v,ri in zip([i for i,x in enumerate(raw['variables'])if x['kind']in('gate','square_difference')],interfaces['all_gate_rows']):
        row=rows[ri];need(row.get((v,))in(-1,1)and max(p.vars_(row))==v and all(v not in m or m==(v,)for m in row),'all topological unit gate definitions')
        deps=p.vars_(row)-{v}
        if deps&changed:changed.add(v);changed_gates.append(dict(variable=v,row=ri,dependencies=sorted(deps)))
    affected=[i for i,row in enumerate(rows)if i not in gate_rows and p.vars_(row)&changed]
    need(len(changed_gates)==6 and affected==[603]and not changed&oldguards,'Z normalization preserves every oldguard value')
    nongates=[t for t in cert['bootstrap_norm']['row_combination']if t['row']not in gate_rows]
    need(nongates==[dict(multiplier=[[1,[]]],row=603)],'only affected constraint has unit bootstrap norm ideal')
    fixed_roles=set(range(643))|{643,644,655,656}|{v[1]for s in raw['indices']for v in s['pair']}|{v[1]for c in raw['powers']for v in(c['base'],c['exponent'],c['output'])}|{c['modulus']for c in cert['power_calls']}|{c['quotient']for c in cert['power_calls']}
    need(not changed&fixed_roles,'Z normalization fixes all claimed semantic/main/comparison/power roles')
    aa,nn,xx,yy=[V(v)for v in range(4)];dd=add(add(mul(C(2),mul(aa,nn)),mul(nn,nn)),C(1));delta=add(mul(aa,aa),C(-1))
    pellminus=add(xx,mul(add(aa,nn),yy),-1);pellplus=add(xx,mul(add(aa,nn),yy))
    norm=add(mul(xx,xx),mul(delta,mul(yy,yy)),-1)
    need(mul(pellminus,pellplus)==add(norm,mul(dd,mul(yy,yy)),-1),'complete negativeA Pell product identity')
    nx=add(mul(aa,xx),mul(delta,yy));ny=add(xx,mul(aa,yy))
    need(add(nx,mul(add(aa,nn),ny),-1)==add(mul(mul(C(-1),nn),pellminus),mul(dd,yy),-1),'complete negativeA residue recurrence identity')
    controls=0
    for W in range(2,9):
        a=W**W+1
        for n in range(1,W):
            D=2*a*n+n*n+1
            for k in range(1,W):
                chi,psi=pell(a,k)
                for m in range(W):
                    need(m+n**k<=W**W and m*n**k+1<=W**W,'both strict smallresidue bounds')
                    for signX in(-1,1):
                        residue=signX*chi+(a+n)*psi-m
                        if residue%D==0:
                            allowed=(signX==-1 and k%2==1 and m==n**k)or(signX==1 and k%2==0 and n==m==1)
                            need(allowed,'every viable negativeA source-call branch')
                        controls+=1
    parity=0
    for t in range(1,20,2):
        for f0 in range(1,20):
            n=1+(t+1)*f0
            need(n>=3 and n%2==1 and(t+pow(n,t,2)+2)%2==0,'literal oddcall2 to evencall9 parity contradiction');parity+=1
    signed_index=0
    for a in range(2,5):
        for k in range(1,4):
            x,y=pell(a,k);u,v=pell(a,2*k*y)
            need(v%(y*y)==0 and u>a+1 and u%2==1,'signedA comparison fixture commonunit')
            for signA in(-1,1):
                A=signA*a;q0=((A-1)*pow(4*v,-1,u))%u
                for q in(q0,q0-u):
                    B=1+4*v*q;s,r=pell(B,k)
                    for signX in(-1,1):
                        X=signX*x;S=signX*(signA**k)*s
                        need(abs(B)>=3 and(B-A)%u==0 and(S-X)%u==0 and(r-k)%(4*y)==0 and S*S-(B*B-1)*r*r==1,'both signedA and signedB index fixtures')
                        signed_index+=1
    bootstrap=0
    for W in range(2,8):
        for multiplier in(1,2):
            a,zW=pell(W+1,W*multiplier)
            need(zW%W==0 and a>W**W,'bootstrap classification/recurrence controls')
            z=zW//W
            for signZ in(-1,1):
                oldZ=signZ*z;newZ=abs(oldZ)
                need(newZ-1>=0 and a*a-1==W**3*(W+2)*newZ*newZ,'converseZsign normalization');bootstrap+=1
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),
        'source_pins':{str(f.relative_to(ROOT)):sha(f)for f in[rawpath,oldpath,prior/'CERTIFICATE.json',ROOT/'reviews/main-root-modulus-signs-peer.py',Path(__file__)]},
        'old_guard_indices':sorted(oldguards),'new_guard_indices':sorted(newguards),
        'replaced_guard':694,'replacement_guard':645,'guard_count':78,
        'prefix_signs_without_T0':len(known),'exact_sign_rows':signs,'positive_constructor_steps':len(pp['steps']),
        'whole_original_row_combinations':combinations,'raw86_exact_formula':'(t+x+y+M0+2)^(2^23)',
        'raw86_constructor_evenness_assumed':False,'raw86_lower_bound':3,
        'critical_calls':wanted,'negativeA_smallresidue_controls':controls,'parity_controls':parity,
        'universal_collected_negativeA_identities':2,'signedA_signedB_index_controls':signed_index,
        'bootstrap_and_Z_flip_controls':bootstrap,'Z_flip_changed_gates':changed_gates,'Z_flip_affected_constraints':affected,
        'scope':'Exact finite source/prefix/constructor/use binding for the ordinary guardexchange in README. No new quartic, metric, Lean/internalZFC theorem or claim thatconstructor86 is always even.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k]for k in('status','guard_count','prefix_signs_without_T0','whole_original_row_combinations','negativeA_smallresidue_controls','parity_controls')},indent=2))

if __name__=='__main__':main()

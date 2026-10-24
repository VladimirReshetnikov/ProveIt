#!/usr/bin/env python3
"""Independent signed-B lift peer: entire original-row closure and exact cuts.

Imports no author audit/checker/builder, optimizer or Pell emitter. The ordinary
unbounded signed-index proof is reviewed separately in the accompanying note.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'research/comparison-base-sign'
PRIOR=ROOT/'research/main-root-and-modulus-signs'


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_bytes())
def sha(p):return sha256(p.read_bytes()).hexdigest()
def P(terms):
    out={}
    for c,m in terms:
        need(type(c)is int and all(type(i)is int and i>=0 for i in m),'literal integer coefficients/indices')
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return{m:c for m,c in out.items()if c}


def add(p,q,scale=1):
    out=dict(p)
    for m,c in q.items():out[m]=out.get(m,0)+scale*c
    return{m:c for m,c in out.items()if c}


def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return{m:c for m,c in out.items()if c}


def V(i):return{(i,):1}
def C(c):return{():c}if c else{}
def plus(*ps):
    p={}
    for q in ps:p=add(p,q)
    return p


def product(*ps):
    p=C(1)
    for q in ps:p=mul(p,q)
    return p


def variables(p):return{i for m in p for i in m}
def square(p):return mul(p,p)


def sealed(folder):
    manifest=folder/'MANIFEST.json';files=load(manifest)['files']
    need({str(p.relative_to(folder))for p in folder.rglob('*')if p.is_file()and p!=manifest}==set(files),'complete closed packet '+str(folder))
    for n,h in files.items():need(sha(folder/n)==h,'whole sealed member '+str(folder/n))


def literal_audit(raw,interfaces,cert):
    need(len(raw['variables'])==1259 and len(raw['rows'])==1177,'all actual raw variables and rows')
    rows=[P(r['terms'])for r in raw['rows']]
    # Reconstruct the gate inventory directly from source row data, rather than
    # accepting the author's private/nonprivate row partitions as completeness.
    gate_by_variable={}
    for i,row in enumerate(raw['rows']):
        if row.get('gate')is not None:
            v=row['gate'];need(v not in gate_by_variable,'one actual defining row per gate')
            gate_by_variable[v]=i
    actual_gate_variables={i for i,v in enumerate(raw['variables'])if v['kind']in['gate','square_difference']}
    need(set(gate_by_variable)==actual_gate_variables and len(actual_gate_variables)==1029,'full independent1029-gate inventory')
    need([gate_by_variable[v]for v in sorted(gate_by_variable)]==interfaces['all_gate_rows'],'all prior gate interfaces authenticated by actual rows')
    constraints=sorted(set(range(1177))-set(gate_by_variable.values()))
    need(len(constraints)==148 and set(constraints)==set(interfaces['semantic_non_gate_rows'])|set(interfaces['private_non_gate_rows']),
         'complete148 nongates, with no constraint outside the independent audit')
    free={i for i in range(1259)if i not in gate_by_variable}
    changed_free={657,658}|{s[k][1]for s in interfaces['seeds']for k in['S','R','Squotient','Rquotient']}
    need(len(changed_free)==62 and changed_free<=free,'exact62 free integer comparison witnesses')
    closure=set(changed_free);affected_gates=[]
    for v in sorted(gate_by_variable):
        r=gate_by_variable[v];p=rows[r];coefficient=p.get((v,))
        need(coefficient in[-1,1]and all(v not in m or m==(v,)for m in p),'literal unit gate pivot')
        deps=variables(p)-{v};need(all(i<v for i in deps),'actual strictly earlier gate operands')
        if deps&closure:
            closure.add(v);affected_gates.append(dict(variable=v,row=r,dependencies=sorted(deps)))
    affected_constraints=[r for r in constraints if variables(rows[r])&closure]
    expected_constraints={616}|{s['rows'][k]for s in interfaces['seeds']for k in['norm3','S_mod_U','R_mod_4Y']}
    need(len(affected_gates)==141 and len(affected_constraints)==46 and set(affected_constraints)==expected_constraints,
         'entire1177-row use boundary has exactly141 gates and46 comparison constraints')
    protected=set(range(643))|{643,644,645,646,655,656,917,1214}
    protected|={v[1]for s in raw['indices']for v in s['pair']}
    protected|={p[k][1]for p in raw['powers']for k in['base','exponent','output']}
    protected|={p['quotient']for p in cert['power_calls']}
    remaining=set(cert['remaining_raw_guard_indices'])-{657}
    need(len(remaining)==78 and not(closure&(protected|remaining)),'all semantic ports, main pairs, power quotients and78 guards fixed')
    gate_rows=set(gate_by_variable.values());checked=[]
    def cut(obj,want,rid):
        got={};nongates=[]
        for x in obj['row_combination']:
            i=x['row'];need(type(i)is int and 0<=i<1177,'literal cut row index')
            q=P(x['multiplier']);got=add(got,mul(q,rows[i]))
            if i not in gate_rows:nongates.append((i,q))
        need(got==want==P(obj['polynomial']),'every collected coefficient of independently specified comparison target')
        need(nongates==[(rid,C(1))],'exact unit nongate pivot, with only gate rows in the remainder')
        checked.append(rid)
    A,B,U=map(V,[644,667,655])
    cut(cert['comparison_base_congruence'],plus(B,product(C(-1),A),product(C(-1),U,V(658))),616)
    need(len(cert['seeds'])==len(interfaces['seeds'])==15,'all15 comparison instances')
    for s,i in zip(cert['seeds'],interfaces['seeds']):
        a=s['aliases'];need(all(a[k]==i[k][1]for k in['X','Y','S','R','YminusK','Squotient','Rquotient'])and a['k']==i['exponent'][1],
             'all literal changed and fixed seed aliases')
        X,Y,S,R,k,sq,rq=[V(a[key])for key in['X','Y','S','R','k','Squotient','Rquotient']]
        norm=plus(square(S),product(C(-1),add(square(B),C(1),-1),square(R)),C(-1))
        cut(s['cuts']['norm3'],norm,i['rows']['norm3'])
        cut(s['cuts']['S_mod_U'],plus(S,product(C(-1),X),product(C(-1),U,sq)),i['rows']['S_mod_U'])
        cut(s['cuts']['R_mod_4Y'],plus(R,product(C(-1),k),product(C(-4),Y,rq)),i['rows']['R_mod_4Y'])
    need(set(checked)==set(affected_constraints)and len(checked)==46,'every changed constraint restored by a full unit ideal')
    return dict(original_rows=1177,gate_rows=1029,nongate_rows=148,free_coordinates=230,
        changed_free_coordinates=sorted(changed_free),affected_gate_rows=affected_gates,
        affected_nongate_rows=affected_constraints,complete_independent_unit_constraint_ideals=46,
        unchanged_guard_indices=sorted(remaining),protected_main_pairs=len(raw['indices']),
        protected_actual_power_calls=len(raw['powers']))


def pell(a,h):
    x,y=1,0
    for _ in range(h):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def universal_lift_algebra():
    A,U,Vv,q,B,bq,t,e=map(V,range(8));fourV=product(C(4),Vv)
    absU=mul(e,U)
    qn=add(q,mul(absU,t));Bn=add(B,product(fourV,absU,t));bqn=add(bq,product(fourV,e,t))
    constructor=plus(B,C(-1),product(C(-1),fourV,plus(q,C(1))))
    lifted=plus(Bn,C(-1),product(C(-1),fourV,plus(qn,C(1))))
    congruence=plus(B,product(C(-1),A),product(C(-1),U,bq))
    lifted_congruence=plus(Bn,product(C(-1),A),product(C(-1),U,bqn))
    need(lifted==constructor and lifted_congruence==congruence,'universal fixed-U/V lift identities, no denominator or CRT')
    return 2


def controls():
    parity=congruences=bounds=lifts=0
    for a in range(2,8):
        for h in range(15):
            x,y=pell(a,h);xm,ym=pell(-a,h)
            need(xm==(-1)**h*x and ym==(-1 if h%2==0 else 1)*y,'negative-base parity, including h0')
            parity+=1
    for modulus in range(2,18):
        for e in[-1,1]:
            b=e+modulus*(2 if e==1 else 3)
            for h in range(13):
                x,y=pell(b,h)
                need((x-e**h)%modulus==0 and (y-(h if e==1 or h%2 else -h))%modulus==0,'base plus/minus1 reduction')
                congruences+=1
    for u in list(range(-8,-1))+list(range(2,9)):
        e=1 if u>0 else-1
        for q in range(-15,16):
            qn=q+abs(u)*(abs(q)+1)
            need(qn>=abs(q)+2 and u*e==abs(u),'strict positive q4 lift with either U sign');bounds+=1
    # Explicit i=n,Y=1 negative-B endpoint, and both signs of U.
    for u in[-3,3]:
        A,Vv,q,B,bq,X,Y,k=3,1,-2,-3,(-6)//u,3,1,1
        S,R=pell(B,k)
        need(S==-3 and R==1 and S*S-(B*B-1)*R*R==1 and (S-X)%u==0,'negative-B endpoint assumptions')
        t=abs(q)+1;qn=q+abs(u)*t;Bn=B+4*Vv*abs(u)*t;bqn=bq+4*Vv*(1 if u>0 else-1)*t
        Sn,Rn=pell(Bn,k)
        need(qn>=0 and Bn==1+4*Vv*(qn+1)and Bn-A==u*bqn
             and (Sn-X)%u==0 and (Rn-k)%(4*Y)==0 and Sn*Sn-(Bn*Bn-1)*Rn*Rn==1,'exact endpoint reconstruction')
        lifts+=1
    # Finite residual-class implication, explicitly allowing independent S/R signs.
    signed_index=0
    for a in range(2,7):
        for i in range(1,4):
            x,Y=pell(a,i)
            for n in range(i,9):
                u,v=pell(a,n)
                if v%(Y*Y):continue
                for b in range(-14,-1):
                    if(b-a)%u or(b-1)%(4*Y):continue
                    for h in range(9):
                        s,r=pell(abs(b),h)
                        for eps in[-1,1]:
                            for delta in[-1,1]:
                                for k in range(1,Y+1):
                                    if(eps*s-x)%u==0 and(delta*r-k)%(4*Y)==0:
                                        need(k==i,'finite signed negative-B index implication');signed_index+=1
    return dict(negative_base_parity=parity,base_plus_minus_one_congruences=congruences,
        positive_q4_bound_both_U_signs=bounds,negative_B_endpoint_i_equals_n_Y_equals_one_both_U_signs=lifts,
        finite_signed_negative_B_index_instances=signed_index,
        scope='Diagnostics only; ordinary parity/induction/classification/short-interval proof supplies the unbounded theorem.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    sealed(PACKET);sealed(PRIOR)
    for n,h in load(PRIOR/'SOURCE_PINS.json')['files'].items():need(sha(ROOT/n)==h,'whole frozen source '+n)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json');cert=load(PRIOR/'CERTIFICATE.json')
    result=literal_audit(raw,interfaces,cert);author=load(PACKET/'VERIFY.json')
    need(result['affected_gate_rows']==author['changed_gate_rows']and result['affected_nongate_rows']==author['affected_private_constraints'],
         'independently reconstructed closure agrees with author receipt')
    rejected=[]
    def reject(label,r,i,c):
        try:literal_audit(r,i,c)
        except(ValueError,KeyError,IndexError,TypeError):rejected.append(label)
        else:raise ValueError('corrupt literal certificate accepted: '+label)
    bad=deepcopy(raw);rid=interfaces['semantic_non_gate_rows'][0];bad['rows'][rid]['terms'].append([1,[657]])
    reject('q4 use hidden outside the private constraint inventory',bad,interfaces,cert)
    bad=deepcopy(raw);rid=interfaces['all_gate_rows'][0];v=bad['rows'][rid]['gate']
    term=next(t for t in bad['rows'][rid]['terms']if t[1]==[v]);term[0]*=2
    reject('nonunit integer gate pivot',bad,interfaces,cert)
    bad=deepcopy(interfaces);bad['private_non_gate_rows'].pop()
    reject('missing source constraint in supplied private inventory',raw,bad,cert)
    bad=deepcopy(cert);bad['seeds'][0]['cuts']['norm3']['row_combination'][0]['multiplier'][0][0]+=1
    reject('changed whole comparison norm ideal',raw,interfaces,bad)
    bad=deepcopy(cert);bad['seeds'][0]['aliases']['Squotient']+=1
    reject('wrong comparison quotient coordinate',raw,interfaces,bad)
    bad=deepcopy(cert);bad['remaining_raw_guard_indices'].remove(657);bad['remaining_raw_guard_indices'].append(658)
    reject('changed retained guard instead of omitted q4',raw,interfaces,bad)
    proc=subprocess.run([sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(PACKET/'audit.py'),'--output',str(args.output)+'.author-tmp'],capture_output=True,text=True)
    need(proc.returncode==0,'scoped author replay: '+proc.stderr)
    generated=Path(str(args.output)+'.author-tmp');audit=load(generated);generated.unlink()
    expected=load(PACKET/('VERIFY_OPTIMIZED.json'if sys.flags.optimize else'VERIFY.json'))
    need(audit==expected,'entire normal/optimized author receipt reproduction')
    result.update(status='PASS',optimized_python=bool(sys.flags.optimize),source_pins={str(p.relative_to(ROOT)):sha(p)for p in[
        PACKET/'README.md',PACKET/'audit.py',PACKET/'MANIFEST.json',PRIOR/'README.md',PRIOR/'CERTIFICATE.json',PRIOR/'MANIFEST.json']},
        independent_peer_program_sha256=sha(Path(__file__)),ordinary_review_sha256=sha(Path(__file__).with_suffix('.md')),
        universal_lift_identities=universal_lift_algebra(),finite_controls=controls(),
        rejected_corruptions=rejected,
        complete_author_replay=dict(status='PASS',whole_receipt_matches=True),
        scope='Independent complete1177-row use boundary and46 exact unit constraints plus ordinary adversarial signed-B/fixed-U,V lift review. No78-guard quartic, projected count, Lean or internal-ZFC claim.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k]for k in['status','optimized_python','original_rows','gate_rows','nongate_rows','complete_independent_unit_constraint_ideals','finite_controls']},indent=2))


if __name__=='__main__':main()

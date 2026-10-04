#!/usr/bin/env python3
"""Independent full-source diagnostic audit; deliberately outside compiler slices."""
import argparse
from collections import Counter
import hashlib
import json
import operator
from pathlib import Path

AUTHOR={
 'complete83_nonunit_positive_diagnostic.py':'47cd06b52e0f22cd712e1fe09abb8af8061f123216acdc8b083be49d46d202ac',
 'complete83_nonunit_positive_diagnostic.json':'d3aea11b4a0c5880b77d7909a260858b8592ef6ff1522f51cfc05ae8bee71f1d',
 'complete83_nonunit_positive_diagnostic.md':'98f279ddeeca8b369634a0458d9e4501bc62a325cc13bcd464c7d50cf3bdddcd',
}
PARENT={
 'complete83_free_coefficient_scout.py':'a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485',
 'complete83_free_coefficient_scout.json':'682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
 'complete83_free_coefficient_scout.md':'867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
}
def require(x,m):
    if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def same(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def pell(A,n):
    # Sequential second-order recurrence, not the author's binary pair powering.
    x0,x1=1,A;y0,y1=0,1
    if n==0:return x0,y0
    for _ in range(1,n):x0,x1=x1,2*A*x1-x0;y0,y1=y1,2*A*y1-y0
    return x1,y1

def recover(A,x,y):
    D=A*A-1;steps=0
    require(x>0 and y>=0 and x*x-D*y*y==1,'positive Pell solution')
    while y:
        u=A*x-D*y;v=A*y-x
        require(u>0 and 0<=v<y,'strict inverse Pell step')
        x,y=u,v;steps+=1
    require(x==1,'Pell endpoint')
    return steps

def reconstruct_values():
    D,c=pell(26,1351);tau,kn=pell(257,855);k=2*kn;mu,kappa=pell(26,17)
    def divide(a,b):
        q,r=divmod(a,b);require(r==0,'exact quotient');return q
    gamma=divide(D-24*c-2,99);rho=divide(mu-24*kappa+4,99)
    v={'Jrep':1,'F':1,'alpha':1,'transport_quotient':670,'f':1,
       'h':divide(k-2702,16),'aux_coefficient_root':26,'auxiliary_quotient':1,
       's':1,'w':1,'tau_root':tau,'eta':c-8*k,'zeta':9*k-c,'y_aux':2703,
       'Z':1,'delta':divide(kappa-17,675),'rho':rho,'sigma':gamma-rho,'x':1,
       'Bm1':1,'Kconstant':1,'twice_cell_bits':2,'inner_bits':15,'MC':2694,'MF':2}
    require(all(type(x) is int and x>0 for x in v.values()),'all 25 supplied values positive')
    require(gamma>rho>0 and 8*k<c<9*k,'both positivity comparisons')
    return v

def evaluate_and_audit(p,v):
    require(set(v)==set(p['free']),'exact supplied interface')
    partition=p['witnesses']+[p['ordinary_input']]+p['fixed_numerals']
    require(len(partition)==len(set(partition))==25 and set(partition)==set(v),'disjoint input classification')
    env=dict(v);table={};counts=Counter();functions={'+':operator.add,'-':operator.sub,'*':operator.mul}
    for row in p['source']:
        require(type(row) is list and len(row)==4,'literal row')
        n,op,a,b=row
        require(type(n) is str and n not in env and op in functions,'SSA and opcode')
        require(all(type(x) is int or type(x) is str and x in env for x in (a,b)),'prior operands')
        env[n]=functions[op](env[a] if type(a) is str else a,env[b] if type(b) is str else b)
        table[n]=[x for x in (a,b) if type(x) is str];counts[op]+=1
    require(p['output']==p['source'][-1][0]=='polynomial','complete final row')
    live=set();todo=[p['output']]
    while todo:
        n=todo.pop()
        if n in live:continue
        live.add(n);todo+=table.get(n,[])
    require(live==set(env),'all rows and all free ports live')
    require((counts['*'],counts['+']+counts['-'])==(46,37),'paid full count')
    return env

def verify(root,author_root):
    for n,pin in AUTHOR.items():require(sha((author_root/n).read_bytes())==pin,'author pin '+n)
    for n,pin in PARENT.items():require(sha((root/n).read_bytes())==pin,'parent pin '+n)
    a=json.loads((author_root/'complete83_nonunit_positive_diagnostic.json').read_text())
    p=json.loads((root/'complete83_free_coefficient_scout.json').read_text())['packet']
    require(a['parent_pins']==PARENT and a['checker_sha256']==AUTHOR['complete83_nonunit_positive_diagnostic.py'],'author provenance')
    for k in ['source','output','free','witnesses','fixed_numerals']:require(same(a[k],p[k]),'identical saved source/interface '+k)
    v=reconstruct_values();e=evaluate_and_audit(p,v)
    vh={n:hex(v[n]) for n in p['free']};rh={r[0]:hex(e[r[0]]) for r in p['source']}
    require(same(vh,a['positive_assignment_hex']),'all 25 exact free values')
    require(same(rh,a['actual_register_values_hex']),'all 83 exact computed values')
    factors=[e[n] for n in p['factors']]
    require(factors==[1,1,1,1,1,-675,-1] and factors==a['factor_values'],'seven actual factors')
    prod=1
    for x in factors:prod*=x
    require(prod==e['A']==675 and e['polynomial']==0,'entire paid output')
    require(e['q']==2 and e['wn2']==2 and e['sn2']==8 and e['R12']==24 and e['a4m5']==99,'small actual producers')
    require(e['marked_rhs']==-3 and e['W']==-4 and e['r_lhs']==2701 and e['aux_u_rhs']==-2701,'signed computed ports')
    require(e['R10b']%2==0,'first Pell ordinate parity')
    indices=dict(main=recover(26,e['R14'],e['R10a']),first=recover(257,e['tau_root'],e['R10b']//2),
                 input=recover(26,e['exponent_rhs'],e['index_rhs']),auxiliary=recover(26,26*abs(e['aux_u_rhs']),e['y_aux']))
    require(indices==dict(main=1351,first=855,input=17,auxiliary=3),'independently recovered ranks')
    require(a['pell_parameters']==dict(main_A=26,main_index=1351,first_P=257,first_index=855,input_index=17),'advertised Pell parameters')
    require(a['factor_names']==p['factors'] and a['supplied_counts']==dict(witnesses=18,ordinary_inputs=1,fixed_numerals=6),'advertised interface counts')
    require(a['maximum_free_bit_length']==max(x.bit_length() for x in v.values()) and a['maximum_computed_bit_length']==max(abs(e[r[0]]).bit_length() for r in p['source']),'advertised bit lengths')
    require(pow(2,1351,99)==2 and pow(2,17,99)==95,'both projection residues')
    require(e['R10b']%16==2702%16,'exact retained first-index congruence')
    # Concrete necessary compiler conditions fail; no admissibility is inferred.
    B=v['Bm1']+1;MF0=v['MF']-v['Bm1'];d=v['twice_cell_bits']//2
    exclusions=dict(B_below_16=B<16,MC_not_between_zero_and_Bminus1=not(0<v['MC']<B-1),
                    native_MF_not_between_zero_and_Bminus1=not(0<MF0<B-1),native_MF_mod8_not4=MF0%8!=4,
                    inner_bits_greater_than_d=v['inner_bits']>d)
    require(all(exclusions.values()),'explicit noncompiler numerals')
    require(a['scope']['full_polynomial_zero_materialized'] is True and a['scope']['valid_fixed_compiler_slice'] is False and a['scope']['false_accepted_input_claim'] is False and a['scope']['universal_bound_claim'] is False,'honest diagnostic scope')
    require(a['Delta']==675 and a['full_output']==0 and a['actual_ledger']==dict(M=46,A=37,total=83),'receipt ledger/output')
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PARENT,
                source_sha256_of_array=sha(stable(p['source'])),paid_gates=83,M=46,A=37,
                positive_free_values=25,positive_witnesses=18,ordinary_inputs=1,positive_fixed_numerals=6,
                exact_supplied_sha256=sha(stable(vh)),exact_register_sha256=sha(stable(rh)),
                recovered_Pell_indices=indices,factors=factors,Delta=675,output=0,
                computed_ports={n:e[n] for n in ['q','wn2','sn2','R12','A','a4m5','marked_rhs','W','r_lhs','aux_u_rhs']},
                compiler_exclusions=exclusions,maximum_free_bits=max(x.bit_length() for x in v.values()),
                maximum_register_bits=max(abs(e[r[0]]).bit_length() for r in p['source']),
                scope='Fully materialized positive tuple and entire83 output zero at explicitly invalid compiler numerals; no accepted-language refutation or universal bound.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--author-root',type=Path)
    group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path);a=ap.parse_args()
    r=verify(a.root,a.author_root or a.root);require(same(r,json.loads(json.dumps(r))),'type exact JSON')
    if a.expect:require(same(r,json.loads(a.expect.read_text())),'exact receipt mismatch')
    else:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',paid_gates=83,positive_free_values=25,factors=r['factors'],output=0,valid_compiler_slice=False)))
if __name__=='__main__':main()

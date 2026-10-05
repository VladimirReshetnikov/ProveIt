#!/usr/bin/env python3
"""Fresh six-port polynomial proof and inert full-source ledger.
No predecessor program or saved full-source array is evaluated/imported.
"""
import argparse
import hashlib
import itertools
import json
import pathlib
from fractions import Fraction

DEPENDENCIES = [
 'complete84_scaled_strong_output.json', 'complete84_scaled_strong_output.md',
 'complete84_aux_strong_joint_cut.md', 'complete84_auxiliary_nine_gate_frontier.md',
 'complete86_joint_strong_auxiliary_scout.md', 'complete85_reduced_auxiliary_degree.md',
]
PARENT_PIN = '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
REMOVED = ['aux_square_gap','norm_strong','L17','norm_aux','norm_four',
           'norm_product','all_units','seven_units','polynomial']
OLD = [
 ['aux_square_gap','-','H2','aux_y2'],
 ['norm_strong','-','scaled_f_square','R16'],
 ['L17','*','R16','aux_square_gap'],
 ['norm_aux','+','L17','aux_y2'],
 ['norm_four','*','norm_triple','norm_aux'],
 ['norm_product','*','norm_four','norm_index'],
 ['all_units','*','norm_product','norm_transport'],
 ['seven_units','*','all_units','norm_strong'],
 ['polynomial','-','seven_units','A'],
]
TAIL = [
 ['boundary_p5_index','*','norm_triple','norm_index'],
 ['boundary_p5','*','boundary_p5_index','norm_transport'],
 ['boundary_strong','-','scaled_f_square','R16'],
 ['boundary_gap','-','H2','aux_y2'],
 ['boundary_weighted_gap','*','R16','boundary_gap'],
 ['boundary_auxiliary','+','boundary_weighted_gap','aux_y2'],
 ['boundary_joint','*','boundary_strong','boundary_auxiliary'],
 ['boundary_scaled','*','boundary_p5','boundary_joint'],
 ['polynomial','-','boundary_scaled','A'],
]
GUARDS = [
 ['q','+','repunit',1], ['repunit','*','Bm1','Jrep'],
 ['n2','*','Lbig','q'], ['sn2','*','s','n2'],
 ['wn2','*','w','q'], ['UM','*','wn2','sn2'], ['R12','+','UM','sn2'],
 ['a_square','*','R12','R12'], ['a4','*',4,'R12'], ['a4m5','+','a4',3],
 ['A','+','a_square','a4m5'], ['R10a','+','ksn2','eta'],
 ['c2','*','R10a','R10a'], ['Ac2','*','A','c2'],
 ['aux_coefficient_root','*','i','Ac2'], ['R16','*','aux_coefficient_root','aux_coefficient_root'],
 ['L16','*','f','f'], ['scaled_f_square','*','A','L16'],
 ['auxiliary_Tf','*','auxiliary_quotient','f'],
 ['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
 ['auxiliary_R_f2','*','r_lhs','L16'], ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
 ['H2','*','aux_u_rhs','aux_u_rhs'], ['aux_y2','*','y_aux','y_aux'],
 ['tau_square','*','tau_root','tau_root'], ['norm_first','-','tau_square','first_product'],
 ['norm_pair','*','norm_first','norm_main'], ['norm_triple','*','norm_pair','norm_input'],
]

def need(ok, text):
    if not ok: raise ValueError(text)

def digest(data): return hashlib.sha256(data).hexdigest()

def add(a,b,sign=1):
    c=dict(a)
    for e,v in b.items(): c[e]=c.get(e,0)+sign*v
    return {e:v for e,v in c.items() if v}

def mul(a,b):
    c={}
    for e,u in a.items():
        for f,v in b.items():
            g=tuple(x+y for x,y in zip(e,f)); c[g]=c.get(g,0)+u*v
    return {e:v for e,v in c.items() if v}

def var(n,i): return {tuple(int(j==i) for j in range(n)):1}
def const(n,v): return {(0,)*n:v} if v else {}
def degree(p): return max(map(sum,p))
def serial(p): return [{'exponents':list(e),'coefficient':v} for e,v in sorted(p.items())]

def rank(rows):
    a=[list(map(Fraction,r)) for r in rows]; k=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(k,len(a)) if a[i][j]),None)
        if pivot is None: continue
        a[k],a[pivot]=a[pivot],a[k]
        d=a[k][j]; a[k]=[v/d for v in a[k]]
        for i in range(len(a)):
            if i!=k:
                d=a[i][j]; a[i]=[x-d*y for x,y in zip(a[i],a[k])]
        k+=1
    return k

def affine_rank(p):
    base=next(iter(p)); return rank([[a-b for a,b in zip(e,base)] for e in p])

def ledger(rows):
    m=sum(r[1]=='*' for r in rows); return {'M':m,'A':len(rows)-m,'total':len(rows)}

def graph(rows,free):
    seen=set(free); by={}
    for row in rows:
        name,op,a,b=row
        need(name not in seen and op in ['+','-','*'],'row or operation')
        need(all(type(x) is int or x in seen for x in [a,b]),'operand before definition')
        seen.add(name); by[name]=row
    live=set(); stack=['polynomial']
    while stack:
        x=stack.pop()
        if type(x) is int or x in live: continue
        live.add(x)
        if x in by: stack.extend(by[x][2:])
    need(live==seen,'dead rows or ports')
    return {'all_rows_live':True,'all_free_ports_live':True,'free_ports':len(free)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=pathlib.Path,required=True)
    ap.add_argument('--output',type=pathlib.Path,required=True)
    args=ap.parse_args()
    data={name:(args.root/name).read_bytes() for name in DEPENDENCIES}
    need(digest(data[DEPENDENCIES[0]])==PARENT_PIN,'parent changed')
    old=json.loads(data[DEPENDENCIES[0]])['packet']
    rows=old['source']; by={r[0]:r for r in rows}
    need(len(by)==len(rows)==84,'parent census')
    for row in OLD+GUARDS: need(by.get(row[0])==row,'literal guard '+row[0])
    prefix=[r for r in rows if r[0] not in REMOVED]
    new=prefix+TAIL
    need(ledger(prefix)=={'M':42,'A':33,'total':75},'prefix count')
    need(ledger(new)=={'M':47,'A':37,'total':84},'full count')
    closure=graph(new,old['free'])
    P,U,Q,A,B,D=[var(6,i) for i in range(6)]
    joint=mul(add(U,Q,-1),add(mul(Q,add(A,B,-1)),B))
    target=add(mul(P,joint),D,-1)
    top={e:v for e,v in target.items() if sum(e)==4}
    need(top==mul(mul(P,Q),mul(add(U,Q,-1),add(A,B,-1))),'quartic leader')
    need(len(target)==7 and affine_rank(target)==4,'support rank')
    multipliers={'one':const(6,1),'Delta':D,'Q':Q,'scaled_strong':add(U,Q,-1),
                 'positive_sum':add(mul(add(U,Q,-1),add(U,Q,-1)),mul(D,D))}
    supplements=[]
    for name,h in multipliers.items():
        product=mul(target,h)
        need(degree(product)==4+degree(h) and affine_rank(product)>=4,'supplement')
        supplements.append({'multiplier':name,'degree':degree(product),'terms':len(product),'support_affine_dimension':affine_rank(product)})
    # Expand ONLY this new nine-row cut, never the parent or full saved array.
    cuts=['norm_triple','norm_index','norm_transport','scaled_f_square','R16','H2','aux_y2','A']
    env={x:var(8,i) for i,x in enumerate(cuts)}
    for name,op,a,b in TAIL:
        x,y=env[a],env[b]
        env[name]=mul(x,y) if op=='*' else add(x,y,-1 if op=='-' else 1)
    v=[var(8,i) for i in range(8)]
    expected=add(mul(mul(mul(v[0],v[1]),v[2]),mul(add(v[3],v[4],-1),add(mul(v[4],add(v[5],v[6],-1)),v[6]))),v[7],-1)
    need(env['polynomial']==expected,'full finalizer cut identity')
    result={'schema':'scaled-finalizer-boundary-v1','pins':{k:digest(v) for k,v in data.items()},
      'helper_sha256':digest(pathlib.Path(__file__).read_bytes()),
      'model':{'independent_cut_order':['P5','Delta_f2','S2','V2','y2','Delta'],
        'only_these_nonscalar_ports':True,'binary_operations':['+','-','*'],'division':False,
        'minimum_gates_every_nonzero_polynomial_multiple':7,'attained_for_multiplier_one':True,
        'outside_donor_sharing_excluded':True,'zero_set_only_replacements_excluded':True},
      'target':serial(target),'quartic_leader':serial(top),'support_affine_dimension':affine_rank(target),
      'multiplier_supplements_not_exhaustive':supplements,
      'source':new,'removed_parent_rows':OLD,'literal_source_guards':GUARDS,
      'free':old['free'],'witnesses':old['witnesses'],'fixed_numerals':old['fixed_numerals'],
      'counts':{'retained_prefix':ledger(prefix),'materialize_P5':ledger(TAIL[:2]),'six_port_residual':ledger(TAIL[2:]),'complete':ledger(new)},
      'closure':closure,'finalizer_eight_cut_identity':serial(env['polynomial']),
      'scope':{'predecessor_execution_import':False,'saved_full_array_evaluation':False,'finite_native_zero_claim':False,
        'new_cut_symbolic_expansion_only':True,'same_whole_polynomial_multiplier_one':True,
        'degree187_inherited_only_for_multiplier_one':True,'new_gate_saving':False,'global_optimality':False},
      'status':'PASS algebra, complete static ledger and scoped seven-gate boundary'}
    with args.output.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(result,f,sort_keys=True,indent=2); f.write('\n')
    print('PASS: exact7 at six ports; full84 tie, all25 ports live; no predecessor execution')

if __name__=='__main__': main()

"""Fresh all-value 505-to-477 U21 source rewrite; predecessors are inert bytes only."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

DEFAULT_ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS = {
 'residue_affine_sparse_control_codes.py':'433c4d87af47d166d8c26db4e879a77e12a3fbcf3e7a1bf8c125701b2b21a4a7',
 'residue_affine_sparse_control_codes.json':'2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d',
 'residue_affine_sparse_factored.md':'b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7',
 'residue_affine_sparse_scale538.md':'0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623',
 'residue_affine_sparse_terminal537.md':'9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1',
 'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
}
GROUPS = ['prime_selector_93','prime_selector_95','prime_selector_97','prime_selector_101',
          'prime_selector_109','prime_selector_113','prime_selector_115',
          'selectors_36','control_codes__duplicate_state_6','edge_29']
OUTPUT = 'norm_output'

def need(condition, message):
    if not condition: raise ValueError(message)

def digest(b): return hashlib.sha256(b).hexdigest()
def canonical(x): return json.dumps(x, sort_keys=True, separators=(',',':')).encode()
def unique_pairs(pairs):
    d={}
    for k,v in pairs:
        need(k not in d, 'duplicate JSON key '+k); d[k]=v
    return d

def read_json(path): return json.loads(path.read_text(), object_pairs_hook=unique_pairs)
def definitions(rows):
    d={}
    for row in rows:
        need(type(row)is list and len(row)==4,'row shape')
        n,op,a,b=row
        need(type(n)is str and n not in d and op in ('+','-','*'),'SSA/op')
        need(all(type(t)in (str,int) for t in (a,b)),'exact operand types')
        d[n]=row
    return d

def leaves(rows):
    d=definitions(rows)
    return sorted({a for n,o,a,b in rows for a in (a,b) if type(a)is str and a not in d})

def reachable(d, roots):
    live=set()
    def visit(n):
        if n not in d or n in live:return
        live.add(n)
        for v in d[n][2:]:
            if type(v)is str:visit(v)
    for n in roots:visit(n)
    return live

def validate(rows, ports):
    d=definitions(rows); seen=set(ports)
    for n,o,a,b in rows:
        need(all(type(v)is int or v in seen for v in (a,b)), 'forward/unbound '+n)
        need(n not in seen,'port/SSA collision');seen.add(n)
    need(reachable(d,[OUTPUT])==set(d),'dead rows')
    need(leaves(rows)==sorted(ports),'changed free interface')
    c=Counter(r[1] for r in rows)
    return dict(operations=len(rows), multiplications=c['*'], additions_subtractions=c['+']+c['-'])

def rewrite(rows):
    d=definitions(rows)
    need(d['selectors_70']==['selectors_70','+','selectors_69','edge_35'],'parent J')
    removed=[f'selectors_{i}' for i in range(37,70)]
    removed += ['non_increment_149','non_decrement_150','zero_complement_151','range_repeat_shift_407','three_range_repeat_408']
    for n in removed:del d[n]
    acc=GROUPS[0]
    for i,n in enumerate(GROUPS[1:]):
        name='selectors_70' if i==8 else f'u21_grouped_J_{i}'
        d[name]=[name,'+',acc,n];acc=name
    need(d['common_quotient_152']==['common_quotient_152','+','positive_quotient_word_135','difference_word_148'],'payload parent')
    d['common_quotient_152']=['common_quotient_152','+','quotient_71','difference_word_148']
    d['u21_nonzero_actions']=['u21_nonzero_actions','+','action_selector_123','action_selector_134']
    d['u21_nonzero_or_test']=['u21_nonzero_or_test','+','u21_nonzero_actions','edge_14']
    d['common_payload_154']=['common_payload_154','+','common_remainder_153','u21_nonzero_or_test']
    need(d['all_ranges_427']==['all_ranges_427','*','range_mask_91','three_range_repeat_408'],'range consumer')
    d['all_ranges_427']=['all_ranges_427','*','range_mask_91','repeat_odd_318']
    live=reachable(d,[OUTPUT]); need(live==set(d),'unexpected dangling/dead replacement')
    out=[];visited=set();visiting=set()
    def emit(n):
        if n not in d or n in visited:return
        need(n not in visiting,'cycle');visiting.add(n)
        for v in d[n][2:]:
            if type(v)is str:emit(v)
        visiting.remove(n);visited.add(n);out.append(d[n])
    # Preserve original ordering except dependencies that must precede the new J.
    for n,_,_,_ in rows:
        if n in d:emit(n)
    need(visited==set(d),'unemitted additions')
    return out,removed

# Exact small polynomial ring. Only explicitly bounded local ancestor cones are expanded.
def padd(a,b,sign=1):
    c=a.copy()
    for k,v in b.items(): c[k]=c.get(k,0)+sign*v
    return {k:v for k,v in c.items() if v}
def pmul(a,b):
    c={}
    for k,v in a.items():
        for l,w in b.items():
            m=tuple(sorted(k+l));c[m]=c.get(m,0)+v*w
    return {k:v for k,v in c.items() if v}
def poly_at(rows, root, boundaries):
    d=definitions(rows);cache={v:{(v,):1} for v in boundaries}
    def get(v):
        if type(v)is int:return {():v} if v else {}
        if v in cache:return cache[v]
        need(v in d,'unbound polynomial leaf '+v)
        _,o,a,b=d[v];a,b=get(a),get(b)
        p=pmul(a,b) if o=='*' else padd(a,b,1 if o=='+' else -1)
        need(len(p)<200,'unexpected expansion');cache[v]=p;return p
    return get(root)
def plist(p):return [[list(k),v] for k,v in sorted(p.items())]

def exact_contract(old,new):
    ports=leaves(old)
    pj=poly_at(old,'selectors_70',ports); nj=poly_at(new,'selectors_70',ports)
    need(pj==nj,'J identity')
    partition=[]
    for name in GROUPS:
        p=poly_at(old,name,{f'edge_{i}' for i in range(36)})
        need(all(len(k)==1 and v==1 for k,v in p.items()),'non Boolean group')
        partition.append(dict(register=name,edges=sorted(int(k[0][5:]) for k in p)))
    need(sorted(e for g in partition for e in g['edges'])==list(range(36)),'not a disjoint partition')
    rp=poly_at(old,'three_range_repeat_408',{'scale_89'})
    rn=poly_at(new,'repeat_odd_318',{'scale_89'})
    need(rp==rn=={():1,('scale_89',):1,('scale_89','scale_89'):1},'R3 identity')
    bd={'quotient_71','selectors_70','difference_word_148','complement_73','action_selector_123','action_selector_134','edge_14'}
    pp=poly_at(old,'common_payload_154',bd);np=poly_at(new,'common_payload_154',bd)
    need(pp==np,'joint payload identity')
    # Hash-consed exact-expression DAG; justified local equalities are the only substitutions.
    def token(v):return digest(canonical(v))
    envs=[]
    for rows in (old,new):
        env={v:token(['variable',v]) for v in ports}
        def get(v):return token(['integer',v]) if type(v)is int else env[v]
        for n,o,a,b in rows:
            xs=[get(a),get(b)]
            if o in ('+','*'):xs.sort()
            value=token([o]+xs)
            if n=='three_range_repeat_408':value=env['repeat_odd_318']
            if envs and n in ('selectors_70','common_payload_154'):value=envs[0][n]
            env[n]=value
        envs.append(env)
    changed={'common_quotient_152','common_remainder_153'}
    common=set(definitions(old))&set(definitions(new));checked=sorted(common-changed)
    need(all(envs[0][n]==envs[1][n] for n in checked),'whole DAG congruence')
    need(envs[0][OUTPUT]==envs[1][OUTPUT],'output identity')
    native=[n for n in common if n.startswith('native__')]
    residuals=[f'norm_residual{i}' for i in range(6)]
    need(all(envs[0][n]==envs[1][n] for n in native+residuals),'native/residual identity')
    return dict(disjoint_partition=partition,J_polynomial=plist(pj),range_polynomial=plist(rp),
        payload_polynomial=plist(pp),same_value_retained_registers=len(checked),
        unchanged_native_registers=len(native),same_value_residuals=residuals,
        all_ring_identity='F477 = F505 on identical supplied coordinates over every commutative ring',
        changed_intermediate_values=sorted(changed))

def evaluate(rows, values, modulus=None):
    e=dict(values)
    for n,o,a,b in rows:
        a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
        v=a*b if o=='*' else a+b if o=='+' else a-b
        e[n]=v%modulus if modulus else v
    return e

def sample_checks(old,new):
    rng=random.Random(47720261004);ports=leaves(old);count=0
    for p in (1000000007,1000000009):
        for _ in range(16):
            v={n:rng.randrange(-30,31) for n in ports};a=evaluate(old,v,p);b=evaluate(new,v,p)
            need(a[OUTPUT]==b[OUTPUT],'modular output check')
            for n in ('selectors_70','common_payload_154','joined_H_406','joined_M_431','joined_Z_451','sparse_all_units'):
                need(a[n]==b[n],'modular cut '+n)
            count+=1
    # Small actual rationals; native degree is large but integer sizes remain bounded.
    for _ in range(4):
        v={n:Fraction(rng.randrange(-1,2),2) for n in ports}
        need(evaluate(old,v)[OUTPUT]==evaluate(new,v)[OUTPUT],'rational output check')
    return dict(full_modular_source_pairs=count,moduli=[1000000007,1000000009],full_signed_rational_source_pairs=4,
                finite_scope='Off-zero algebra checks only; no accepting history or full positive Pell zero materialized')

def build(root):
    for n,h in PINS.items(): need(digest((root/n).read_bytes())==h,'pin '+n)
    parent=read_json(root/'residue_affine_sparse_control_codes.json');old=parent['source']
    ports=leaves(old); need(len(ports)==69 and 'radix_program' not in ports,'one-program parent interface')
    parameters=['program','input']
    height_rows=[['height_83','+','program','input'],['height_85','+','height_83','height_slack'],['radix_86','*',64,'height_85']]
    need(all(r in old for r in height_rows),'literal one-program height and radix')
    need(parent['source_sha256']==digest(json.dumps(old).encode()),'saved parent source binding')
    before=validate(old,ports);need(before==dict(operations=505,multiplications=177,additions_subtractions=328),'parent count')
    parent_source_bytes=canonical(old)
    new,removed=rewrite(old)
    need(canonical(old)==parent_source_bytes,'parent source mutated in memory')
    after=validate(new,ports)
    need(after==dict(operations=477,multiplications=176,additions_subtractions=301),'derived count')
    eq=exact_contract(old,new)
    need(all(r in new for r in old if r[0].startswith('native__')),'literal native rows')
    finalizer=old[485:];need(len(finalizer)==20 and all(r in new for r in finalizer),'literal finalizer rows')
    need(all(r in new for r in height_rows),'one-program height and radix retained')
    final_names={r[0] for r in finalizer}
    certificate=[r for r in new if r[0] not in final_names]; cc=Counter(r[1] for r in certificate)
    certificate_ledger=dict(operations=len(certificate),multiplications=cc['*'],additions_subtractions=cc['+']+cc['-'],equations=7,witnesses=67)
    need(certificate_ledger==dict(operations=457,multiplications=169,additions_subtractions=288,equations=7,witnesses=67),'derived certificate count')
    return dict(status='PASS_U21_SHARED477',source_sha256=digest(Path(__file__).read_bytes()),dependencies=PINS,
        packet=dict(source=new,output=OUTPUT,parameters=parameters,
            fixed_program_parameters=['program'],ordinary_input_parameter='input',
            witnesses=sorted(set(ports)-set(parameters)),ledger=dict(after,witnesses=67),
            certificate_ledger=certificate_ledger,
            polynomial_degree_upper_bound=5091,exact_degree_claimed=False,
            source_sha256=digest(canonical(new)),
            valid_recipe='Fixed positive program E=3^e from the inherited U21 compiler; literal radix B=64*(E+x+height_slack), ordinary input x>0',
            literal_height_radix_rows=height_rows),
        rewrite=dict(parent_ledger=before,removed_names=removed,new_names=sorted(set(definitions(new))-set(definitions(old))),
            stage_savings={'selector_population':{'M':0,'A':25},'range_repunit':{'M':1,'A':1},'joint_payload':{'M':0,'A':1}},
            paid_relocations='Existing prime-class and state-pair producers moved before J by topological scheduling'),
        exact_contract=eq,finite_checks=sample_checks(old,new),
        scope='Identical full polynomial, supplied coordinates and positive zero sets to the pinned 505 default coupled-product source; inherited ordinary positive input and sole fixed program E=3^e with literal radix multiplier64; no new claim below84, no circuit minimality, no exact degree claim')

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=DEFAULT_ROOT)
    p.add_argument('--write',type=Path);p.add_argument('--expect',type=Path,default=Path(__file__).with_suffix('.json'));a=p.parse_args()
    r=build(a.root)
    if a.write:a.write.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    else:need(canonical(read_json(a.expect))==canonical(r),'receipt exact typed replay')
    print(r['status'],r['packet']['ledger'])
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Own stdlib audit of fixed56 graphs and all32 mathematical anchor choices."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {'PROOF.md': '1c968fd62c53ea2eac14410188f02a59a50f91a816bdb289b9dcba667d296070',
        'check.py': '3a652cf3b12a174ef5c3c81dfa4db4980eedffe93dfa51bc27e19ba09e12a851',
        'SOURCE_PINS.json': '5c25c0bc52fe1abbd7b7713f1a360dcdeb15a4a9cec7a50dd1dbbeee348bf784',
        'raw/parent.json': '7823afb3c6c9b5e730e5571212a5398cb278647a5747cb3093cf2a2317a9adde',
        'raw/domain.json': '01d9fabc1a7d8bc9109eaab9b62cf17c448fe09172633c61bf04b1fc9cce92e1'}
GROUPS = [(574, [(576,577),(585,586),(593,594),(601,602)], [547,553,559,565]),
          (608, [(610,611),(619,620)], [572,578]),
          (626, [(628,629),(637,638)], [585,591]),
          (547, [(549,550),(562,563)], [526,537])]
def need(ok, why):
    if not ok: raise ValueError(why)
def load(path): return json.loads(path.read_bytes())
def digest(path): return sha256(path.read_bytes()).hexdigest()
def poly(terms):
    out = Counter()
    for c,m in terms: out[tuple(sorted(m))] += c
    return {m:c for m,c in out.items() if c}
def add(a,b,scale=1):
    out = Counter(a)
    for m,c in b.items(): out[m] += scale*c
    return {m:c for m,c in out.items() if c}
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    for n,h in PINS.items(): need(digest(HERE/n)==h,'whole reviewed core '+n)
    base=ROOT/'research/power3-square-frame-source-prototype'
    need(digest(base/'MANIFEST.json')=='f2ec7687ac03a9270c39ad839a0b1170499d186743037f9a2a30ff196795fed3','exact accepted62 seal')
    for n,h in load(base/'MANIFEST.json')['files'].items(): need(digest(base/n)==h,'whole accepted62 member '+n)
    need((HERE/'source/raw_builder.json').read_bytes()==(base/'source/raw_builder.json').read_bytes() and (HERE/'FRAME_POLICY.json').read_bytes()==(base/'FRAME_POLICY.json').read_bytes(),'body/frame bytes unchanged')
    raw=load(HERE/'source/raw_builder.json');rows=[poly(r['terms']) for r in raw['rows']]
    cuts=[]
    for N,pairs,starts in GROUPS:
        group=[]
        for (r,s),start in zip(pairs,starts):
            actual={}
            for j in range(start,start+3): actual=add(actual,rows[j])
            need(actual==poly([[1,[N]],[-1,[r]],[-1,[s]],[-1,[]]]),'each complete actual three-row sum')
            group.append(actual)
        cuts.append(group)
    choices=[];differences=0
    for selection in product(*(range(len(g[1])) for g in GROUPS)):
        anchors=[];merged=[]
        for k,((N,pairs,starts),anchor_index) in enumerate(zip(GROUPS,selection)):
            a,b=pairs[anchor_index];anchors.append([a,b])
            for j,(r,s) in enumerate(pairs):
                if j==anchor_index: continue
                need(add(cuts[k][anchor_index],cuts[k][j],-1)==poly([[1,[r]],[1,[s]],[-1,[a]],[-1,[b]]]),'universal anchor-minus-merged source ideal')
                differences+=1;merged.append([r,s])
        need(len(anchors)==4 and len(merged)==6,'six replacements for each mathematical selection')
        choices.append(dict(anchors=anchors,merged_pairs=merged))
    need(len(choices)==32 and differences==192,'all32 anchor choices with192 actual difference ideals')
    olddomain=load(base/'raw/domain.json');oldparent=load(base/'raw/parent.json');domain=load(HERE/'raw/domain.json');parent=load(HERE/'raw/parent.json')
    fixed_pairs=[pair for _,pairs,_ in GROUPS for pair in pairs[1:]]
    removed={v for pair in fixed_pairs for v in pair}
    expected=[g['predicate'] for g in olddomain['guards'] if not(g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] in removed)]
    expected += [dict(kind='shared_remainder_product',raw_variables=[r,s],terms=[[1,[r,s]]]) for r,s in fixed_pairs]
    canonical=lambda p: json.dumps(p,sort_keys=True,separators=(',',':'))
    need(Counter(map(canonical,expected))==Counter(canonical(g['predicate']) for g in domain['guards']),'exact fixed predicate multiset: only six scalar pairs exchanged')
    need(parent['domain']==oldparent['domain']=='unrestricted integers' and parent['variables'][:1268]==oldparent['variables'][:1268] and parent['residuals'][:1186]==oldparent['residuals'][:1186],'entire raw integer tuple stays fixed')
    graphs=0
    for full,guards in [(oldparent,olddomain['guards']),(parent,domain['guards'])]:
        for j,g in enumerate(guards):
            a,b,c=g['auxiliary'];want=add(poly(g['predicate']['terms']),poly([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
            need(poly(full['residuals'][1186+j]['terms'])==want,'each full integer Legendre guard graph, old and new')
            graphs+=1
    controls=0;zero_sum=0
    for a,b,r,s in product(range(5),range(5),range(-8,9),range(-8,9)):
        if r+s==a+b and r*s>=0:
            need(r>=0 and s>=0,'anchored product sign lemma diagnostic')
            controls+=1;zero_sum+=(r+s==0)
    need(zero_sum==1 and (-1)*(-1)>=0 and -1+-1<0 and -1+1==0 and (-1)*1<0,'zero endpoint and two necessary-premise counterexamples')
    need(all(c*(c+1)>=0 for c in range(-30,31)),'integer Legendre auxiliary boundary diagnostic')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),reviewed_core=PINS,base_sum_ideals=10,mathematical_anchor_choices=choices,source_difference_ideals=differences,actual_old_and_new_guard_graphs=graphs,fixed_new_predicates=len(domain['guards']),fixed_replaced_pairs=[list(p) for p in fixed_pairs],raw_body_and_frame_byte_unchanged=True,sign_controls=controls,zero_sum_controls=zero_sum,other_parents_or_profiles_materialized=False,author_code_or_optimizer_imported=False,whole_guarded_tuple_bijection_claimed=False,finite_controls_replace_unbounded_proof=False,audit_sha256=digest(Path(__file__)))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists(): need(args.output.read_text()==text,'refuse changed peer receipt overwrite')
    else: args.output.write_text(text)
    print(json.dumps(dict(status='PASS',anchor_choices=32,difference_ideals=192,full_guard_graphs=graphs),sort_keys=True))
if __name__=='__main__': main()

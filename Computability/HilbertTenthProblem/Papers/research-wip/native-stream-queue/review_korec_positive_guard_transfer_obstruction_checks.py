#!/usr/bin/env python3
"""Independent table algebra and metadata only; no saved DAG evaluation."""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

AUTHOR_PINS = {
    'md':'29a3e9c08648201d64a8a07ff4d081e93e4af4474834f9ef93134aea50c443cd',
    'py':'68c8895a1a2c0e72f41825ae7c41ff418dca16bd29d9e1dba6185a924a92ef86',
    'json':'f6c771b9a0b2e582375178df47c7618da26e8d15a720afd196793a229d7804ac',
}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

# Polynomials are tuples (coefficient of x, coefficient of A, constant).
def plus_constant(p, c):
    return (p[0], p[1], p[2] + c)

def at(p, x=1, a=1):
    return p[0]*x+p[1]*a+p[2]

def positive(p):
    return min(p[:2]) >= 0 and sum(p) > 0

def convert(p):
    return [p[2], p[1], p[0]]

def trajectory(table, initial, length, exceptional_time=None):
    state, values, rows = 0, list(initial), []
    for time in range(length):
        require(state in table, 'attempt to step halt')
        instruction = table[state]
        action, register = instruction[:2]
        selected = values[register]
        fake = time == exceptional_time
        if action == 'I':
            require(not fake, 'bad forced increment')
            target, kind, change = instruction[2], 'I', 1
        elif selected == (0, 0, 0) or fake:
            require(not fake or positive(selected), 'exception must be false')
            target, kind, change = instruction[3], 'Z', 0
        else:
            require(positive(selected), 'unresolved polynomial branch')
            target, kind = instruction[2], action
            change = -1 if action == 'D' else 0
        after = list(values)
        after[register] = plus_constant(after[register], change)
        require(all(min(p[:2]) >= 0 and sum(p) >= 0 for p in after), 'negative register')
        rows.append({'state':state, 'target':target, 'register':register,
                     'kind':kind, 'before':[convert(p) for p in values],
                     'after':[convert(p) for p in after], 'forced_false_zero':fake})
        state, values = target, after
    return state, values, rows

def pack(table, labels, rows, x):
    h = 16
    while h <= x+4:
        h *= 2
    D, duration = 2*h, len(rows)
    B = D**8
    P = B**duration
    J = (P-1)//(B-1)
    edges = []
    for state, ins in table.items():
        op, register = ins[:2]
        edges.append((state, ins[2], register, op))
        if op != 'I':
            edges.append((state, ins[3], register, 'Z'))
    selectors = [0]*len(edges)
    W = increment = decrement = zero_word = current = following = 0
    def value(p):
        return p[0]+p[1]+p[2]*x
    def word(v):
        return sum(value(p)*D**j for j,p in enumerate(v))
    def code(s):
        return 0 if s == 21 else labels[s]*D**table[s][1]
    # Reverse Horner packing uses independently transcribed scalar formulas.
    for row in reversed(rows):
        r, kind = row['register'], row['kind']
        before = word(row['before'])
        low = D**r if kind in ('D','T') else 0
        high = D**r if kind in ('I','T') else 0
        post = before-low
        require(post+high == word(row['after']), 'row transport')
        for j,p in enumerate(row['before']):
            z = value(p)-int(kind in ('D','T') and r == j)
            require(0 <= z <= h-3, 'strict digit margin')
        W = B*W+post
        increment = B*increment+high
        decrement = B*decrement+low
        zero_word = B*zero_word+(D**r if kind == 'Z' else 0)
        current = B*current+code(row['state'])
        following = B*following+code(row['target'])
        edge = edges.index((row['state'],row['target'],r,kind))
        selectors = [B*v+int(j == edge) for j,v in enumerate(selectors)]
    V = sum(D**j for j in range(8))
    R0 = (h-1)*V*J
    Rstar = (h-1)*(V*J-zero_word)
    final = word(rows[-1]['after'])
    require(B*(W+increment)+2*D+x*D**2 == W+decrement+P*final, 'whole counter transport')
    require(B*following+D == current, 'whole control transport')
    require(sum(selectors) == J and all(e & J == e for e in selectors), 'selectors')
    require(W & R0 == W and W-(W & Rstar) == D**5*B**85, 'exact failed zero cell')
    require(R0-W-2 > 0, 'positive range slack')
    H = sum(e*P**j for j,e in enumerate(selectors))+P**34*W
    M = J*sum(P**j for j in range(34))+P**34*R0
    Q = B*P**35
    require(0 <= H < M < Q and H & M == H, 'joined AND')
    q = 16*Q
    fields = [16*(Q-M)-15, 4, 16*(M-H)+2, 16*H+8]
    require(min(fields)>0 and sum(fields)==q-1, 'positive checksum')
    require(q & (q-1) == 0, 'dyadic q')
    r = sum(v*q**j for j,v in enumerate(fields))
    S = 5+(16*M+10)+q*((16*M+10)+q*(16*H+8))
    require(r==(q-1)*S and q<r<q**4, 'actual index identity/bounds')
    # The extension beta=2^(2r+1)/q-S is not materialized. Its exponent
    # is integral since log2(q)<r, and positivity follows from 2^(2r+1)>q*r.
    require(q.bit_length()-1 < r, 'integral canonical beta premise')
    summary = {'input':x,'h':h,'D':D,'duration':duration,'P_bits':P.bit_length(),
               'Q_bits':Q.bit_length(),'final_registers':[value(p) for p in rows[-1]['after']],
               'range_slack_positive':True,'exact_missing_cell_time':85,
               'all_retained_outer_and_AND_conditions':True}
    if x == 1:
        summary['saved_outer_compare'] = {
            'edge_hats':[hex(e+1) for e in selectors], 'W_hat':hex(W+1),
            'Y_hat':hex(final+1), 'global_slack':hex(R0-W-2)}
    return summary

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--author',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    author={}
    for suffix,pin in AUTHOR_PINS.items():
        path=args.author.with_suffix('.'+suffix)
        data=path.read_bytes()
        require(digest(data)==pin,'author pin '+suffix)
        author[suffix]={'sha256':pin,'bytes':len(data)}
    receipt=json.loads(args.author.with_suffix('.json').read_bytes())
    dependencies={}
    for name,record in receipt['dependencies'].items():
        data=(args.root/name).read_bytes()
        require(digest(data)==record['sha256'],'dependency '+name)
        dependencies[name]={'sha256':digest(data),'bytes':len(data)}
    table_text=(args.root/'korec_packed_counter_units.md').read_text()
    table, labels = {}, []
    for match in re.finditer(r'^\|(\d+)\|([IDT]) (\d+) ([\d ]+)\|(\d+)\|$',table_text,re.M):
        state,op,reg,targets,label=match.groups()
        table[int(state)]=(op,int(reg),*(int(t) for t in targets.split()))
        labels.append(int(label))
    require(list(table)==list(range(21)) and labels==receipt['labels'],'literal table/labels')
    require([list(v) for v in table.values()]==receipt['table'],'author table')
    z=(0,0,0);x=(1,0,0);a=(0,1,0)
    start=[z,(0,0,2),x,z,z,z,z,z]
    s,end,prefix=trajectory(table,start,59)
    require(s==0 and end==[(0,0,1),(0,0,2),x,z,z,z,(0,0,1),z],'prefix theorem')
    require(prefix==receipt['true_prefix59'],'saved prefix')
    cycle_start=[a,(0,0,2),x,z,z,z,(0,0,1),z]
    s,end,cycle=trajectory(table,cycle_start,30)
    require(s==0 and end==[plus_constant(a,1),*cycle_start[1:]],'affine cycle theorem')
    require(cycle==receipt['cycle30'],'saved cycle')
    s,end,forged=trajectory(table,start,88,85)
    require(s==21 and end==[(0,0,1),(0,0,2),plus_constant(x,-1),z,z,(0,0,1),(0,0,1),z],'forged endpoint')
    require(forged==receipt['forged_trace88'],'all saved forged rows')
    require(forged[85]['state']==10 and forged[85]['before'][5]==[1,0,0],'false guard')
    parent=json.loads((args.root/'korec_packed_repunit376.json').read_bytes())
    record=next(r for r in parent['records'] if r['form']=='units' and not r['program_radix'])
    source=record['source']
    removed=['counter_M_325','-','counter_digit_mask_92','Z_sum_146']
    require(source.count(removed)==1,'removed exact producer')
    require([r for r in source if 'counter_M_325' in r[2:]]==
            [['range_mask_93','*','counter_half_minus_one_84','counter_M_325']], 'sole removed consumer')
    new=[]
    for row in source:
        if row != removed:
            new.append([row[0],row[1],*['counter_digit_mask_92' if v=='counter_M_325' else v for v in row[2:]]])
    ports=record['parameters']+record['auxiliaries'];known=set(ports);edges={}
    for name,op,lhs,rhs in new:
        require(name not in known and op in ('+','-','*'),'row shape')
        require(all(type(v)is int or v in known for v in (lhs,rhs)),'acyclic metadata')
        known.add(name);edges[name]=[v for v in (lhs,rhs) if type(v)is str]
    live=set();stack=[record['output']]
    while stack:
        v=stack.pop()
        if v not in live:
            live.add(v);stack.extend(edges.get(v,[]))
    counts=Counter(r[1] for r in new)
    require(live==known and len(new)==375 and counts['*']==143,'full live 375 source')
    require(len(record['auxiliaries'])==50,'witness count')
    require([r[0] for r in new if 'Z_sum_146' in r[2:]]==['current_base_159'],'Z remains live')
    packs=[pack(table,labels,forged,x) for x in (1,2,7,16,31,255)]
    for key,value in packs[0].pop('saved_outer_compare').items():
        require(value==receipt['outer'][key],'independent pack '+key)
    result={'status':'PASS','schema':'independent-korec-guard-obstruction-review-v1',
            'helper_sha256':digest(Path(__file__).read_bytes()),'author':author,'dependencies':dependencies,
            'symbolic_checks':{'true_prefix':59,'unbounded_affine_cycle':30,'false_trace':88,
                               'exact_author_rows_matched':177,'input_domain':'all integers x>=1',
                               'false_zero_time':85,'false_register':5,'false_value':1},
            'source_metadata':{'parent_rows':len(source),'mutated_rows':len(new),'M':counts['*'],
                               'A':counts['+']+counts['-'],'positive_witnesses':50,'all_ports_rows_live':True,
                               'mutated_source_sha256':digest(json.dumps(new,separators=(',',':')).encode()),
                               'source_arrays_evaluated':False},'independent_formula_packs':packs,
            'scope':{'author_or_predecessor_execution_import':False,'native_Pell_tuple_materialized':False,
                     'native_extension':'proof-only inherited complete theorem; checked present interface',
                     'primary_universality_reaudit':False}}
    with args.output.open('x') as stream:
        json.dump(result,stream,sort_keys=True,indent=2);stream.write('\n')
    print('PASS: 177 symbolic transition records, 6 independent outer packs, structural 375-row mutation')

if __name__=='__main__':
    main()

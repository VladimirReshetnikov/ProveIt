#!/usr/bin/env python3
"""Canonicalize and check the exact 223-state binary machine; stdlib only."""
from pathlib import Path
import argparse, csv, hashlib, json, sys

ROOT = Path(__file__).resolve().parent
K_SHA = '5bcee335bc5cf45b6ebc6d1f97a10e3cc8aae2af303b82c5cc9ce506a4d22ed7'
SOURCE_SHA = 'fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f'
MAP_SHA = '8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151'

def need(condition, message):
    if not condition: raise ValueError(message)

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump(path, value): Path(path).write_text(json.dumps(value, indent=2) + '\n')

def parse(path):
    rows = {}; start = None
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):
            need(start is None, 'Duplicate start declaration'); start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,z = line.split(); q,b,w,z = map(int,(q,b,w,z))
            need((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'), 'Invalid row')
            rows[q,b] = (w, 1 if d=='R' else -1, z)
    states = {q for q,b in rows}
    need(start in states and set(rows)=={(q,b) for q in states for b in (0,1)}, 'Incomplete table')
    missing = {z for w,d,z in rows.values()}-states
    need(len(missing)==1, 'Expected one distinguished halt target')
    return rows,start,missing.pop(),states

def encode(table, start=0):
    return ('#! start %d\n'%start + ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
        for (q,b),(w,d,z) in sorted(table.items()))).encode()

def canonical(table, start, halt):
    order = [start]; seen = {start}
    for q in order:
        for b in (0,1):
            z = table[q,b][2]
            if z!=halt and z not in seen: seen.add(z); order.append(z)
    need(seen=={q for q,b in table}, 'Unreachable declared state')
    labels = {q:i for i,q in enumerate(order)}; labels[halt] = len(order)
    return {(labels[q],b):(w,d,labels[z]) for (q,b),(w,d,z) in table.items()},labels

def source_metrics(path):
    need(sha(path)==SOURCE_SHA, 'Source hash differs')
    sites = json.loads(Path(path).read_text()); leaves={}; prefixes=set()
    for pc,op,arg in sites:
        need(isinstance(pc,str) and pc and set(pc)<={'0','1'} and pc not in leaves, 'Invalid source address')
        need(op in ('CI','CD','CB','CC','CH'), 'Unknown primitive')
        if op in ('CI','CD'): need(type(arg) is int and 0<=arg<9, 'Invalid register')
        elif op in ('CB','CC'): need(type(arg) is int and arg>=1, 'Invalid jump depth')
        else: need(arg is None, 'Invalid halt argument')
        leaves[pc]=(op,arg); prefixes.update(pc[:i] for i in range(len(pc)))
    need(not set(leaves)&prefixes and len(prefixes)==len(leaves)-1, 'Incomplete prefix tree')
    need(all(p+b in leaves or p+b in prefixes for p in prefixes for b in ('0','1')), 'Missing source branch')
    nodes=set()
    def tree(p):
        n=leaves[p] if p in leaves else (tree(p+'0'),tree(p+'1'))
        nodes.add(n); return n
    tree('')
    metrics=dict(instructions=len(sites),dag_nodes=len(nodes),maximum_depth=max(map(len,leaves)),
        maximum_zero_run=max(len(s) for p in leaves for s in p.split('1')),
        guarded_cases=sum(2 if op=='CD' else 1 for pc,op,arg in sites))
    need(metrics==dict(instructions=4581,dag_nodes=209,maximum_depth=38,maximum_zero_run=6,guarded_cases=5956), 'Source census differs')
    return sites,metrics

def bootstrap(table):
    q=0;head=0;ones=set()
    for tick in range(409835):
        need(q!=254, 'Premature halt during initialization')
        b=int(head in ones);w,d,q=table[q,b]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    need(q==84 and head==-5, 'Blank bootstrap endpoint differs')
    need(min(ones)==head-1, 'Nonblank tape to the left of the marker')
    # At this checked dispatcher the address is empty. The first right-hand 1
    # marks the end of the zero gap; B(v)=0 1^(v+1) encodes each register.
    header=min(x for x in ones if x>=head); pos=header+1; values=[]
    while pos<=max(ones):
        need(pos not in ones and pos+1 in ones, 'Malformed unary register block')
        pos+=1;start=pos
        while pos in ones:pos+=1
        values.append(pos-start-1)
    need(pos==max(ones)+1 and len(values)==176, 'Wrong register/spare count')
    physical=[0]*9
    logical=[3,0,0,0,3,0,0,0,0]
    permutation=[6,2,0,4,3,7,8,5,1]
    for i,j in enumerate(permutation):physical[j]=logical[i]
    need(values[:9]==physical and values[9:]==[1]*167, 'Wrong initialized registers')
    need(header-head==181 and len(ones)==351, 'Wrong initialized gap or support')
    return dict(status='EXACT_BLANK_BOOTSTRAP_PASS',steps=409835,k_state=q,head=head,
        logical_registers=logical,physical_register_map=permutation,zero_gap=181,extra_gap=117,
        spare_count=167,spare_values=1,one_cells=sorted(ones),one_cell_count=len(ones),
        all_unlisted_cells=0,scope='Exact complete tape after the first 409835 blank-start transitions.')

def build(output):
    need(__debug__ and not sys.flags.optimize, 'Assertions must remain enabled')
    output.mkdir(parents=True,exist_ok=True)
    source=ROOT/'results/sites.json'; _,metrics=source_metrics(source)
    ktpath=ROOT/'folds/candidate223.k.tm'; need(sha(ktpath)==K_SHA, 'K table hash differs')
    kt,start,halt,states=parse(ktpath)
    need((start,halt,len(states),len(kt))==(0,254,223,446), 'K table census differs')
    nt,labels=canonical(kt,start,halt)
    need(set(labels.values())==set(range(224)), 'Canonical labels differ')
    (output/'candidate223.tm').write_bytes(encode(nt))
    (output/'candidate223.k.tm').write_bytes(encode(kt))
    mapfile=ROOT/'vendor/legacy_state_map.json';need(sha(mapfile)==MAP_SHA, 'Legacy map differs')
    old=json.loads(mapfile.read_text()); legacy={int(q):v for q,v in old['k230_to_old'].items()};legacy[254]=254
    for q in labels:
        if q not in legacy:legacy[q]=q+1000
    need(len({legacy[q] for q in labels})==len(labels), 'Legacy labels collide')
    lt={(legacy[q],b):(w,d,legacy[z]) for (q,b),(w,d,z) in kt.items()}
    (output/'candidate223.legacy.tm').write_bytes(encode(lt,legacy[0]))
    dump(output/'state_map.json',dict(canonical_order='Breadth first from start, visit read0 before read1',
        k_to_canonical=labels,k_to_legacy={q:legacy[q] for q in labels},
        canonical_start=0,canonical_halt=223,k_start=0,k_halt=254,legacy_start=95,legacy_dispatcher=96))
    with (output/'candidate223.csv').open('w',newline='') as stream:
        writer=csv.writer(stream);writer.writerow(['state','read','write','move','next'])
        writer.writerows((q,b,w,'R' if d==1 else 'L',z) for (q,b),(w,d,z) in sorted(nt.items()))
    boot=bootstrap(kt);boot['canonical_state']=labels[84];dump(output/'bootstrap223.json',boot)
    hashes={n:sha(output/n) for n in ['candidate223.tm','candidate223.k.tm','candidate223.legacy.tm','candidate223.csv','state_map.json','bootstrap223.json']}
    receipt=dict(status='EXACT_BINARY_MACHINE_BUILD_PASS',working_states=223,alphabet=[0,1],rows=446,
        start=0,halt=223,initial_tape='all zero',initial_head=0,all_states_graph_reachable=True,
        source_sha256=SOURCE_SHA,source_metrics=metrics,output_sha256=hashes,
        bootstrap=dict(steps=409835,canonical_dispatcher=labels[84],head=-5,one_cells=351),
        scope='Exact table syntax, graph census, relabeling, full blank startup, and source census; logical and universal runtime checks are separate.')
    dump(output/'build223.json',receipt);return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,default=ROOT/'results');args=ap.parse_args()
    print(json.dumps(build(args.output_dir),indent=2))

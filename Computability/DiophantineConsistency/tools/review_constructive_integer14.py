#!/usr/bin/env python3
"""Inert full-source, norm-tail and graph review of the integer14 component.

Imports only an earlier independently written polynomial oracle, never any
delivered builder or verifier. Full author replays are attached separately.
"""
from collections import Counter
import argparse
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ARCHIVE = REPO/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
PIN = '37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0'
PREFIX = 'ConZFC_Constructive_Reductions_2026-10-23/integer14/'
PRIOR = ROOT/'candidates/interpolation-shared-norms/source/inherited/root_fusion'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def norm_tail(packet, oracle):
    named, nodes = packet['named_registers'], packet['nodes']
    x, a, b, d, c, delta = [oracle.variable(i) for i in range(6)]
    env = {i:oracle.Poly(row[1]) for i,row in enumerate(nodes) if row[0]=='integer'}
    for name,value in zip(('center','A','B','Dm','Cn','delta'), (x,a,b,d,c,delta)):
        need(named[name] not in env, 'distinct nonconstant cut ports')
        env[named[name]] = value
    start = max(named[n] for n in ('center','A','B','Dm','Cn'))+1
    for i in range(start, named['N']+1):
        row = nodes[i]
        if row[0]=='integer':
            continue
        need(row[0] in ('add','sub','mul') and row[1] in env and row[2] in env,
             'norm tail has no other free input')
        u,v = env[row[1]],env[row[2]]
        env[i] = u+v if row[0]=='add' else u-v if row[0]=='sub' else u*v
    # Laurent monomials are used only inside this exact oracle; delta^8
    # clears every negative exponent. No division appears in the circuit.
    fraction = oracle.Poly({(0,0,0,0,1,-1):1})
    want = delta**8*oracle.norm_oracle(x, [a,b,d,fraction])
    need(all(all(e>=0 for e in m) for m in want.t), 'complete denominator clearing')
    need(env[named['N']].t == want.t and len(want.t)==495,
         'whole literal tail equals all495 cleared norm coefficients')
    return dict(complete_norm_coefficients=len(want.t),
                all_six_cut_ports_bound=True, other_free_tail_inputs=0)


def graph(packet):
    nodes=packet['nodes'];live=set();todo=[packet['output']]
    for i,row in enumerate(nodes):
        need(row[0] in ('integer','variable','coefficient','add','sub','mul'), 'polynomial nodes')
        if row[0] in ('add','sub','mul'):
            need(all(type(j) is int and 0<=j<i for j in row[1:]), 'topological binary gate')
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    need(live==set(range(len(nodes))), 'all nodes live')
    variables=[r[1] for r in nodes if r[0]=='variable']
    need(variables==packet['variables'] and len(set(variables))==14, 'all14 live integer unknowns')
    need(packet['domain']=='unrestricted integers', 'integer domain')
    ports=[r[1] for r in nodes if r[0]=='coefficient']
    need(len(ports)==6 and set(ports)=={'beta','K0','MC','MF','cone_A','cone_B'},
         'exact complete live coefficient ports')
    counts=Counter(r[0] for r in nodes if r[0] in ('add','sub','mul'))
    need(dict(counts)==packet['operation_counts'] and sum(counts.values())==packet['operations'],
         'actual operation census')
    return dict(variables=14,operations=sum(counts.values()),operation_counts=dict(counts),
                exact_degree=packet['exact_degree'],all_nodes_live=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--replay-receipt',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    raw=ARCHIVE.read_bytes();need(digest(raw)==PIN,'complete immutable archive')
    oracle_path=ROOT/'reviews/ten-positive-scaled-norm-peer.py'
    need(digest(oracle_path.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83',
         'independent sparse-ring oracle pin')
    spec=importlib.util.spec_from_file_location('integer14_independent_norm_oracle',oracle_path)
    oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
    with zipfile.ZipFile(ARCHIVE) as z:
        files={n[len(PREFIX):]:z.read(n) for n in z.namelist()
               if n.startswith(PREFIX) and not n.endswith('/')}
    need(len(files)==104,'exact component inventory')
    inherited=[]
    for name,blob in files.items():
        if name.startswith('upstream/'):
            rel=name[len('upstream/'):]
            need((PRIOR/rel).read_bytes()==blob,'whole previously reviewed parent '+rel)
            inherited.append(rel)
    need(len(inherited)==92,'whole copied parent subtree')
    binding=json.loads(files['upstream/coefficients/BINDING.json'])
    payloads={}
    for name,record in binding['payloads'].items():
        data=gzip.decompress(files['upstream/coefficients/'+record['file']])
        need(digest(data)==record['raw_sha256'],'whole actual payload '+name)
        payloads[name]=dict(raw_sha256=digest(data),raw_bytes=len(data))
    need(len(payloads)==6,'complete six-port tuple')
    replay=json.loads(args.replay_receipt.read_bytes())
    need(replay['status']=='PASS' and len(replay['equations'])==2,'complete scoped author replay')
    results={}
    for name,operations,degree in [('crt14_degree540',160,540),('crt14_degree568',147,568)]:
        blob=files[name+'.json'];p=json.loads(blob)
        need(p['operations']==operations and p['exact_degree']==degree,'declared complete endpoint')
        rec=next(r for r in replay['equations'] if r['name']==name)
        need(rec['sha256']==digest(blob),'fresh replay matches entire literal graph')
        results[name]=dict(**graph(p),**norm_tail(p,oracle),sha256=digest(blob))
    result=dict(status='PASS',python_optimization=sys.flags.optimize,archive_sha256=PIN,
                scoped_component_member_sha256={n:digest(b) for n,b in sorted(files.items())},
                whole_previously_reviewed_parent_files=len(inherited),whole_payloads=payloads,
                equations=results,full_scoped_author_replay=replay,
                scope='Integer14 only. Generic495-coefficient norms and graph identities are exact; '
                      'unbounded semantics and degrees use the separate ordinary proof review. '
                      'No Lean or new internal-ZFC derivation.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',parent_files=len(inherited),equations=results),indent=2))


if __name__=='__main__':
    main()

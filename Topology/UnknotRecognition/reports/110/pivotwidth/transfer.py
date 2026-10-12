"""Checked fixed-width path templates and max-plus powers.

None is minus infinity. Templates have named input/output interfaces. Each
positive edge must involve a vertex fresh within its template, so repeated
copies never silently duplicate an input-input occurrence. This is an abstract
incidence-graph contract, not a geometric source-chart validator.
"""
from __future__ import annotations
from itertools import permutations
from copy import deepcopy
from .core import Edge, Value, introduce, forget, introduce_edge


def states(names):
    return [(tuple(p), mask) for p in permutations(sorted(names))
            for mask in range(1 << len(names))]


def inspect_program(program):
    inputs = program.get('inputs', [])
    live, data, labels = {}, {}, {}
    serial = 0
    def add(name, side, weight):
        nonlocal serial
        if not isinstance(name, str) or not name or name in labels:
            raise ValueError('vertex names must be unique nonempty strings within a template')
        if side not in ('R','C') or type(weight) is not int or weight < 0 or (side == 'C' and weight):
            raise ValueError('invalid vertex type or weight')
        live[name] = serial
        labels[name] = serial
        data[serial] = (side, weight)
        serial += 1
    for v in inputs:
        add(v['name'], v['side'], v.get('weight', 0))
    input_ids = set(live.values())
    initial = dict(live)
    events, seen = [], set()
    peak = len(live)
    fresh_weight = 0
    for cmd in program.get('commands', []):
        op = cmd['op']
        if op == 'introduce':
            add(cmd['name'], cmd['side'], cmd.get('weight', 0))
            v = live[cmd['name']]
            events.append(('introduce', v))
            fresh_weight += data[v][1]
            peak = max(peak, len(live))
        elif op == 'forget':
            if cmd['name'] not in live:
                raise ValueError('forgotten vertex is not live')
            events.append(('forget', live.pop(cmd['name'])))
        elif op == 'edge':
            if cmd['row'] not in live or cmd['column'] not in live:
                raise ValueError('edge endpoint not live')
            r, c = live[cmd['row']], live[cmd['column']]
            count = cmd['count']
            allowed = cmd.get('allowed', count == 1)
            if data[r][0] != 'R' or data[c][0] != 'C':
                raise ValueError('edge must run from a row to a column')
            if type(count) is not int or count <= 0 or type(allowed) is not bool or (allowed and count != 1):
                raise ValueError('invalid count or allowed-pivot flag')
            if (r,c) in seen or (r in input_ids and c in input_ids):
                raise ValueError('duplicate edge or non-fresh interface edge')
            seen.add((r,c))
            events.append(('edge', Edge(r,c,count,allowed), data[r][1]))
        else:
            raise ValueError('unsupported template command')
    outputs = program.get('outputs', {})
    if set(outputs) != set(live) or len(set(outputs.values())) != len(live):
        raise ValueError('output map must bijectively rename the live interface')
    if any(not isinstance(v,str) or not v for v in outputs.values()):
        raise ValueError('invalid output label')
    output_ids = {outputs[name]: ident for name,ident in live.items()}
    input_types = {name:data[i] for name,i in initial.items()}
    output_types = {name:data[i] for name,i in output_ids.items()}
    return {'events':events, 'initial':initial, 'final':output_ids,
            'input_types':input_types, 'output_types':output_types,
            'max_bag':peak, 'fresh_weight':fresh_weight}


def compile_transfer(program):
    info = inspect_program(program)
    ss, tt = states(info['initial']), states(info['final'])
    index = {s:i for i,s in enumerate(tt)}
    output_name = {v:name for name,v in info['final'].items()}
    matrix = [[None]*len(tt) for _ in ss]
    peak = 0
    for k,(names,mask) in enumerate(ss):
        order = tuple(info['initial'][name] for name in names)
        table = {(order,mask):Value(0,None)}
        for event in info['events']:
            if event[0] == 'introduce':
                table = introduce(table,event[1])
            elif event[0] == 'forget':
                table = forget(table,event[1])
            else:
                table = introduce_edge(table,event[1],event[2])
            peak = max(peak,len(table))
        for (order,mask), value in table.items():
            j = index[(tuple(output_name[v] for v in order),mask)]
            matrix[k][j] = value.score
    return {'matrix':matrix, 'input_states':ss, 'output_states':tt,
            'input_types':info['input_types'], 'output_types':info['output_types'],
            'max_bag':info['max_bag'], 'fresh_weight':info['fresh_weight'],
            'peak_states_per_input':peak}


def product(a,b):
    if not a or not b or len(a[0]) != len(b):
        raise ValueError('incompatible transfer dimensions')
    rows,inner,cols = len(a),len(b),len(b[0])
    if any(len(row)!=inner for row in a) or any(len(row)!=cols for row in b):
        raise ValueError('ragged transfer')
    out = [[None]*cols for _ in range(rows)]
    witness = [[None]*cols for _ in range(rows)]
    for i in range(rows):
        for k in range(inner):
            if a[i][k] is None:
                continue
            for j in range(cols):
                if b[k][j] is not None:
                    val = a[i][k]+b[k][j]
                    if out[i][j] is None or val > out[i][j]:
                        out[i][j], witness[i][j] = val,k
    return out,witness


def power_certificate(program, exponent):
    if type(exponent) is not int or exponent < 0:
        raise ValueError('exponent must be a nonnegative integer')
    transfer = compile_transfer(program)
    if transfer['input_types'] != transfer['output_types']:
        raise ValueError('power requires the same typed input/output interface')
    n = len(transfer['matrix'])
    nodes = [ {'kind':'identity', 'length':0,
               'matrix':[[0 if i==j else None for j in range(n)] for i in range(n)]},
              {'kind':'template', 'length':1, 'matrix':transfer['matrix']} ]
    def compose(x,y):
        table,mid = product(nodes[x]['matrix'], nodes[y]['matrix'])
        nodes.append({'kind':'product','left':x,'right':y,
                      'length':nodes[x]['length']+nodes[y]['length'],
                      'matrix':table,'middle':mid})
        return len(nodes)-1
    answer,base,e = 0,1,exponent
    while e:
        if e & 1:
            answer = compose(answer,base)
        e >>= 1
        if e:
            base = compose(base,base)
    ss = transfer['input_states']
    candidates = [x for i,s in enumerate(ss) if s[1] == 0
                  for x in nodes[answer]['matrix'][i] if x is not None]
    optimum = max(candidates)
    # Each interface row is one initial actual row; each copy contributes fresh rows.
    total_weight = sum(t[1] for t in transfer['input_types'].values()) + exponent*transfer['fresh_weight']
    return {'schema':'ordered-pivot-power-v1','program':deepcopy(program),
            'exponent':exponent, 'nodes':nodes, 'root':answer,
            'retained_weight':optimum,'deferred_weight':total_weight-optimum,
            'stats':{'interface_states':n,'max_bag':transfer['max_bag'],
                     'proof_nodes':len(nodes),
                     'peak_states_per_input':transfer['peak_states_per_input']}}


def expand(program, exponent):
    """Small-test expansion only. Repetition makes fresh internal vertex identities."""
    info = inspect_program(program)
    if info['input_types'] != info['output_types'] or type(exponent) is not int or exponent < 0:
        raise ValueError('invalid power template')
    all_data, edges, interface = {},[],{}
    next_id = 0
    for name,typ in sorted(info['input_types'].items()):
        interface[name]=next_id;all_data[next_id]=typ;next_id+=1
    for _ in range(exponent):
        live=dict(interface)
        for cmd in program['commands']:
            if cmd['op']=='introduce':
                live[cmd['name']]=next_id
                all_data[next_id]=(cmd['side'],cmd.get('weight',0));next_id+=1
            elif cmd['op']=='forget':
                del live[cmd['name']]
            else:
                edges.append((live[cmd['row']],live[cmd['column']],cmd['count'],
                              cmd.get('allowed',cmd['count']==1)))
        interface={new:live[old] for old,new in program['outputs'].items()}
    rr=[v for v,t in all_data.items() if t[0]=='R'];cc=[v for v,t in all_data.items() if t[0]=='C']
    ri={v:i for i,v in enumerate(rr)};ci={v:i for i,v in enumerate(cc)}
    a=[[0]*len(cc) for _ in rr];forbidden=[]
    for r,c,x,allowed in edges:
        assert a[ri[r]][ci[c]]==0
        a[ri[r]][ci[c]]=x
        if x==1 and not allowed:forbidden.append((ri[r],ci[c]))
    return {'matrix':a,'columns':len(cc),'weights':[all_data[r][1] for r in rr],
            'forbidden_pivots':forbidden}

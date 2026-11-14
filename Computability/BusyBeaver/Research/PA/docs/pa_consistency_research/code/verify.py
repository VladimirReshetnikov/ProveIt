#!/usr/bin/env python3
"""Independent finite checks for the PA consistency-machine research packet.

Python 3.10+, standard library only. No optimizer, network, or saved success
flag is needed. These checks do not establish an end-to-end PA theorem or a
new physical machine with fewer than 196 states.
"""
from pathlib import Path
from collections import deque, Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def require(test, message):
    if not test:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def leaf(t):
    return isinstance(t[0], str)

def lean_tree(path):
    raw = path.read_text()
    require(digest(path) == '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872',
            'Pinned original Program.lean changed')
    env = {}
    tokens = re.compile(r'\.leaf \(\.(?:inc|dec|breakTo|continueTo) \d+\)|\.leaf \(\.halt\)|[A-Za-z]\w*')
    names = dict(inc='CI', dec='CD', breakTo='CB', continueTo='CC', halt='CH')
    for name, body in re.findall(r'^def (\w+) : Tree := \.node (.+)$', raw, re.M):
        parts = tokens.findall(body)
        require(len(parts) == 2, 'Lean constructor shape')
        def term(x):
            if not x.startswith('.leaf'):
                return env[x]
            m = re.fullmatch(r'\.leaf \(\.(\w+)(?: (\d+))?\)', x)
            return names[m[1]], int(m[2]) if m[2] else None
        env[name] = tuple(map(term, parts))
    root = re.findall(r'^def trie : Tree := (\w+)\s*$', raw, re.M)
    require(root == ['node172'], 'Original root name')
    return env[root[0]]

def flatten(t, prefix=''):
    if leaf(t):
        return [[prefix, *t]]
    return flatten(t[0], prefix+'0') + flatten(t[1], prefix+'1')

def from_rows(rows):
    trie = {}
    for path, op, arg in rows:
        require(path and set(path) <= {'0','1'}, 'Binary source path')
        require(op in ('CI','CD','CB','CC','CH'), 'Source opcode')
        require((op == 'CH' and arg is None) or
                (type(arg) is int and arg >= 0), 'Source operand')
        if op in ('CI','CD'):
            require(arg < 9, 'Register range')
        if op in ('CB','CC'):
            require(arg > 0, 'Positive jump depth')
        here = trie
        for b in path:
            require('leaf' not in here, 'Prefix overlap')
            here = here.setdefault(b, {})
        require(not here, 'Duplicate or overlapping path')
        here['leaf'] = (op,arg)
    def build(d):
        if 'leaf' in d:
            require(len(d) == 1, 'Leaf overlap')
            return d['leaf']
        require(set(d) == {'0','1'}, 'Full binary tree')
        return build(d['0']), build(d['1'])
    answer = build(trie)
    require(flatten(answer) == rows, 'Canonical leaf order')
    return answer

def statistics(t):
    seen = set()
    def visit(n):
        if leaf(n) or n in seen:
            return
        seen.add(n)
        visit(n[0]); visit(n[1])
    visit(t)
    rows = flatten(t)
    return dict(internal_nodes=len(seen), instructions=len(rows),
                maximum_depth=max(len(r[0]) for r in rows),
                maximum_zero_run=max(len(z) for r in rows for z in r[0].split('1')))

def graph_by_intervals(t):
    """Resolve jumps by ancestor intervals in the ordered leaf tree."""
    rows = flatten(t)
    intervals = {}
    for i,(p,_,_) in enumerate(rows):
        for j in range(len(p)+1):
            u = p[:j]
            if u not in intervals:
                intervals[u] = [i,i+1]
            else:
                intervals[u][1] = i+1
    def cut(p, b, k):
        hits = [i for i,c in enumerate(p) if c == b]
        require(len(hits) >= k, 'A jump escapes the root')
        return p[:hits[-k]]
    result = []
    for i,(p,op,arg) in enumerate(rows):
        after = i+1
        if op == 'CI':
            row = ['inc',arg,after]
        elif op == 'CD':
            row = ['dec',arg,intervals[cut(p,'0',1)][1],after]
        elif op == 'CB':
            row = ['jump',intervals[cut(p,'0',arg)][1]]
        elif op == 'CC':
            row = ['jump',intervals[cut(p,'1',arg)][0]]
        else:
            row = ['halt']
        targets = row[2:] if op in ('CI','CD') else row[1:]
        require(all(0 <= x < len(rows) for x in targets), 'Root exit in ordinal graph')
        result.append(row)
    return result

def graph_by_bits(t):
    """Independently resolve by binary increment, cut, and zero extension."""
    rows = flatten(t); index = {p:i for i,(p,_,_) in enumerate(rows)}
    def locate(p):
        n = t; j = 0; used = ''
        while not leaf(n):
            bit = p[j] if j < len(p) else '0'
            n = n[int(bit)]; used += bit; j += 1
        require('1' not in p[j:], 'Nonzero suffix after selected instruction')
        return index[used]
    def cut(p,b,k):
        while p:
            end,p = p[-1],p[:-1]
            if end == b:
                k -= 1
                if k == 0:
                    return p
        raise ValueError('Unresolved source jump')
    def successor(p):
        require('0' in p, 'Source exits root')
        j = p.rfind('0')
        return locate(p[:j]+'1'+'0'*(len(p)-j-1))
    result=[]
    for p,op,arg in rows:
        if op == 'CI': row=['inc',arg,successor(p)]
        elif op == 'CD': row=['dec',arg,successor(cut(p,'0',1)),successor(p)]
        elif op == 'CB': row=['jump',successor(cut(p,'0',arg))]
        elif op == 'CC': row=['jump',locate(cut(p,'1',arg))]
        else: row=['halt']
        result.append(row)
    return result

def table(path):
    rows={}; start=0
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start=int(line[9:]); continue
        if not line or line.startswith('#'): continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'), 'Bad table row')
        rows[q,b]=(w,d,z)
    working={q for q,b in rows}
    require(set(rows)=={(q,b) for q in working for b in (0,1)}, 'Incomplete binary table')
    terminals={z for w,d,z in rows.values()}-working
    require(len(terminals)==1 and start in working, 'Start/halt convention')
    return rows,start,next(iter(terminals))

def canonical(rows,start,halt):
    number={start:0}; todo=[start]; out=[]
    for q in todo:
        acts=[]
        for bit in (0,1):
            w,d,z=rows[q,bit]
            if z==halt: nz='H'
            else:
                if z not in number: number[z]=len(number);todo.append(z)
                nz=number[z]
            acts.append([w,d,nz])
        out.append(acts)
    require(len(number)==len(rows)//2, 'Graph-unreachable working state')
    return json.dumps(out,separators=(',',':'))

def main():
    old=lean_tree(ROOT/'data/pa196_program.lean')
    old_rows=json.loads((ROOT/'data/source196.json').read_text())
    require(flatten(old)==old_rows, 'Lean/JSON original disagreement')
    new=from_rows(json.loads((ROOT/'data/source158.json').read_text()))
    dag=json.loads((ROOT/'data/source158.dag.json').read_text());expanded=[]
    for i,node in enumerate(dag['nodes']):
        require(node['id']==i, 'DAG postorder ID')
        def child(x):
            if type(x) is int:
                require(0 <= x < i, 'DAG forward/cyclic edge')
                return expanded[x]
            require(type(x) is list and len(x)==2, 'DAG leaf')
            return tuple(x)
        expanded.append((child(node['left']),child(node['right'])))
    require(len(expanded)==158 and dag['root']==157 and expanded[157]==new, 'DAG/source mismatch')
    a,b=statistics(old),statistics(new)
    require(a==dict(internal_nodes=159,instructions=3812,maximum_depth=38,maximum_zero_run=6), 'Original census')
    require(b==dict(internal_nodes=158,instructions=3812,maximum_depth=37,maximum_zero_run=6), 'New source census')
    g=graph_by_intervals(old)
    require(g==graph_by_bits(old)==graph_by_intervals(new)==graph_by_bits(new), 'Source CFG changed')
    require([x[1:] for x in flatten(old)]==[x[1:] for x in flatten(new)], 'Source primitive word changed')
    machine_counts={}
    for file,expected in [('pa196.tm',196),('pa209.tm',209)]:
        rows,start,halt=table(ROOT/'data'/file)
        require(len(rows)==2*expected, 'Machine census '+file)
        canonical(rows,start,halt)
        machine_counts[file]=dict(working_states=expected,rows=len(rows),start=start,halt=halt,sha256=digest(ROOT/'data'/file))
    require(machine_counts['pa196.tm']['sha256']=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8','PA196 identity')
    inv=json.loads((ROOT/'data/u208_inventory.json').read_text());classes=Counter();functions=set();raw=set();items=[]
    for item in inv['outputs']:
        path=ROOT/item['package_file'];rows,start,halt=table(path)
        require(len(rows)==416 and digest(path)==item['native_bytes_sha256'],'U208 identity/census')
        key=canonical(rows,start,halt);classes[key]+=1
        functions.add(tuple(sorted(rows.items())));raw.add(path.read_bytes())
        items.append(dict(name=item['name'],class_fingerprint=hashlib.sha256(key.encode()).hexdigest()))
    require(len(classes)==2 and sorted(classes.values())==[4,5] and len(functions)==6 and len(raw)==7,'U208 classes')
    # Baseline blank startup is finite evidence, not evidence for infinite nonhalting.
    rows,start,halt=table(ROOT/'data/pa196.tm');q=start;h=0;ones=set()
    for step in range(58154):
        require(q!=halt,'PA196 halted during checked startup')
        w,d,q=rows[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    bits=[1]+[0]*47+[1]
    for v in physical:bits.extend([0]+[1]*(v+1))
    expected={-1}|{i for i,v in enumerate(bits) if v}
    require(q==75 and {i-h for i in ones}==expected, 'PA196 complete startup tape mismatch')
    result=dict(status='FINITE_CHECKS_PASS',source_original=a,source_new=b,
                source_cfg_rows_checked=len(g),two_independent_resolvers=True,
                source_seed_ordinal=25,source_seed_registers=[2,0,0,0,0,0,0,0,0],
                source158_sha256=digest(ROOT/'data/source158.json'),
                machines=machine_counts,u208_classes=len(classes),u208_class_sizes=sorted(classes.values()),
                u208_native_functions=len(functions),u208_byte_variants=len(raw),u208_outputs=items,
                startup=dict(steps=58154,state=q,absolute_head=h,relative_header_gap=48),
                scope='Finite source/graph/startup checks; no sub-196 machine is certified.')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

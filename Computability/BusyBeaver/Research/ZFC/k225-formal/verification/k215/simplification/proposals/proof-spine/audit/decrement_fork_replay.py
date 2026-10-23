#!/usr/bin/env python3
"""Independent, fail-closed finite audit of K215 decrement prefix factoring.

This file was written for this audit. It imports only Python's standard library,
parses repository files as inert data, and does not execute repository programs.
Run from anywhere: python3 audit/decrement_fork_replay.py
No Lean/Rocq compilation, proof certificate, or wall-clock benchmark is claimed.
"""
from pathlib import Path
import collections
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'rocq/inputs'
SUPPORT = ROOT / 'audit/decrement_fork_inputs'
CURRENT = ROOT / 'review/current/Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
REVISION = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
PIN = {
    'KRuntimeCore.lean': '6383b6326f694ff3e20e7961e2518176e6664232',
    'KHome.lean': '95e9cd89bf61a2b9316ba1e450bd601703273d47',
    'KHomeReady.lean': 'f62e017eef890a35bd1d2638fa7044ee2416fd52',
    'KSim.lean': '3dd6a53a8e5777c6f80fb82083ce0037d7566382',
    'KTable215.lean': '2f8cec37f4b99420ce030308edbb57d1de1de8f1',
    'K215Decoder.lean': 'c3ed666652f33ae3ebc476d7e4cd05639d04352f',
    'KDecoderPrefix215.lean': '637e47d00c0ae607c344cce86213c0bc4f9fd071',
    'KSource215Program.lean': '378b6bc9375f2abfe565c95c963263b6250a7f30',
    'KTableCore.lean': '5a96ff3a700726986a6deb39f06266da8bffef24',
    'RegisterPath.lean': '6435281a905f512c875ac5e9f255ba96830ab732',
    'FramedWindow.lean': '6307a63adaacc2e7273c65d9d7221da023ab034c',
    'Runtime230Core.v': '5aff688453852ebdcdba8dc8819180c120b6c519',
    'Interpreter230Sites.v': '4e8a4f32561cfaeb39222158b5322aa0d8a4a2af',
    'Interpreter230Check.v': '05cadc9d40b45f5b00462ff221653399ac31d1e9',
    'Table230.v': '30fcc014354a0a59cf851503cd7eea92acb010dd',
    'TM230.v': 'bd64fa01d7b4120238e253793f5feb39dc1ffe1b',
    'Prog215.v': 'c74df29d0e0d3c9c91d46b3cda73c3563b7f2058',
}

def check(ok, explanation):
    if not ok:
        raise RuntimeError(explanation)


def read_pinned():
    texts, ledger = {}, {}
    for name, expected in PIN.items():
        p = INPUT / name
        if not p.exists():
            p = SUPPORT / name
        if not p.exists():
            p = CURRENT / name
        data = p.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        check(actual == expected, 'Source pin mismatch: ' + name)
        texts[name] = data.decode()
        ledger[name] = {'path': str(p.relative_to(ROOT)), 'git_blob': actual,
                        'sha256': hashlib.sha256(data).hexdigest()}
    return texts, ledger


def literal_array(text, name):
    m = re.search(r'def ' + name + r' : Array \w+ := #\[\n(.*?)\n\]', text, re.S)
    check(m is not None, 'Array missing: ' + name)
    return [s.strip().removesuffix(',') for s in m.group(1).splitlines() if s.strip()]


def bools(s):
    check(re.fullmatch(r'(?:true|false)(?:, (?:true|false))*', s) is not None, 'Bad bits')
    return tuple(x == 'true' for x in s.split(', '))


def formal_table(text):
    body = text.split('def table215 : List (Row × Row) := [\n', 1)[1].split(']', 1)[0]
    token = r'(?:none|some \((?:true|false), (?:true|false), \d+\))'
    table = {}
    lines = [line for line in body.splitlines() if line.strip()]
    check(len(lines) == 226, 'Table length changed')
    for q, line in enumerate(lines):
        m = re.fullmatch(r'  \((' + token + r'), (' + token + r')\),?', line)
        check(m is not None, 'Unparsed table row')
        for b, s in enumerate(m.groups()):
            if s != 'none':
                w, d, t = re.fullmatch(r'some \((true|false), (true|false), (\d+)\)', s).groups()
                table[q, bool(b)] = (w == 'true', d == 'true', int(t))
    check(len(table) == 430, 'Expected 430 defined transitions')
    native = {}
    rename = {301: 102, 302: 120, 254: 230}
    for line in (INPUT / 'native.tm').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        m = re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)', line)
        check(m is not None, 'Unparsed native transition')
        q, b, w, d, t = m.groups()
        q, t = rename.get(int(q), int(q)), rename.get(int(t), int(t))
        key = (q, b == '1')
        check(key not in native, 'Duplicate native transition')
        native[key] = (w == '1', d == 'R', t)
    check(native == table, 'Native/formal tables differ')
    return table


def run_window(table, entry, head, cells, steps, exit_state, exit_head):
    tape = dict(cells)
    check(len(tape) == len(cells), 'Duplicate local window index')
    initial = dict(tape)
    q, h = entry, head
    for _ in range(steps):
        check(h in tape, 'Finite replay tried to read unknown exterior')
        row = table.get((q, tape[h]))
        check(row is not None, 'Finite replay halted before declared endpoint')
        w, direction, q = row
        tape[h] = w
        h += 1 if direction else -1
    check((q, h, tape) == (exit_state, exit_head, initial), 'Window endpoint/restoration failed')


def rocq_table_binding(texts,table):
    body=texts['Table230.v'].split('Definition table230 : list (bool * dir * nat * bool * dir * nat) := [',1)[1].split('].',1)[0]
    disabled_body=texts['TM230.v'].split('Definition tmn ',1)[1].split('match nth_error',1)[0]
    disabled=set(map(int,re.findall(r'Nat.eqb q (\d+)',disabled_body)))
    check(disabled=={79,121,140,175,183,191,192,202,208,219,224,226,227,228,229},'Rocq disabled rows changed')
    rows=[line.strip() for line in body.splitlines() if line.strip()]
    check(len(rows)==230,'Rocq table length')
    actual={}
    for q,line in enumerate(rows):
        m=re.fullmatch(r'\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\);?',line)
        check(m is not None,'Unparsed Rocq table row')
        if q not in disabled:
            for b,offset in ((False,0),(True,3)):
                w,d,t=m.groups()[offset:offset+3]
                actual[q,b]=(w=='true',d=='R',int(t))
    check(actual==table,'Rocq/plain/formal machine mismatch')
    check('Definition phys_of (r : nat) : nat := nth r [6; 2; 0; 4; 3; 7; 8; 5; 1] 0.' in texts['Interpreter230Check.v'],'Rocq physical-register map changed')
    check('Definition D0 := 64.' in texts['Interpreter230Sites.v'] and 'Definition FUEL := 4000.' in texts['Interpreter230Sites.v'],'Rocq gap/fuel changed')


def source_coverage(texts, table):
    # Enumerate the maintained 179-node program, not merely the received sites JSON.
    source = texts['KSource215Program.lean']
    body = source.split('def p215Nodes : Nat → Edge × Edge\n', 1)[1].split('  | _ =>', 1)[0]
    program = {}
    for line in body.splitlines():
        m = re.fullmatch(r'  \| (\d+) => (.*)', line)
        check(m is not None, 'Unparsed source node')
        n = int(m[1])
        es = re.findall(r'\.(inc|decnz|brk|cont|node|halt)(?: (\d+))?', m[2])
        check(len(es) == 2, 'Source node arity')
        program[n] = tuple((op, int(arg) if arg else 0) for op, arg in es)
    check(set(program) == set(range(179)), 'Source program coverage gap')
    check('def p215 : Program := ⟨p215Nodes, 178, 179⟩' in source, 'Source root changed')
    rocq_body=texts['Prog215.v'].split('Definition p215_tab : list (cedge * cedge) := [',1)[1].split('].',1)[0]
    rocq_lines=[line.strip() for line in rocq_body.splitlines() if line.strip()]
    check(len(rocq_lines)==179 and 'root := 178; nnodes := 179' in texts['Prog215.v'],'Rocq source root/count')
    opmap={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CN':'node','CH':'halt'}
    for n,line in enumerate(rocq_lines):
        m=re.fullmatch(r'\((C[IDBCNH])(?: (\d+))?, (C[IDBCNH])(?: (\d+))?\);?',line)
        check(m is not None,'Unparsed Rocq source row')
        es=tuple((opmap[op],int(arg) if arg else 0) for op,arg in ((m[1],m[2]),(m[3],m[4])))
        check(es==program[n],'Rocq and Lean source nodes differ')
    opnames = {'inc': 'CI', 'decnz': 'CD', 'brk': 'CB', 'cont': 'CC', 'halt': 'CH'}
    sites = []
    def descend(n, word):
        for b, (op, arg) in enumerate(program[n]):
            w = word + str(b)
            if op == 'node':
                check(arg < n, 'Source DAG is not decreasing')
                descend(arg, w)
            else:
                sites.append([w, opnames[op], None if op == 'halt' else arg])
    descend(178, '')
    check(sites == json.loads((INPUT / 'sites.json').read_text()), 'Entire ordered source leaf enumeration differs')
    check(len({s[0] for s in sites}) == len(sites) == 4751, 'Source leaf count/uniqueness')
    # Independently route every full source word through current decoder roles.
    decoder = texts['K215Decoder.lean']
    nodes = []
    for line in literal_array(decoder, 'sourceNodes'):
        m = re.fullmatch(r'\.(leaf|fork) (\d+) (\d+)', line)
        check(m is not None, 'Unparsed decoder node')
        nodes.append((m[1], int(m[2]), int(m[3])))
    blocks = []
    for line in literal_array(decoder, 'blocks'):
        m = re.fullmatch(r'⟨(\d+), (\d+), \[(.*?)\], (\d+)⟩', line)
        check(m is not None, 'Unparsed decoder block')
        q, t, word, steps = int(m[1]), int(m[2]), bools(m[3]), int(m[4])
        check(steps > 0, 'Empty decoder block')
        run_window(table, q, 0, [(i-len(word)+1,b) for i,b in enumerate(word)], steps, t, 1)
        blocks.append((q, t, word, steps))
    roles = []
    edge_re = r'\(\.(?:internal \d+ \d+|primitive \d+ ⟨(?:true|false), (?:1|\(-1\)), \d+⟩)\)'
    for line in literal_array(decoder, 'roles'):
        m = re.fullmatch(r'⟨(\d+), (\d+), \[(.*?)\], ('+edge_re+r'), ('+edge_re+r')⟩', line)
        check(m is not None, 'Unparsed decoder role: ' + line)
        edges = []
        for edge in m.groups()[3:5]:
            v = re.fullmatch(r'\(\.internal (\d+) (\d+)\)', edge)
            if v:
                edges.append(('internal', int(v[1]), int(v[2])))
            else:
                v = re.fullmatch(r'\(\.primitive (\d+) ⟨(true|false), (1|\(-1\)), (\d+)⟩\)', edge)
                check(v is not None, 'Bad primitive edge')
                edges.append(('primitive', int(v[1]), (v[2]=='true',v[3]=='1',int(v[4]))))
        roles.append((int(m[1]), int(m[2]), bools(m[3]), tuple(edges)))
    check((len(nodes), len(blocks), len(roles)) == (202,281,234), 'Decoder literal count')
    check(roles[0][:3] == (201,84,(True,)), 'Decoder root role changed')
    for n,q,suffix,edges in roles:
        check(1 <= len(suffix) <= 2 and nodes[n][0] == 'fork', 'Invalid role')
        for b,edge in enumerate(edges):
            child = nodes[n][b+1]
            check(child < n, 'Decoder DAG not decreasing')
            if edge[0] == 'primitive':
                check(child == edge[1] and nodes[child][0] == 'leaf', 'Primitive source binding')
                check(table.get((q,bool(b))) == edge[2], 'Primitive machine binding')
            else:
                _, r, k = edge
                other = roles[r]
                block = blocks[k]
                word = suffix + (bool(b),)
                check(nodes[child][0] == 'fork' and other[0] == child, 'Internal source binding')
                check(other[2] == word[-2:], 'Role suffix binding')
                check(block[:2] == (q,other[1]) and len(block[2]) <= len(word) and block[2] == word[-len(block[2]):], 'Block word binding')
    numeric_ops = {'CI':0, 'CD':1, 'CB':2, 'CC':3, 'CH':4}
    ports = {}
    for word,op,arg in sites:
        r = 0
        for i,bit in enumerate(word):
            n,q,suffix,edges = roles[r]
            edge = edges[int(bit)]
            if i == len(word)-1:
                check(edge[0] == 'primitive' and nodes[edge[1]] == ('leaf',numeric_ops[op],0 if arg is None else arg), 'Full-word leaf binding')
                ports[word] = q
            else:
                check(edge[0] == 'internal', 'Premature primitive edge')
                r = edge[1]
    return sites, ports

# Segments: ('b', bit), ('r', bit, coefficient, constant), ('x', effect, register).
def bit(b): return ('b', bool(b))
def run(b,a,c): return ('r', bool(b), a, c)
def box(effect='none',r=0): return ('x', effect, r)
SKIP = (51,36,25,48,32,33,22,55,60)
PHY = (6,2,0,4,3,7,8,5,1)

def home(s):
    q,left,L,R = s
    if q != 2 or not left: return None
    rev = list(reversed(L))
    while rev and rev[0][0] in ('b','r') and not rev[0][1]:
        rev.pop(0)
    if not rev or rev.pop(0) != bit(True): return None
    streak = 0
    for seg in reversed(rev):
        if seg[0] == 'x': return None
        if seg[0] == 'b':
            streak = 0 if seg[1] else streak+1
        elif seg[1]:
            if seg[3] != 0: streak = 0
        else:
            if seg[2] != 0: return None
            streak += seg[3]
        if streak >= 8: return None
    return (84,False,(bit(True),),tuple(rev)+R), True, 'home'


def next_symbolic(table,branch,s,use_home=True):
    h = home(s) if use_home else None
    if h is not None: return h
    q,left,L,R = s
    if left and not L: return (q,False,(),(bit(False),)+R),False,'orient'
    if not left and not R: return None
    x = L[0] if left else R[0]
    if x[0] == 'b':
        if left: return (q,False,L[1:],(x,)+R),False,'orient'
        row = table.get((q,x[1]))
        if row is None: return None
        w,d,t = row
        return ((t,False,(bit(w),)+L,R[1:]) if d else (t,True,L,(bit(w),)+R[1:])),True,'literal'
    if x[0] == 'r':
        _,b,a,c = x
        row = table.get((q,b))
        if row is not None and row[1] == (not left) and row[2] == q:
            return ((q,True,L[1:],(run(row[0],a,c),)+R) if left else (q,False,(run(row[0],a,c),)+L,R[1:])),False,'scan'
        if c == 0 and a != 0: return None
        replacement = () if c == 0 else (bit(b),run(b,a,c-1))
        return ((q,True,replacement+L[1:],R) if left else (q,False,L,replacement+R[1:])),False,'peel'
    if left or len(R) != 1: return None
    _,effect,r = x
    oracle = None
    if effect == 'none' and q in SKIP:
        rr = SKIP.index(q)
        oracle = (1 if rr == 0 else 3,box('mark',rr),False)
    elif effect == 'mark' and r < 9:
        if q == 64: oracle = (40,box('inc',r),False)
        elif q == 0 and branch is not None and branch[0] == r:
            oracle = (97,box(),False) if branch[1] else (40,box('dec',r),True)
    if oracle is not None:
        t,y,extra = oracle
        return (t,True,((bit(True),)+L if extra else L),(y,)),False,'oracle'
    # Essential: oracle=None is not itself a halt. The formal stepper falls back.
    row = table.get((q,False))
    if row is not None and row[:2] == (False,False):
        return (row[2],True,L,R),True,'box-fallback'
    return None


def normal(xs, trim=False):
    # Independent right fold, matching the formal push/norm, not the author's forward loop.
    acc = []
    for seg in reversed(xs):
        token = run(seg[1],0,1) if seg[0] == 'b' else seg
        if token[0] == 'r' and token[2:] == (0,0): continue
        if token[0] == 'r' and acc and acc[0][:2] == token[:2]:
            token = run(token[1],token[2]+acc[0][2],token[3]+acc[0][3])
            acc = acc[1:]
        acc.insert(0,token)
    if trim and acc and acc[-1][:2] == ('r',False): acc.pop()
    return tuple(acc)


def matches(s,t):
    return s[:2] == t[:2] and normal(s[2],True) == normal(t[2],True) and normal(s[3]) == normal(t[3])


def execute(table,branch,s,target,moved=False,fuel=4000,use_home=True):
    trace=[]
    # Test only at positive remaining fuel, as execWith 0 always returns none.
    while fuel > 0:
        if moved and target(s): return s,moved,trace,fuel
        out = next_symbolic(table,branch,s,use_home=use_home)
        check(out is not None,'Symbolic execution stuck before target')
        t,m,kind=out
        trace.append((s,t,m,kind))
        s=t; moved=moved or m; fuel-=1
    raise RuntimeError('Symbolic execution exhausted fuel; not counted as success')


def increment(word):
    out=list(word)
    for i in range(len(out)-1,-1,-1):
        if out[i] == '0':
            out[i]='1'
            return ''.join(out)
        out[i]='0'
    return ''.join(out)


def strip_false(word):
    rev=list(reversed(word))
    while rev:
        if rev.pop(0) == '0': break
    return ''.join(reversed(rev))


def target_for(word,r,z):
    prefix = strip_false(word) if z else word
    successor = increment(prefix)
    overflow = all(c == '1' for c in prefix)
    return (84,False,(bit(True),),tuple(bit(c=='1') for c in successor)+(run(False,1,64+int(overflow)+int(not z)-len(successor)),bit(True),box() if z else box('dec',r)))


def cut_for(r,s):
    # Exact shape, physical register included. Never normal-form matching or oracle failure.
    return s[0] == 0 and s[1] is False and s[3] == (box('mark',r),)


def replay_mode(table,sites,ports,from_port,use_home,expected):
    execute_mode = lambda branch,s,target,**kwargs: execute(table,branch,s,target,use_home=use_home,**kwargs)
    rows=[]
    totals=collections.Counter()
    for idx,(word,op,logical) in enumerate(sites):
        if op != 'CD': continue
        check(0 < len(word) <= 48 and logical < 9,'checkEdge domain guard')
        r=PHY[logical]
        start=(ports[word],False,tuple(bit(c=='1') for c in reversed(word[:-1]))+(bit(True),),(bit(word[-1]=='1'),run(False,1,64-len(word)),bit(True),box()))
        if not from_port:
            start=(84,False,(bit(True),),tuple(bit(c=='1') for c in word)+(run(False,1,64-len(word)),bit(True),box()))
        # Prefix independently executes neutral branch to exact stop, before calling stepper there.
        cut,moved,prefix,fleft=execute_mode(None,start,lambda s:cut_for(r,s))
        check(moved and any(t[2] for t in prefix),'Prefix must establish positive concrete progress')
        targets={z:target_for(word,r,z) for z in (True,False)}
        complete={}
        suffix={}
        for z in (True,False):
            end,_,whole,remaining=execute_mode((r,z),start,lambda s:matches(s,targets[z]))
            complete[z]=whole
            check(whole[:len(prefix)] == prefix,'Neutral prefix not identical to guarded execution')
            check(whole[len(prefix)][0] == cut,'Cut not exact common intermediate state')
            e2,_,tail,fremain=execute_mode((r,z),cut,lambda s:matches(s,targets[z]),moved=True)
            check(tail == whole[len(prefix):] and e2 == end,'Suffix differs from baseline')
            # False restart is also successful here, but the composition only needs true.
            e3,_,tail_false,_=execute_mode((r,z),cut,lambda s:matches(s,targets[z]),moved=False)
            check(e3 == end and tail_false == tail,'Unexpected dependence on resetting moved')
            check(sum(t[3]=='oracle' for t in tail) == 1,'Unexpected suffix oracle count')
            suffix[z]=tail
            totals['baseline_symbolic_steps']+=len(whole)
            totals['suffix_symbolic_steps']+=len(tail)
            totals['full_runs']+=1
            totals['min_remaining_full_fuel']=min(totals.get('min_remaining_full_fuel',4000),remaining)
        check(complete[True][len(prefix)] != complete[False][len(prefix)],'Cut not first branch divergence')
        check(suffix[True][0][1] == (97,True,cut[2],(box(),)) and suffix[True][0][2] is False,'Zero oracle cut behavior')
        check(suffix[False][0][1] == (40,True,(bit(True),)+cut[2],(box('dec',r),)) and suffix[False][0][2] is False,'Nonzero oracle cut behavior')
        homes=sum(t[3]=='home' for t in prefix)
        check(homes == (2 if use_home else 0),'Prefix Home shortcut count')
        totals['prefix_symbolic_steps']+=len(prefix)
        totals['prefix_homes']+=homes
        rows.append({'site_index':idx,'word':word,'logical_register':logical,'physical_register':r,
                     'prefix_steps':len(prefix),'zero_suffix_steps':len(suffix[True]),
                     'nonzero_suffix_steps':len(suffix[False]),'prefix_home_shortcuts':homes,
                     'cut_sha256':hashlib.sha256(repr(cut).encode()).hexdigest()})
    check(len(rows)==1425 and totals['full_runs']==2850,'Incomplete decrement coverage')
    total=totals['baseline_symbolic_steps']; saved=totals['prefix_symbolic_steps']
    check((total,total-saved,saved)==expected,'Claimed mode metrics do not reproduce')
    return {'source_start':'leafPort' if from_port else 'start Q', 'home_ready':use_home,
        'decrement_sites':len(rows),'decrement_outcomes':totals['full_runs'],
        'baseline_symbolic_steps':total,'factored_symbolic_steps':total-saved,
        'saved_symbolic_steps':saved,'saved_fraction':saved/total,
        'prefix_steps_min':min(r['prefix_steps'] for r in rows),
        'prefix_steps_max':max(r['prefix_steps'] for r in rows),
        'prefix_home_shortcuts':totals['prefix_homes'],'every_prefix_positive':True,
        'minimum_remaining_full_fuel':totals['min_remaining_full_fuel'],
        'max_full_execution_steps':4000-totals['min_remaining_full_fuel'],
        'physical_registers':dict(sorted(collections.Counter(r['physical_register'] for r in rows).items())),
        'uses':rows}

def main():
    texts,pins=read_pinned()
    table=formal_table(texts['KTable215.lean'])
    rocq_table_binding(texts,table)
    sites,ports=source_coverage(texts,table)
    # Establish the finite ready-table guard before using Home shortcuts.
    states=(2,3,5,9,15,23,34,50)
    check(all(table.get((q,True)) == (True,False,2) for q in states),'Home reset rows')
    check(all(table.get((states[i],False)) == (False,False,states[i+1]) for i in range(7)),'Home next rows')
    run_window(table,2,0,[(1,True)]+[(i,False) for i in range(0,-9,-1)],18,84,2)
    modes={
        'lean_full_start_home': replay_mode(table,sites,ports,False,True,(514073,312947,201126)),
        'rocq_full_start_raw': replay_mode(table,sites,ports,False,False,(1337729,852647,485082)),
        'lean_leaf_port_home_diagnostic': replay_mode(table,sites,ports,True,True,(415205,263513,151692)),
    }
    # Regressions for the exact classifier and the execWith fuel convention.
    test_cut=(0,False,(),(box('mark',0),))
    check(cut_for(0,test_cut) and not cut_for(1,test_cut),'Cut must identify physical register')
    check(not cut_for(0,(0,True,(),test_cut[3])),'Cut orientation')
    check(not cut_for(0,(0,False,(),test_cut[3]+(bit(False),))),'Cut singleton shape')
    try:
        execute(table,None,test_cut,lambda _:True,moved=True,fuel=0)
    except RuntimeError as error:
        check('exhausted fuel' in str(error),'Unexpected zero-fuel error')
    else:
        raise RuntimeError('Zero fuel incorrectly accepted an already reached target')
    # Regression witness: generic neutral-oracle failure does not imply stepper failure.
    witness=(0,False,(),(box('mark',0),))
    changed=dict(table); changed[0,False]=(False,False,94)
    check(next_symbolic(changed,None,witness)==((94,True,(),witness[3]),True,'box-fallback'),'Missing generic fallback')
    result={'status':'INDEPENDENT_FINITE_REPLAY_PASS','revision':REVISION,
        'scope':'Finite literal-data audit, not compiled Lean or Rocq and not a performance benchmark.',
        'source_leaf_count':len(sites),'defined_transitions':len(table),
        'decoder_nodes':202,'decoder_roles':234,'decoder_blocks_replayed':281,
        'all_sites_derived_from_current_program':True,'all_ports_derived_from_current_roles':True,
        'home_ready_guard_independently_checked':True,'rocq_formal_native_tables_identical':True,'rocq_lean_program_nodes_identical':True,
        'budget_exhaustion_is_hard_failure':True,'generic_oracle_none_fallback_witness_passed':True,
        'modes':modes,
        'source_pins':pins,
        'input_digests':{name:hashlib.sha256((INPUT/name).read_bytes()).hexdigest() for name in ('sites.json','native.tm')},
        }
    out=Path(__file__).with_name('decrement_fork_result.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    display={k:v for k,v in result.items() if k != 'source_pins'}
    display['modes']={name:{k:v for k,v in mode.items() if k != 'uses'} for name,mode in modes.items()}
    print(json.dumps(display,indent=2))

if __name__ == '__main__': main()

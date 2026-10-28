from pathlib import Path
from functools import lru_cache
from collections import deque, Counter
import re, json, hashlib
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
BASE = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
PHYS = [6, 2, 0, 4, 3, 7, 8, 5, 1]
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def parsed(name, count):
    path = BASE / (name + '.lean')
    nodes = {}
    for line in path.read_text().splitlines():
        match = re.match(r'\s*\| (\d+) =>', line)
        if match:
            edges = re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?', line)
            assert len(edges) == 2, line
            nodes[int(match[1])] = tuple((kind, int(n) if n else 0) for kind,n in edges)
    assert len(nodes) == count, (name, len(nodes))
    return nodes, {'path':str(path),'sha256':sha(path)}
def inc(path):
    out = list(path); i = len(out)-1
    while i >= 0 and out[i]: out[i] = False; i -= 1
    if i >= 0: out[i] = True
    return tuple(out)
def strip(path, bit, count):
    i = len(path)
    while i > 0 and count > 0:
        i -= 1
        if path[i] == bit: count -= 1
    return path[:i]
def catalogue(nodes, root):
    @lru_cache(None)
    def stats(edge):
        if edge[0] != 'node': return 0, 1
        a, b = nodes[edge[1]]
        ha, sa = stats(a); hb, sb = stats(b)
        return 1+max(ha,hb), sa+sb
    def entries(edge, path=()):
        if edge[0] != 'node': return [(path,edge)]
        a,b = nodes[edge[1]]
        return entries(a,path+(False,)) + entries(b,path+(True,))
    def resolve(path):
        edge = ('node',root); offset = 0; depth = 0
        while edge[0] == 'node':
            a,b = nodes[edge[1]]
            bit = path[depth] if depth < len(path) else False
            depth += 1
            if bit: offset += stats(a)[1]; edge = b
            else: edge = a
        return offset+1
    es = entries(('node',root)); rows = []
    for path,(op,r) in es:
        if op == 'halt': row = (4,0,0,0)
        elif op == 'inc': q = resolve(inc(path)); row = (1,PHYS[r],q,q)
        elif op == 'decnz': row = (2,PHYS[r],resolve(inc(strip(path,False,1))),resolve(inc(path)))
        elif op == 'brk': q = resolve(inc(strip(path,False,r))); row = (3,0,q,q)
        elif op == 'cont': q = resolve(strip(path,True,r)); row = (3,0,q,q)
        else: raise AssertionError(op)
        rows.append(row)
    return rows, es, stats(('node',root))
def rowhash(rows): return hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()
def iso(rows_a, rows_b):
    forward={0:0,1:1}; backward={0:0,1:1}; todo=deque([(1,1)]); visited=set()
    while todo:
        a,b=todo.popleft()
        if (a,b) in visited or a==0: continue
        visited.add((a,b)); ra=rows_a[a-1]; rb=rows_b[b-1]
        if ra[:2] != rb[:2]: return {'success':False,'reason':'opcode/register mismatch','a_pc':a,'b_pc':b,'a_row':ra,'b_row':rb,'visited_pairs':len(visited)}
        for x,y in zip(ra[2:],rb[2:]):
            if x in forward and forward[x]!=y: return {'success':False,'reason':'forward map conflict','a_pc':a,'b_pc':b,'a_successor':x,'old_b_successor':forward[x],'new_b_successor':y,'visited_pairs':len(visited)}
            if y in backward and backward[y]!=x: return {'success':False,'reason':'backward map conflict','a_pc':a,'b_pc':b,'b_successor':y,'old_a_successor':backward[y],'new_a_successor':x,'visited_pairs':len(visited)}
            forward[x]=y; backward[y]=x
            todo.append((x,y))
    return {'success':True,'visited_live_pairs':len(visited),'all_live_nodes_covered':len(visited)==len(rows_a)==len(rows_b),'mapping_sha256':hashlib.sha256(json.dumps(sorted(forward.items()),separators=(',',':')).encode()).hexdigest()}
nodes={}; pins=[]
for name,count in [('Dag222',461),('Dag219',7),('DagDom',18),('DagPerm',7)]:
    piece,pin=parsed(name,count); nodes.update(piece); pins.append(pin)
assert set(nodes)==set(range(487))
pnodes,pin=parsed('KSource215Program',179); pins.append(pin)
a,ae,astats=catalogue(nodes,0)
b,be,bstats=catalogue(pnodes,178)
assert len(a)==len(b)==4751
assert rowhash(a)=='42bcd1c057e73b82f6e13d151dbe280f1d30e06784575e788dbe2a8430704dcd'
diffs=[i for i,(x,y) in enumerate(zip(a,b),1) if x!=y]
result={'scope':'Read-only finite comparison from current literal sources using exact catalogue row conventions; no Lean proof or internal simulation is claimed.',
 'physical_map':PHYS,'dagperm':{'root':0,'nodes':487,'depth':astats[0],'rows':len(a),'row_sha256':rowhash(a)},
 'p215':{'root':178,'nodes':179,'depth':bstats[0],'rows':len(b),'row_sha256':rowhash(b)},
 'literal_rows_equal':a==b,'different_row_count':len(diffs),
 'first_differences':[{'pc':i,'dagperm':a[i-1],'p215':b[i-1],'dagperm_edge':ae[i-1][1],'p215_edge':be[i-1][1]} for i in diffs[:12]],
 'opcode_register_multisets_equal':Counter(r[:2] for r in a)==Counter(r[:2] for r in b),
 'root_preserving_labelled_directed_isomorphism':iso(a,b),
 'source_pins':pins,'script':{'path':__file__,'sha256':sha(__file__)}}
# Classify every differing row and rule out entry into a swapped-pair interior.
diffset=set(diffs); pair_starts=[]; used=set()
for pc in diffs:
    if pc in used: continue
    assert pc+1 in diffset
    aa,an=a[pc-1],a[pc]; bb,bn=b[pc-1],b[pc]
    assert aa[0]==an[0]==bb[0]==bn[0]==1
    assert aa[:2]==bn[:2] and an[:2]==bb[:2]
    assert aa[1]!=an[1]
    assert aa[2:]==bb[2:]==(pc+1,pc+1)
    assert an[2:]==bn[2:]==(pc+2,pc+2)
    pair_starts.append(pc);used.update([pc,pc+1])
assert used==diffset
interiors={pc+1 for pc in pair_starts}
assert 1 not in interiors
for rows in [a,b]:
    for pc,row in enumerate(rows,1):
        for target in row[2:]:
            assert target not in interiors or pc==target-1
assert all(ra[2:]==rb[2:] for ra,rb in zip(a,b))
# A diagonal certificate for the existing, genuinely internal segment theorem:
# root plus all test successors. This is an audit of finite data, not its proof.
cuts=sorted({1}|{target for row in a if row[0]==2 for target in row[2:]})
assert set(cuts).isdisjoint(interiors)
cut_index={pc:i for i,pc in enumerate(cuts)}
def segment(rows,pc):
    offsets=[0]*9; steps=0;seen=set()
    while True:
        assert pc not in seen, ('straight-line cycle',pc)
        seen.add(pc); row=rows[pc-1];steps+=1
        if row[0] in [2,4]: return pc,offsets,steps
        assert row[0] in [1,3]
        if row[0]==1: offsets[row[1]]+=1
        pc=row[2]
cert=[];max_fuel=0
for pc in cuts:
    ta,oa,fa=segment(a,pc);tb,ob,fb=segment(b,pc)
    assert ta==tb and oa==ob
    ra,rb=a[ta-1],b[tb-1]
    assert ra==rb and ra[0] in [2,4]
    max_fuel=max(max_fuel,fa,fb)
    if ra[0]==2: s0,s1=cut_index[ra[2]],cut_index[ra[3]]
    else: s0=s1=0
    cert.append([pc,pc,[0]*9,[0]*9,s0,s1])
result['adjacent_increment_swaps']={'pair_count':len(pair_starts),
  'all_successors_identical':True,'all_pairs_distinct_registers':True,
  'all_pairs_sequential':True,'no_other_entry_to_pair_interior':True,
  'pair_start_pcs':pair_starts}
result['diagonal_segment_certificate_audit']={'entry_count':len(cert),
  'fuel_suffices':max_fuel,'root_entry':cut_index[1],
  'all_offsets_equal_at_terminal_test_or_halt':True,
  'all_branch_successors_in_certificate':True,
  'all_entry_offsets_nine_zeros':True,
  'entries_sha256':hashlib.sha256(json.dumps(cert,separators=(',',':')).encode()).hexdigest(),
  'scope':'Finite source reconstruction only; actual ArithmeticControlBisim.checkFrom kernel theorem remains unproved.'}
print(json.dumps(result,indent=2))

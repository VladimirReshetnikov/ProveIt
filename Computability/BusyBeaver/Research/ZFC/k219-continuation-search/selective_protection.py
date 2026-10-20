#!/usr/bin/env python3
"""Bounded selective old-state protection, decoder-binding measurements only."""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,hashlib,importlib,json,sys,time
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
class PrefixFailure(ValueError):
 def __init__(self,detail):self.detail=detail;super().__init__(detail['reason'])
def decoder_map_trace(s,table,tree):
 """Same 100-step known-prefix check as build221, retaining first failing edge."""
 groups=defaultdict(set);paths=defaultdict(list);routes={}
 def visit(node,prefix,state,prior):
  if s.leaf(node):return
  groups[state].add(node);paths[state].append(prefix);routes[prefix]=prior
  for bit in (0,1):
   if s.leaf(node[bit]):continue
   tape={i:int(v) for i,v in enumerate(prefix+str(bit))};tape[-1]=1;before=tape.copy();head,q=len(prefix),state;trace=[]
   def fail(reason):
    raise PrefixFailure({'reason':reason,'prefix':prefix+str(bit),'state':q,'head':head,'before':sorted(before.items()),'after':sorted(tape.items()),'edge_trace':trace,'all_trace':[x for edge in prior for x in edge]+trace})
   for tick in range(100):
    if head==len(prefix)+1:break
    if head not in tape:fail('read_outside_known_prefix')
    if (q,tape[head]) not in table:fail('missing_action')
    w,d,z=table[q,tape[head]];trace.append({'q':q,'bit':tape[head],'head':head,'action':[w,d,z]});tape[head]=w;head+=d;q=z
   if tape!=before or head!=len(prefix)+1:fail('prefix_changed_or_did_not_advance')
   visit(node[bit],prefix+str(bit),q,prior+[trace])
 visit(tree,'',84,[])
 return groups,paths,routes

def compile_tree(s, b, table, old_src, new_src, protected, capture):
    """Incremental exploratory allocator, adapted from K220 recompile.py.

    K219 has one duplicated subtree role. Unlike the older function-valued
    validator, unchanged nodes may resolve to any of their exact old states.
    This is a decoder-prefix check only, never a primitive/runtime proof.
    """
    groups, _ = b.decoder_map(table, old_src)
    old_states = defaultdict(set)
    for q, nodes in groups.items():
        for n in nodes: old_states[n].add(q)
    node_state = {n: min(qs) for n, qs in old_states.items()}
    live = set()
    def visit(n):
        if s.leaf(n) or n in live: return
        live.add(n); visit(n[0]); visit(n[1])
    visit(new_src)
    origins = {}
    def walk(n, o):
        if s.leaf(n) or o is None or s.leaf(o): return
        if n != o: origins.setdefault(n, o)
        walk(n[0], o[0]); walk(n[1], o[1])
    walk(new_src, old_src)
    origins = {n: o for n, o in origins.items() if o not in live}
    compiled = dict(table); mapped = dict(node_state); mapped[new_src] = 84
    claimed = {84: new_src}; reused_states = []; fresh = max(300, max(q for q, _ in table)+1)
    nextfresh = fresh; reused = 0; leaves = {}
    for op in ['CI', 'CD', 'CC', 'CB', 'CH']:
        for arg in ([None] if op == 'CH' else range(10)):
            ch = op, arg
            for bit in (0, 1):
                choices = Counter(table[q, bit] for n, qs in old_states.items() for q in qs if n[bit] == ch)
                direct = [a for a in choices if a[:2] == (bit, 1)]
                if len(direct) == 1: leaves[ch, bit] = direct[0]
                elif ch == ('CC', 1) and bit == 1: leaves[ch, bit] = (0, -1, 1)
                elif ch == ('CC', 2) and bit == 1: leaves[ch, bit] = (0, -1, 16)
                elif ch == ('CB', 1) and bit == 1: leaves[ch, bit] = (0, -1, 40)
    def go(n):
        nonlocal fresh, reused
        if n in mapped: return mapped[n]
        if n in origins and origins[n] in node_state and len(groups[node_state[origins[n]]]) == 1 and node_state[origins[n]] not in claimed and node_state[origins[n]] not in protected:
            q = node_state[origins[n]]; reused += 1; reused_states.append(q)
        else: q = fresh; fresh += 1
        mapped[n] = q; claimed[q] = n
        for bit, ch in enumerate(n):
            if not s.leaf(ch): compiled[q, bit] = (bit, 1, go(ch))
            elif n in origins and origins[n] in node_state and origins[n][bit] == ch:
                compiled[q, bit] = table[node_state[origins[n]], bit]
            elif (ch, bit) in leaves: compiled[q, bit] = leaves[ch, bit]
            else: raise ValueError(('No generic leaf entry', ch, bit, q))
        return q
    for bit, ch in enumerate(new_src):
        compiled[84, bit] = (bit, 1, go(ch)) if not s.leaf(ch) else leaves[ch, bit]
    reach = {0}; todo = [0]
    for q in todo:
        for bit in (0, 1):
            z = compiled[q, bit][2]
            if z != 254 and z not in reach: reach.add(z); todo.append(z)
    compiled = {k: v for k, v in compiled.items() if k[0] in reach}
    capture.update(table=compiled, reused_states=sorted(reused_states), old_groups=groups)
    gg, path_map, routes = decoder_map_trace(s, compiled, new_src)
    for q, nodes in gg.items():
        for n in nodes:
            permitted = old_states[n] if n in old_states and n != new_src else {mapped[n]}
            if q not in permitted:
                path = next(p for p in path_map[q] if s.subtree(new_src, p) == n)
                raise PrefixFailure({'reason':'node_binding_mismatch','state':q,'permitted':sorted(permitted),'prefix':path,'edge_trace':routes[path][-1] if routes[path] else [],'all_trace':[x for edge in routes[path] for x in edge]})
    return compiled, {'working_states': len(compiled)//2, 'fresh': fresh-nextfresh,
        'reused': reused, 'aliases': sum(len(ns)-1 for ns in gg.values()),
        'decoder_states': len(gg), 'interior_roles': sum(map(len, gg.values())),
        'scope': 'Raw table and exact decoder-prefix binding only; no runtime or startup validation.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 require(__debug__ and not sys.flags.optimize,'Assertions must be enabled');require(not a.output.exists(),'Output must be fresh')
 library=P/'compiler-inputs';baseline=P/'../candidate-k219';variants=P/'../k219-pivot-fusion/results/membership-protected'
 pins={str((baseline/'sites219.json').resolve()):'0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',str((baseline/'k219.native.tm').resolve()):'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'}
 for name,d in json.loads((library/'provenance.json').read_text()).items():pins[str((library/name).resolve())]=d['sha256']
 names={'RAB-left':'9891a1212f4cacb152b09d58c3ee901dabd29e96def960908a589fb8bf7ebb96','RBC-left':'01ef6ec12e2c3308b0fc9e8f1bc2cf883422e0720b019a2d815ebe5f5b3d9400','RCA-right':'b6ceff73ab847630b347561939a56c868034204a895c5131f4269cca9fe73d70'}
 for name,h in names.items():pins[str((variants/name/'sites.json').resolve())]=h
 require(all(sha(Path(p))==h for p,h in pins.items()),'Pinned input drift')
 sys.dont_write_bytecode=True;sys.path.insert(0,str(library.resolve()))
 s=importlib.import_module('source_language');b=importlib.import_module('build221')
 old=s.tree(json.loads((baseline/'sites219.json').read_text()));table=b.read_table((baseline/'k219.native.tm').read_bytes())
 cap={};identity,identity_metrics=compile_tree(s,b,table,old,old,set(),cap)
 require(identity==table and identity_metrics['working_states']==219,'Exact baseline control')
 # Independent original prefix walker must agree with the traced clone.
 original_groups,original_paths=b.decoder_map(table,old);traced_groups,traced_paths,_=decoder_map_trace(s,table,old)
 require(original_groups==traced_groups and original_paths==traced_paths,'Trace walker baseline control')
 a.output.mkdir(parents=True);(a.output/'selective_protection.py').write_bytes(Path(__file__).read_bytes());started=time.monotonic();all_results=[]
 for name,h in names.items():
  out=a.output/name;out.mkdir();raw=(variants/name/'sites.json').read_bytes();(out/'sites.json').write_bytes(raw);rows=json.loads(raw);new=s.tree(rows)
  require(s.metrics(new)['dag_nodes']==205,'Expected205DAG');require(s.graph_arithmetic(rows)[0]==s.graph_intervals(rows),'Independent source CFG')
  protected=set();attempts=[];status='ATTEMPT_LIMIT'
  for index in range(64):
   if time.monotonic()-started>=120:status='TIME_LIMIT';break
   capture={};attempt={'attempt':index,'protected_states':sorted(protected)};now=time.monotonic()
   try:
    compiled,metrics=compile_tree(s,b,table,old,new,protected,capture)
    # Recheck with unchanged complete prefix walker and exact raw roundtrip.
    g1,p1=b.decoder_map(compiled,new);g2,p2,_=decoder_map_trace(s,compiled,new);require(g1==g2 and p1==p2,'Trace walker candidate control')
    encoded=b.table_bytes(compiled);require(b.read_table(encoded)==compiled,'Raw roundtrip')
    (out/'raw-binding-valid.native.tm').write_bytes(encoded)
    attempt.update(status='DECODER_PREFIX_BINDING_PASS',metrics=metrics,raw_sha256=hashlib.sha256(encoded).hexdigest());status=attempt['status']
   except PrefixFailure as exc:
    detail=exc.detail;reused=set(capture.get('reused_states',[]))
    # Exclude the intended edge starting state first; intermediate repurposed
    # states reveal decoder/helper interference. Protection is by state ID,
    # covering every old subtree alias and every incoming branch simultaneously.
    candidates={x['q'] for x in detail['edge_trace'][1:]}|{detail['state']}
    added=(candidates & reused)-protected;method='intermediate_or_arrival_reused_state'
    if not added:
     added=({x['q'] for x in detail['all_trace']} & reused)-protected;method='fallback_full_prefix_reused_states'
    attempt.update(status='PREFIX_REJECTED',failure=detail,reused_states=sorted(reused),newly_protected_states=sorted(added),protection_method=method,old_alias_counts={str(q):len(capture['old_groups'].get(q,())) for q in sorted(added)})
    if not added:status='NO_NEW_IMPLICATED_REUSED_STATE'
    protected.update(added)
   except (ValueError,KeyError,AssertionError) as exc:
    attempt.update(status='OTHER_REJECTION',error=repr(exc));status='OTHER_REJECTION'
   attempt['seconds']=time.monotonic()-now;attempts.append(attempt);dump(out/f'attempt-{index:02d}.json',attempt)
   if capture.get('table') is not None and attempt['status']!='DECODER_PREFIX_BINDING_PASS':(out/f'rejected-{index:02d}.native.tm').write_bytes(b.table_bytes(capture['table']))
   if status!='ATTEMPT_LIMIT':break
  result={'name':name,'status':status,'attempts':len(attempts),'protected_states':sorted(protected),'source_sha256':h,'source_metrics':s.metrics(new),'final_attempt':attempts[-1] if attempts else None};dump(out/'result.json',result);all_results.append(result)
 require(all(sha(Path(p))==h for p,h in pins.items()),'Input drift after search')
 result={'status':'BOUNDED_SELECTIVE_ALLOCATION_MEASUREMENT_COMPLETE','inputs':pins,'seconds':time.monotonic()-started,'limits':{'attempts_per_variant':64,'shared_seconds':120,'prefix_microsteps':100},'baseline_identity':identity_metrics,'variants':all_results,'scope':'Greedy state-level protection from exact prefix witnesses; no optimality claim. A binding pass checks decoder prefixes only, not arithmetic helper, primitive runtime, startup or consistency calibration.'}
 dump(a.output/'result.json',result);print(json.dumps({'status':result['status'],'seconds':result['seconds'],'variants':[{'name':r['name'],'status':r['status'],'attempts':r['attempts'],'protected':r['protected_states'],'metrics':(r['final_attempt'] or {}).get('metrics')} for r in all_results]},indent=2))
if __name__=='__main__':main()

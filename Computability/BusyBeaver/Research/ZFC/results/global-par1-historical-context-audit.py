"""Finite original-source par1/decoder classification; no mutant/table run."""
from pathlib import Path
from collections import defaultdict, Counter
from functools import cache
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
RESEARCH = ROOT/'Computability/BusyBeaver/Research/ZFC'
LEAN = ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
WORK = Path('/tmp/zfc-mp-literal-map')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

bi = load('par1_bisim', RESEARCH/'bisim254.py')
au = load('par1_audit', RESEARCH/'candidate252_independent_audit.py')
g = load('par1_closed_form', RESEARCH/'generate_l2_axioms_eval.py')
p, d = bi.load_prog254(), bi.load_dag254()
table = au.read_table((RESEARCH/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes())
assert sha(RESEARCH/'candidate-permutation252/zfc_permutation252_old.tm') == au.EXPECTED_SHA
pnodes, dcalls = {}, {}
def syntax(rows, node, path, parents, literal):
    if literal:
        pnodes[path] = node
    elif node == 166:
        dcalls[path] = parents
    for bit, edge in enumerate(rows[node]):
        if edge[0] == 'node':
            syntax(rows, edge[1], path+str(bit), parents+[(node,bit)], literal)
syntax(p,0,'',[],True)
syntax(d,0,'',[],False)

@cache
def shape(node):
    return tuple(shape(e[1]) if e[0]=='node' else tuple(e) for e in p[node])

literal_par1 = {path:node for path,node in pnodes.items() if shape(node)==shape(6434)}
assert len(dcalls) == len(literal_par1) == 31
ps, ds = bi.Prog(p), bi.Prog(d)
certificate = bi.build(ps,ds)
assert len(certificate)==3010
bits = lambda value: ''.join(str(int(x)) for x in value)
linked = defaultdict(set)
for index,(a,b,_,_) in enumerate(certificate):
    ea,qa = ps.tsite(a)
    eb,qb = ds.tsite(b)
    q = bits(qb)
    if eb==('decnz',1) and q.endswith('000') and q[:-3] in dcalls:
        root = bits(qa)[:-3]
        assert bits(qa).endswith('000') and root in literal_par1
        linked[q[:-3]].add((root,pnodes[root]))
assert set(linked)==set(dcalls) and all(len(v)==1 for v in linked.values())
assert len({next(iter(v))[1] for v in linked.values()})==31

# Exact direct decoder-prefix classification only. An earlier literal-engine
# shortcut is recorded explicitly; it is not guessed to be a decoder row.
def direct_entry(path):
    q, previous = 96, None
    for depth, bit in enumerate(path):
        action = table[q,int(bit)]
        if action[:2] != (int(bit),'R'):
            return dict(status='EARLIER_ENGINE_SHORTCUT_NOT_CLASSIFIED', prefix=path[:depth], row=[q,int(bit)], action=action)
        previous = [q,int(bit)]
        q = action[2]
    return dict(status='EXACT_PURE_DECODER_ENTRY',state=q,incoming_row=previous)

# Trace only checked AX macro definitions on symbolic records, preserving the
# terms at each call. This is finite source expression evaluation, not a run.
# The complete source syntax enters axioms() at this fixed prefix.
ax_root = '111010010010'
events = {}
def ax_effect(node, st, path):
    if node==166:
        events[path] = dict(top=g.show(st['tw']),stack=g.show(st['ws']),param1=g.show(st['p1']),caller=dcalls[ax_root+path][-1])
    if node in g.LEAVES:
        return g.macro(g.LEAVES[node], st)
    if node==35:
        return ax_effect(58,g.macro('readTw',st),path+'11')
    first,second=d[node]
    assert first[0]==second[0]=='node'
    return ax_effect(second[1],ax_effect(first[1],st,path+'0'),path+'1')
ax_effect(1,{field:('var','st.'+field) for field in g.FIELDS},'')
assert len(events)==29
ax_paths={ax_root+path for path in events}
assert ax_paths <= set(dcalls)
assert set(dcalls)-ax_paths == {'111100','1111111'}
rows=[]
for dag_path,parents in dcalls.items():
    prog_path,node=next(iter(linked[dag_path]))
    if dag_path in ax_paths:
        context=dict(kind='AX',**events[dag_path[len(ax_root):]])
    elif dag_path=='111100':
        context=dict(kind='MP_COMPARISON_CONSTRUCTION',top='st.tw (arbitrary A)',stack='st.ws',param1='st.p1 (requested B)',caller=[161,0])
    else:
        context=dict(kind='MP_SUCCESS_CONTINUATION',top='0',stack='st.ws',param1='st.p1 (requested B)',caller=[130,1])
    rows.append(dict(dag_path=dag_path,dag_caller=parents[-1],literal_path=prog_path,literal_node=node,context=context,binary_prefix=direct_entry(prog_path)))
direct=[row for row in rows if row['binary_prefix'].get('state')==113]
assert len(direct)==24
groups=Counter(tuple(row['binary_prefix']['incoming_row']) for row in direct)
assert groups=={(98,0):13,(175,0):2,(176,0):4,(236,1):4,(204,1):1}

P=lambda a,b:(a+b)*(a+b+1)//2+b
wim=lambda a,b:4*P(a,b)
wal=lambda i,a:4*P(i,a)+2
weq=lambda i,j:4*P(i,j)+3
assert wal(0,0)==2 and weq(0,0)==3 and wim(0,weq(0,0))==36
assert wim(2,1)==28 and wim(0,2+1)==36
paths=[RESEARCH/'bisim254.py',RESEARCH/'candidate252_independent_audit.py',RESEARCH/'generate_l2_axioms_eval.py',RESEARCH/'candidate-permutation252/zfc_permutation252_old.tm']+[LEAN/name for name in ['Dag254.lean','Prog254.lean','L2Lib254.lean','L2Macros254.lean','L2Control254.lean','L2Axioms254.lean','L2AxiomsEval254.lean','SeedInvariant254.lean','Enum254.lean','Code254.lean']]
result=dict(status='COMPLETE_SOURCE_CLASSIFICATION_GLOBAL_FAMILY_STOPPED',scope='Original-source syntax/certificate and direct prefix mapping only. No candidate table, mutant program run, search or Lean build.',driver=dict(path=str(Path(__file__)),sha256=sha(__file__)),source_inputs=[dict(path=str(path),sha256=sha(path))for path in paths],original_segment_pairs=len(certificate),dag_par1_occurrences=31,literal_matching_par1_subtrees=31,certificate_links_all31=True,AX_calls=29,MP_calls=2,occurrences=rows,direct113_entry_count=24,direct113_by_incoming=[dict(row=key,occurrences=value)for key,value in sorted(groups.items())],unclassified_earlier_engine_shortcuts=7,direct_mapping_limit='This partial pure-prefix traversal supplies exact representatives for all five incoming113 rows; it does not classify the seven earlier-engine contexts or prove deletion/global reroute equivalence.',node167_actual_clean_effect=dict(top='oldTW+oldParam1',stack='oldWS',param1='oldParam1',scratch1=0),obstruction=dict(input=dict(top=2,stack=0,d=0,cache=36,mp_argument=1),certified_input_sources=['SeedInvariant254.Formula.sound (.all 0 .truth) yields C254 2.','SeedInvariant254.Formula.sound (.weaken 0 (.eqRefl 0)) yields C254 36.','Enum254.good_zero gives Good 0.'],original_comparison=wim(2,1),global_skip_comparison=wim(0,2+1),old_result=dict(top=0,stack=0,d=1,cache=0),global_skip_result=dict(top=1,stack=0,d=1,cache=0),polarity='Unconditional operational disagreement. Failure of old derivability invariant follows conditionally on C254 F not derivable; semantic truth preservation fails in an appropriate IR model. No claim of modified blank halting.'),conclusion='MP-success-only bypass is justified by TW0. A global166→167 substitution changes AX operands and the earlier161 MP implication construction. No global candidate is warranted by local evidence.',lean_build=False,candidate_or_table_search=False,tracked_edits=False)
(WORK/'par1-contexts.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key]for key in ['status','original_segment_pairs','dag_par1_occurrences','AX_calls','MP_calls','direct113_entry_count','direct113_by_incoming','unclassified_earlier_engine_shortcuts','obstruction']},indent=2))

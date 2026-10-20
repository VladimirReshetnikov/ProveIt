#!/usr/bin/env python3
"""Deterministic K222 source and table reconstruction, without a search.
Finite source/decoder certificate only. The numerical-calculus audit and full
unbounded binary runtime certificate are separate required obligations.
"""
from pathlib import Path
from collections import defaultdict
from functools import cache
import argparse, hashlib, json, sys
import source_language as s
HERE=Path(__file__).resolve().parent
HALT=254
TARGET='11101001001110'
def need(x,message):
    if not x:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def read_table(raw):
    rows = {}
    starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        need((q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Bad table row')
        rows[q, b] = (w, 1 if d == 'R' else -1, target)
    need(starts == [0], 'Expected K-labelled start0')
    states = {q for q, b in rows}
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    need({t for w, d, t in rows.values()} - states == {HALT}, 'Unexpected terminal state')
    return rows


def table_bytes(rows, start=0):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {target}\n'
        for (q, b), (w, d, target) in sorted(rows.items()))).encode('ascii')


def decoder_map(table, tree):
    """Read every internal-node prefix using only its actual known tape bits.

    The caller must also compare the returned q/subtree relation to the intended
    relation. Merely reaching an arbitrary state is not sufficient validation.
    """
    groups = defaultdict(set)
    paths = defaultdict(list)
    def visit(node, prefix, state):
        if s.leaf(node):
            return
        groups[state].add(node); paths[state].append(prefix)
        for bit in (0, 1):
            if s.leaf(node[bit]):
                continue
            tape = {i: int(value) for i, value in enumerate(prefix + str(bit))}
            tape[-1] = 1
            before = tape.copy()
            head, q = len(prefix), state
            for tick in range(100):
                if head == len(prefix) + 1:
                    break
                need(head in tape, 'Decoder read outside known prefix')
                w, d, q = table[q, tape[head]]
                tape[head] = w; head += d
            need(tape == before and head == len(prefix) + 1, 'Decoder prefix changed or did not advance')
            visit(node[bit], prefix + str(bit), q)
    visit(tree, '', 84)
    return groups, paths


def sole(groups, state):
    need(len(groups[state]) == 1, 'Expected one represented subtree at ' + str(state))
    return next(iter(groups[state]))


def closed_chunks(tree, first, last):
    result = []
    def visit(node, start):
        end = start + len(s.sites(node))
        if end <= first or start >= last:
            return
        if first <= start and end <= last:
            need(s.boundary(node) == (0, 0, False), 'Cut chunk is not closed')
            result.append(node); return
        need(not s.leaf(node), 'Cut does not align to instructions')
        visit(node[0], start)
        visit(node[1], start + len(s.sites(node[0])))
    visit(tree, 0)
    return result


def sequence(nodes):
    need(bool(nodes), 'Empty sequence')
    result = nodes[-1]
    for node in reversed(nodes[:-1]):
        result = node, result
    return result


@cache
def flat(n):return (n,) if s.leaf(n) else flat(n[0])+flat(n[1])
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    need(__debug__ and not sys.flags.optimize,'Assertions must remain enabled')
    meta=json.loads((HERE/'recipe.json').read_text())
    for name,digest in meta['input_sha256'].items():need(sha((HERE/name).read_bytes())==digest,'Input differs: '+name)
    oldtree=s.tree(json.loads((HERE/'inputs/sites224.json').read_text()))
    parent=read_table((HERE/'inputs/parent225.k.tm').read_bytes())
    groups,paths=decoder_map(parent,oldtree);q=lambda n:sole(groups,n)
    inc=('CI',1);imp=q(90);neg=q(184)
    macros={166:q(98),121:q(12),168:q(166),177:neg[0],119:imp,
            180:(imp,(inc,inc)),181:(imp,inc),182:(imp,((inc,inc),inc)),218:neg}
    need(neg==(macros[177],imp),'Negation contract shape differs')
    tokens={m:[n]for m,n in macros.items()}
    for m in(166,121,168):tokens[m]=list(macros[m])
    tokens.update({180:[imp,inc,inc],181:[imp,inc],182:[imp,inc,inc,inc],218:[macros[177],imp]})
    need(all(s.boundary(t)==(0,0,False)for ts in tokens.values()for t in ts),'Open emitted macro piece')
    spec=json.loads((HERE/'inputs/grammar_seed.json').read_text())
    word=spec['macro_word'];need(len(word)==77,'Witness word census')
    # Root seed bundle is N(I(rv,I(H,Kseed))). Remove H's exact eleven
    # postfix macros and its consuming implication; no other word changes.
    removed=set(range(9,20))|{74}
    need(word[9:20]==[166,121,182,166,121,181,166,121,182,180,119] and word[74]==119,'Helper interval differs')
    ax=s.subtree(oldtree,TARGET)
    units=closed_chunks(ax,0,1893)+sum((tokens[m]for m in word),[])+closed_chunks(ax,3970,4004)
    need(len(units)==len(spec['units'])==164,'Grammar unit count differs')
    for unit,record in zip(units,spec['units']):
        need(len(s.sites(unit))==record['leaves'] and sha(s.compact(s.sites(unit)))==record['source_sha256'],'Grammar unit pin differs')
    removed_units=set();idx=6
    for i,m in enumerate(word):
        if i in removed:removed_units.update(range(idx,idx+len(tokens[m])))
        idx+=len(tokens[m])
    need(idx==162 and len(removed_units)==27,'Deleted unit count differs')
    seen=[]
    def prune(pattern):
        if type(pattern)is int:
            need(pattern==len(seen),'Grammar changes unit order');seen.append(pattern)
            return None if pattern in removed_units else units[pattern]
        need(isinstance(pattern,list)and len(pattern)==2,'Malformed grammar')
        a,b=map(prune,pattern)
        return b if a is None else a if b is None else(a,b)
    newax=prune(spec['pattern']);need(seen==list(range(164)),'Grammar drops units')
    stage1=s.replace(oldtree,TARGET,newax)
    # Upgrade rho7: retain its Eq(c,b) final increments and insert
    # Rel(a,b), Eq(a,b), All. The G certificate establishes exact deduction.
    pair_inc,rel,eq,all_=q(99),q(155),q(182),q(86)
    need(flat(stage1)[648:732]==flat((pair_inc,eq)),'Rho7 interval differs')
    replacement=((pair_inc,(rel,eq)),all_)
    need(all(s.boundary(x)==(0,0,False)for x in(pair_inc,rel,eq,all_)),'Open G macro')
    def cut(n,pos=0):
        end=pos+len(flat(n))
        if 732<=pos or end<=648:return n
        if 648<=pos and end<=732:return replacement if pos==648 else None
        a=cut(n[0],pos);b=cut(n[1],pos+len(flat(n[0])))
        return b if a is None else a if b is None else(a,b)
    stage2=cut(stage1)
    path=meta['rotation_path'];n=s.subtree(stage2,path)
    need(not s.leaf(n)and not s.leaf(n[0]),'Rotation pattern differs')
    a,b=n[0];d=n[1]
    need(all(s.boundary(x)==(0,0,False)for x in(a,b,d)),'Rotation factor is open')
    final=s.replace(stage2,path,(a,(b,d)))
    need(flat(stage2)==flat(final),'Rotation changes primitive word')
    cfg2,check2=s.graph_arithmetic(s.sites(stage2));cfg3,check3=s.graph_arithmetic(s.sites(final))
    need(cfg2==cfg3==s.graph_intervals(s.sites(stage2))==s.graph_intervals(s.sites(final)),'Rotation changes CFG')
    raw=s.compact(s.sites(final));need(sha(raw)==meta['source_sha256'],'Reconstructed source differs')
    need(s.metrics(final)==dict(dag_nodes=208,leaf_occurrences=4744,maximum_depth=36,maximum_zero_run=6),'Source census differs')
    baseline=read_table((HERE/'inputs/baseline224.k.tm').read_bytes())
    delta=json.loads((HERE/'inputs/table_delta.json').read_text())
    table={k:v for k,v in baseline.items()if k[0]not in delta['drop']}
    need(delta['drop']==[219,226] and len(delta['rows'])==49,'Table delta census differs')
    for q0,b0,w,d,z in delta['rows']:
        need(q0 not in delta['drop'] and b0 in(0,1)and w in(0,1)and d in(-1,1),'Invalid changed row')
        table[q0,b0]=(w,d,z)
    encoded=table_bytes(table);need(sha(encoded)==meta['table_sha256'],'Reconstructed table differs')
    read_table(encoded);need(len(table)==444,'Table state count differs')
    # Every source-prefix decoder run must reach its intended complete subtree.
    # This covers contextual shared states, not just direct-right rows.
    actual,prefixes=decoder_map(table,final)
    assignment=json.loads((HERE/'inputs/node_assignment.json').read_text())
    got={sha(s.compact(s.sites(n))):q0 for q0,ns in actual.items()for n in ns}
    need(got==assignment,'Intended subtree/state relation differs')
    reachable={0};todo=[0]
    for state in todo:
        for bit in(0,1):
            z=table[state,bit][2]
            if z!=HALT and z not in reachable:reachable.add(z);todo.append(z)
    need(reachable=={q0 for q0,b in table},'Unreachable declared state')
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'sites.json').write_bytes(raw);(args.output/'candidate222.k.tm').write_bytes(encoded)
    receipt=dict(status='EXACT_K222_SOURCE_TABLE_RECONSTRUCTION_PASS',source_sha256=sha(raw),table_sha256=sha(encoded),
        source_metrics=s.metrics(final),working_states=len(table)//2,rows=len(table),
        removed_helper_macro_indices=sorted(removed),removed_helper_unit_indices=sorted(removed_units),
        rotation=dict(path=path,direction='right',all_factors_closed=True,primitive_word_equal=True,guarded_cfg_equal=True,independent_resolvers_agree=True,cases_before=check2,cases_after=check3),
        table_delta=dict(deleted_k_states=delta['drop'],changed_retained_rows=len(delta['rows'])),
        decoder=dict(states=len(actual),subtrees=sum(map(len,actual.values())),contextual_alias_savings=sum(len(v)-1 for v in actual.values()),compound_prefixes=sum(map(len,prefixes.values())),intended_relation_checked=True),
        proof_boundary='Deterministic finite reconstruction and source/decoder relation. Exact emitter/calculus calibration, blank startup, and unbounded instruction simulation are separate obligations.')
    dump(args.output/'construction_receipt.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

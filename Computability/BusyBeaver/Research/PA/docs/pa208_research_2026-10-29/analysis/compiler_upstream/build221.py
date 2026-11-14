#!/usr/bin/env python3
"""Deterministic three closed source rotations and one exact tag-sharing fold.
No source optimizer or annealing trace is used. Runtime is a separate obligation.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json,hashlib,sys
import source_language as s
HERE=Path(__file__).resolve().parent
HALT=254
def need(x,m):
 if not x:raise ValueError(m)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
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



def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Assertions required')
 base=a.baseline
 table_raw=(base/'machine/k222.native.tm').read_bytes();source_raw=(base/'machine/sites222.json').read_bytes()
 need(sha(table_raw)=='a85b0baf596c5559581344d02b0fb263f97dda2f9a0781f6c7e651cd236fd818','Baseline table')
 need(sha(source_raw)=='cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e','Baseline source')
 T=read_table(table_raw);tree=s.tree(json.loads(source_raw));oldcfg,_=s.graph_arithmetic(s.sites(tree));oldword=[x[1:]for x in s.sites(tree)];steps=[]
 for item in json.loads((HERE/'inputs/explicit_rotations.json').read_text()):
  need(item['direction']=='left' and item['kind']=='rewrite' and item['r']==item['s'] and len(item['source_paths'])==1,'Unexpected rotation recipe')
  q,r=item['q'],item['r'];path=item['source_paths'][0];n=s.subtree(tree,path)
  need(not s.leaf(n) and not s.leaf(n[1]),'Expected A,(B,C)')
  A,(B,C)=n
  need(all(s.boundary(x)==(0,0,False)for x in(A,B,C)),'Rotation factor not closed')
  groups,prefixes=decoder_map(T,tree);need(sole(groups,q)==n and sole(groups,r)==n[1] and prefixes[q]==[path],'Source and physical rotation mismatch')
  need(all(T[state,b][:2]==(b,1)for state in(q,r)for b in(0,1)) and T[q,1][2]==r,'Nonpure rotation')
  qa,rb,rc=T[q,0][2],T[r,0][2],T[r,1][2]
  T[q,0]=(0,1,r);T[q,1]=(1,1,rc);T[r,0]=(0,1,qa);T[r,1]=(1,1,rb)
  tree=s.replace(tree,path,((A,B),C));rows=s.sites(tree);cfg,_=s.graph_arithmetic(rows)
  need([x[1:]for x in rows]==oldword and cfg==oldcfg==s.graph_intervals(rows),'Rotation changes source semantics')
  decoder_map(T,tree);steps.append(dict(**item,primitive_word_equal=True,guarded_CFG_equal=True,all_factors_closed=True))
 prefold=table_bytes(T)
 need(T[172,1]==T[192,1],'Direct folded branch differs')
 T={(q,b):(w,d,172 if z==192 else z)for(q,b),(w,d,z)in T.items()if q!=192};T[172,0]=(0,-1,112)
 raw=table_bytes(T);src=s.compact(s.sites(tree))
 need(sha(raw)=='e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc','Final table hash')
 need(sha(src)=='691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9','Final source hash')
 read_table(raw);need(len(T)==442,'Exact221 state census');groups,prefixes=decoder_map(T,tree)
 need(s.metrics(tree)==dict(dag_nodes=208,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6),'Final source census')
 out=a.output;out.mkdir(parents=True,exist_ok=True)
 for name,data in [('candidate.tm',raw),('candidate221.k.tm',raw),('prefold.tm',prefold),('sites.json',src),('allocation.json',(HERE/'inputs/allocation.json').read_bytes())]:(out/name).write_bytes(data)
 receipt=dict(status='EXACT_K221_RECONSTRUCTION_PASS',native_sha256=sha(raw),source_sha256=sha(src),prefold_sha256=sha(prefold),working_states=221,rows=442,source_metrics=s.metrics(tree),rotations=steps,fold=dict(keep=172,drop=192,read0_helper=112,read1='direct'),decoder=dict(states=len(groups),subtrees=sum(map(len,groups.values())),aliases=sum(len(ns)-1 for ns in groups.values())),scope='Deterministic finite construction and source/decoder relation; exact runtime and fold induction separately replayed.')
 dump(out/'construction_receipt.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""General decoder rotations with exact leaf-CFG re-encoding.

Research diagnostic: preserve each leaf's instruction effect and successor leaf
index, including both decrement outcomes. Re-encode break/continue depth after
rotation instead of requiring every moved fragment to be closed. A complete
affine TM check and fresh startup are additional requirements for a candidate.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, json, sys, time, importlib.util, hashlib

HERE = Path(__file__).resolve().parent
MACHINE = HERE.parent / 'agents/machine_reduction'
sys.path.insert(0, str(MACHINE))
import rotation_search252 as r
import check_rotation252 as c


def leaves(nodes, root):
    out = []
    prefixes = {}
    def walk(e, p):
        prefixes[p] = len(out)
        if e[0] != 'N':
            out.append((p, e))
        else:
            for b, child in enumerate(nodes[e[1]]):
                walk(child, p + str(b))
    walk(('N', root), '')
    return out, prefixes


def graph(nodes, root):
    ls, ix = leaves(nodes, root)
    ix[None] = 0  # program-counter overflow restarts main at a new marker
    out = []
    for p, e in ls:
        if e[0] == 'H': out.append(('H',)); continue
        if e[0] == 'D':
            out.append(('D', e[1], ix[c.audit.successor(p, 'CD', e[1], True)],
                        ix[c.audit.successor(p, 'CD', e[1], False)]))
        elif e[0] == 'I':
            out.append(('I', e[1], ix[c.audit.successor(p, 'CI', e[1], None)]))
        else:
            out.append(('J', ix[c.audit.successor(p, 'C' + e[0], e[1], None)]))
    return out


def rebase(nodes, root, reference, *, choose='old'):
    ls, ix = leaves(nodes, root)
    ix[None] = 0
    if len(ls) != len(reference): return None
    replacement = {}
    changes = 0
    ambiguity = 0
    for i, (p, e) in enumerate(ls):
        wanted = reference[i]
        if e[0] in 'BC':
            choices = []
            for (ee, bit), counts in r.CONTROL_OPTIONS.items():
                if bit != int(p[-1]): continue
                if ix[c.audit.successor(p, 'C' + ee[0], ee[1], None)] == wanted[1]:
                    choices.append(ee)
            if not choices: return None
            choices = sorted(set(choices), key=lambda x: (x != e, x[1], x[0]))
            if len(choices) > 1: ambiguity += 1
            replacement[p] = choices[0]
            changes += choices[0] != e
        elif e[0] == 'D':
            got = ('D', e[1], ix[c.audit.successor(p, 'CD', e[1], True)],
                   ix[c.audit.successor(p, 'CD', e[1], False)])
            if got != wanted: return None
        elif e[0] == 'I':
            if ('I', e[1], ix[c.audit.successor(p, 'CI', e[1], None)]) != wanted:
                return None
        elif wanted != ('H',): return None
    seen, new = {}, {}
    def visit(e, p):
        if e[0] != 'N': return replacement.get(p, e)
        a, b = nodes[e[1]]
        pair = (visit(a, p+'0'), visit(b, p+'1'))
        if pair not in seen:
            seen[pair] = len(new); new[len(new)] = pair
        return ('N', seen[pair])
    nr = visit(('N', root), '')[1]
    assert graph(new, nr) == reference
    return new, nr, changes, ambiguity


def all_rotations(nodes):
    out = []
    for n, (x, y) in nodes.items():
        if x[0] == 'N':
            a, b = nodes[x[1]]
            out.append((n, ('T', a, ('T', b, y)), 'right'))
        if y[0] == 'N':
            b, cc = nodes[y[1]]
            out.append((n, ('T', ('T', x, b), cc), 'left'))
    return out


def setup(cache=False):
    if not cache: return
    old = json.loads((MACHINE/'mp-cache-decoder-entries.json').read_text())
    r.OLD = old
    r.NODES = {int(k): tuple(map(tuple,v)) for k,v in old['nodes'].items()}
    r.ROOT = old['root']
    r.OLD_FP = {v:int(n) for n,v in old['fingerprints'].items()}
    table = {}
    for line in (MACHINE/'rotation-candidates/mp-cache-permuted252.tm').read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,t=line.split();table[q,int(b)] = int(w),d,t
    r.BASE = table
    r.NEWPHYS = (4,5,0,8,6,2,1,7,3)
    r.CONTROL_OPTIONS = {}
    for n,pair in r.NODES.items():
        for bit,e in enumerate(pair):
            if e[0] not in 'BC':continue
            counts=r.CONTROL_OPTIONS.setdefault((e,bit),Counter())
            for state,weight in r.OLD['state_entries'][str(n)].items():
                counts[r.BASE[state,bit]] += weight


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', action='store_true')
    ap.add_argument('--output',type=Path,default=HERE/'control-rebased-rotations.json')
    a=ap.parse_args();setup(a.cache)
    nodes, root=r.NODES,r.ROOT
    reference=graph(nodes,root);begin=time.monotonic();counts=Counter();results=[];best=252
    outdir=HERE/'control-rebased-candidates';outdir.mkdir(exist_ok=True)
    closed={(n,k) for n,e,k in r.options(nodes)}
    for index,(n,exp,kind) in enumerate(all_rotations(nodes)):
        nn,nr=r.mutate(nodes,root,n,exp)
        fixed=rebase(nn,nr,reference)
        if fixed is None: counts['not_representable']+=1;continue
        nn,nr,changes,ambiguity=fixed
        metrics=r.metrics(nn,nr)
        if metrics[1]>7 or metrics[2]>39:
            counts['code_bound']+=1;continue
        try:table=r.gc(r.emit(nn,nr))
        except KeyError: counts['no_control_encoding']+=1;continue
        cost=len(table)//2;counts[str(cost)]+=1
        row={'index':index,'node':n,'direction':kind,'old_closed':(n,kind) in closed,
             'control_changes':changes,'ambiguous_leaves':ambiguity,'nodes':len(nn),
             'states':cost,'zero_run':metrics[1],'depth':metrics[2]}
        if cost<=252:
            result=c.run(table,nn,nr,stop=True)
            row['affine_cases_checked']=result['cases_checked'];row['failures']=result['failures']
        if cost<=252 and not row['failures']:
            stem=f"{'cache' if a.cache else 'original'}-{index}-{cost}"
            (outdir/(stem+'.json')).write_text(json.dumps({'nodes':nn,'root':nr,'rotation':row},indent=2)+'\n')
            start=0 if a.cache else 64
            (outdir/(stem+'.tm')).write_text(f'#! start {start}\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
            row['candidate']=stem
            if cost<best: best=cost;print('BEST',row,flush=True)
        results.append(row)
    data={'cache_mp':a.cache,'tested':sum(counts.values()),'counts':counts,'best_states':best,
          'results':results,'elapsed_seconds':time.monotonic()-begin,
          'scope':'All global single binary rotations of the selected 203-node decoder, with exact leaf-CFG preservation after re-encoding existing break/continue leaves. Finite structural and conditional affine checks; no bootstrap implied.'}
    a.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='results'},indent=2))


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Replay finite QH6 reduction searches; no state-count lower bound follows."""
from pathlib import Path
from collections import defaultdict
import argparse,hashlib,itertools,json,time,subprocess,tempfile
from common import load
HERE=Path(__file__).resolve().parent
def whole_contract_merges(root):
    c, rows, sites, ins, contracts, digest = load(root)
    visits, tests = defaultdict(set), defaultdict(list)
    for index, contract in enumerate(contracts):
        local = set()
        assert c.run(rows, contract, observe=lambda s: local.add(
            (s[0], c.headbit(s[2] if s[1] else s[3])))) is not None
        for q, bit in local:
            visits[q].add(index)
            tests[q, bit].append(index)
    controls = sorted({q for q, _ in rows})
    removable = [q for q in controls if q not in c.BOXSTATES]
    trials, survivors = 0, []
    started = time.monotonic()
    for a in removable:
        for b in controls:
            if a == b or (a > b and b not in c.BOXSTATES):
                continue
            choices = ([(1, 1)] if b in c.BOXSTATES else
                       list(itertools.product((0, 1), repeat=2)))
            for choice in choices:
                patch = {bit: rows[a if choice[bit] == 0 else b, bit]
                         for bit in (0, 1)}
                affected = visits[a] | visits[b]
                order = []
                for q in (a, b):
                    for bit in (0, 1, None):
                        indices = tests.get((q, bit), [])
                        if indices:
                            order += [indices[0], indices[-1],
                                      indices[len(indices) // 2]]
                order = list(dict.fromkeys(order)) + sorted(affected - set(order))
                changed = {}
                for (q, bit), (w, d, nxt) in rows.items():
                    if q == a:
                        continue
                    if q == b:
                        w, d, nxt = patch[bit]
                    changed[q, bit] = w, d, b if nxt == a else nxt
                trials += 1
                for index in order:
                    try:
                        closed = c.run(changed, contracts[index], fuel=1024)
                    except KeyError:
                        closed = None
                    if closed is None:
                        break
                else:
                    result = c.validate(changed, contracts)
                    if result['ok']:
                        survivors.append({'remove': a, 'keep': b,
                                          'rows': choice, 'validation': result})
    assert trials == 62073
    return {'input': 'PA194QH6', 'native_sha256': digest, 'trials': trials,
            'survivors': survivors, 'symbolic_fuel_bound': 1024,
            'seconds': time.monotonic() - started}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package-root',type=Path,default=HERE.parents[1])
    ap.add_argument('--output',type=Path)
    ap.add_argument('--whole-merges',action='store_true')
    ap.add_argument('--derive-contexts',action='store_true')
    args=ap.parse_args();root=args.package_root.resolve();out=args.output or Path(tempfile.mkdtemp(prefix='qh6-reductions-'));out.mkdir(parents=True,exist_ok=True)
    expected='6ee047dc2d01faf550e83f40c85b5ac50a74c1699f15211e329047e51d979a4b'
    c,rows,sites,ins,contracts,digest=load(root);assert digest==expected
    baseline=c.validate(rows,contracts);assert baseline['ok'] and baseline['contracts']==4876
    if args.derive_contexts:
        for script in ['derive_contexts.py','derive_literal_contexts.py']:
            subprocess.run(['python3',str(HERE/script),'--package-root',str(root),'--output',str(out)],check=True)
        for name in ['QH6-contexts-k5.txt','QH6-all-contexts-k5.txt']:
            assert(out/name).read_bytes()==(HERE/'recorded'/name).read_bytes(),name
    runs=[]
    for name in ['action_merge_future','eliminate','action_merge_start']:
        binary=out/name
        subprocess.run(['g++','-O3','-std=c++17',str(HERE/'src'/f'{name}.cpp'),'-o',str(binary)],check=True)
        contexts=['QH6-all-contexts-k5.txt']if name=='action_merge_start'else['QH6-contexts-k5.txt','QH6-all-contexts-k5.txt']
        for context in contexts:
            tag=f'{name}-{context}';st=time.monotonic()
            with(out/f'{tag}.jsonl').open('w')as log,(out/f'{tag}.log').open('w')as err:
                subprocess.run([str(binary),str(root/'machine/machine.native.tm'),'5','150',str(HERE/'recorded'/context)],stdout=log,stderr=err,check=True)
            hits=(out/f'{tag}.jsonl').read_text().splitlines();runs.append(dict(search=name,context=context,radius=5,step_bound=150,hits=hits,seconds=time.monotonic()-st))
    result=dict(native_sha256=digest,baseline=baseline,runs=runs)
    if args.whole_merges:result['whole_contract_merges']=whole_contract_merges(root)
    (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));print('Results:',out)

#!/usr/bin/env python3
"""Construct the exact 229-, 228-, 227- and 226-state ports from pinned K230.

Python 3.10+ standard library, with assertions enabled. This builder establishes
literal provenance and state census; verification/reproduce.py establishes the
separate source, startup, local-block, and unbounded-runtime obligations.
"""
from pathlib import Path
import argparse, hashlib, json, sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'vendor/proveit'))
import build_zfc235 as source

PINS = {
    'vendor/k230-rocq/machine/k230.tm': 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8',
    'vendor/k230-rocq/machine/sites230.json': '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487',
    'vendor/k230-rocq/manifest.json': 'bbd4694416cef144c8cad8099148a08c5a81114a81e358ad3f0d2dd5cdea6119',
    'source/legacy_state_map.json': '8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151',
    'vendor/proveit/build_zfc235.py': '3184f98cb7d86a6688165aa19b5e715db5fa3facf4eabd6d0ecd88d54df9a75a',
    'verification/reconstruct227.py': 'd89bd9143210c1637712ad06831bf77b8ce3c18bd682fd57676fa85169e0a700',
    'verification/construction227.json': '10ca22b2c227e38a85b34b0fe6e785f7b00b210c2fc3e71414d5f69bd682f0b5',
    'verification/reconstruct226.py': 'ad6fe2c338375f01e5bb23970e06b0a26f82f9b8d724b1d63cffd4f38bcb54d1',
}
OLD = ((('CD', 6), (('CI', 5), ('CC', 2))), ('CI', 5))
NEW = (('CI', 5), (('CD', 6), ('CC', 2)))
ROOTS = ['111010010010111111000011', '11101001001011111110011',
         '1110100101100011', '111110011']
EXPECTED = {
    'rotated230_old.tm': '7782cb2d9666e4796d3968a70f8b0d650b5e71c1eb0cbe0b1f429f9b3f468aad',
    'k229_old.tm': 'b110a172b557f5a1bb42f53b3d82f3d6443b0e99626f61ad457b64d4a88d793d',
    'k228_old.tm': 'b51892325a6f179ae27d5178c56598213c3463c4ff1f66aae953f3f8a192bf4d',
}

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2) + '\n')

def parse(data, start, halt):
    table = {}; starts = []
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        require((q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R'), 'Malformed row')
        table[q,b] = (w, 1 if d == 'R' else -1, z)
    states = {q for q,b in table}
    require(starts == [start], 'Wrong start')
    require(start in states and halt not in states, 'Start or halt census')
    require(set(table) == {(q,b) for q in states for b in (0,1)}, 'Partial table')
    require({z for w,d,z in table.values()} - states == {halt}, 'Wrong halt')
    return table

def canonical(table, legacy_to_k):
    states = {q for q,b in table}
    ordered = [95] + sorted(states - {95}, key=lambda q: legacy_to_k.get(q, 1000000 + q))
    mapping = {q:i for i,q in enumerate(ordered)}
    mapping[254] = len(states)
    result = {(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in table.items()}
    return source.encode(result, start=0), mapping

def changes(old, new):
    return [{'row':list(k), 'before':old.get(k), 'after':new.get(k)}
            for k in sorted(set(old) | set(new)) if old.get(k) != new.get(k)]

def construct(output):
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    for name, digest in PINS.items():
        require(sha((ROOT/name).read_bytes()) == digest, 'Pinned input mismatch: ' + name)
    mapping_record = json.loads((ROOT/'source/legacy_state_map.json').read_text())
    m = {int(k):v for k,v in mapping_record['k230_to_old'].items()}
    mi = {int(k):v for k,v in mapping_record['old_to_k230'].items()}
    require(set(m) == set(range(231)) and len(set(m.values())) == 231, 'Renaming is not a bijection')
    require({v:k for k,v in m.items()} == mi and m[0] == 95 and m[230] == 254, 'Wrong inverse, start, or halt')
    K = parse((ROOT/'vendor/k230-rocq/machine/k230.tm').read_bytes(), 0, 230)
    require(len(K) == 460, 'K230 census')
    T = {(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in K.items()}
    aliases = {'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
    sites = []
    for p, instruction in json.loads((ROOT/'vendor/k230-rocq/machine/sites230.json').read_text()):
        parts = instruction.split(); op = aliases[parts[0]]
        require(len(parts) == (1 if op == 'CH' else 2), 'Bad source instruction')
        sites.append([p, op, None if op == 'CH' else int(parts[1])])
    root = source.tree(sites); roots = []
    def rewrite(t, path=''):
        if t == OLD:
            roots.append(path); return NEW
        return t if source.is_leaf(t) else (rewrite(t[0],path+'0'),rewrite(t[1],path+'1'))
    newroot = rewrite(root)
    require(roots == ROOTS, 'Unexpected rewrite occurrences')
    altered = source.sites(newroot)
    require(len(sites) == 5125 and len(altered) == 5121, 'Source census')
    altered_bytes = source.json_bytes(altered, compact=True)
    require(sha(altered_bytes) == '61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b', 'Altered source mismatch')
    R = dict(T)
    require(R[142,0] == (0,1,37) and R[142,1] == (1,1,72), 'Rotation ports changed')
    R[142,0] = (0,1,72); R[142,1] = (1,1,17)
    U = {(q,b):(w,d,72 if z == 90 else z) for (q,b),(w,d,z) in R.items() if q != 90}
    U[72,0] = (0,-1,144); U[72,1] = (1,-1,36)
    V = {(q,b):(w,d,80 if z == 169 else z) for (q,b),(w,d,z) in U.items() if q != 169}
    V[80,0] = (0,-1,106); V[91,1] = (1,-1,167)
    for folder in ('machines','source','evidence'):
        (output/folder).mkdir(parents=True, exist_ok=True)
    (output/'source/sites230.json').write_bytes(source.json_bytes(sites, compact=True))
    (output/'source/sites229.json').write_bytes(altered_bytes)
    artifacts = {}
    for name, table in [('k230_old.tm',T),('rotated230_old.tm',R),('k229_old.tm',U),('k228_old.tm',V)]:
        raw = source.encode(table)
        if name in EXPECTED:
            require(sha(raw) == EXPECTED[name], 'Unexpected construction output: ' + name)
        (output/'machines'/name).write_bytes(raw)
        artifacts['machines/'+name] = {'sha256':sha(raw), 'working_states':len(table)//2}
    for n, table in [(229,U),(228,V)]:
        raw, cm = canonical(table, mi)
        require(len(parse(raw, 0, n)) == 2*n, 'Canonical state census')
        (output/f'machines/k{n}.tm').write_bytes(raw)
        artifacts[f'machines/k{n}.tm'] = {'sha256':sha(raw), 'working_states':n, 'start':0, 'halt':n}
        dump(output/f'machines/k{n}_state_map.json', {
            'legacy_to_canonical':cm, 'canonical_to_legacy':{v:k for k,v in cm.items()},
            'retained_original_K230_states':{mi[q]:cm[q] for q in cm if q in mi},
            'deleted_original_K230_states':sorted(mi[q] for q in set(mi)-set(cm))})
    # The K-specific source-boundary port has a separate literal recipe and
    # two independently implemented source graph checks at every stage.
    sys.path.insert(0, str(ROOT/'verification'))
    import reconstruct227
    boundary_receipt = reconstruct227.construct(output/'machines/k229_old.tm',
        output/'source/sites229.json', ROOT/'verification/construction227.json', output/'boundary')
    for a,name in [('basis229.tm','boundary229_old.tm'),('candidate228.tm','boundary228_old.tm'),('candidate227.tm','k227_old.tm')]:
        raw = (output/'boundary'/a).read_bytes()
        (output/'machines'/name).write_bytes(raw)
        artifacts['machines/'+name] = {'sha256':sha(raw),'working_states':len(parse(raw,95,254))//2}
    (output/'source/sites227.json').write_bytes((output/'boundary/sites.json').read_bytes())
    raw, cm = canonical(parse((output/'machines/k227_old.tm').read_bytes(),95,254), mi)
    require(sha(raw)=='d99c2aaed592a3c449007ca1c02bff4c362085ed9d59bc0c2f6a2f9dd9949bc9','Canonical K227 mismatch')
    (output/'machines/k227.tm').write_bytes(raw)
    artifacts['machines/k227.tm'] = {'sha256':sha(raw),'working_states':227,'start':0,'halt':227}
    dump(output/'machines/k227_state_map.json',{
        'legacy_to_canonical':cm,'canonical_to_legacy':{v:k for k,v in cm.items()},
        'retained_original_K230_states':{mi[q]:cm[q] for q in cm if q in mi},
        'deleted_original_K230_states':sorted(mi[q] for q in set(mi)-set(cm))})
    import reconstruct226
    extension_receipt = reconstruct226.construct(output/'machines/k227_old.tm',
        output/'source/sites227.json',output/'extension226')
    raw = (output/'extension226/candidate226.tm').read_bytes()
    (output/'machines/k226_old.tm').write_bytes(raw)
    artifacts['machines/k226_old.tm']={'sha256':sha(raw),'working_states':226}
    (output/'source/sites226.json').write_bytes((output/'extension226/sites226.json').read_bytes())
    raw, cm = canonical(parse(raw,95,254),mi)
    require(len(parse(raw,0,226))==452,'Canonical K226 census')
    (output/'machines/k226.tm').write_bytes(raw)
    artifacts['machines/k226.tm']={'sha256':sha(raw),'working_states':226,'start':0,'halt':226}
    dump(output/'machines/k226_state_map.json',{
        'legacy_to_canonical':cm,'canonical_to_legacy':{v:k for k,v in cm.items()},
        'retained_original_K230_states':{mi[q]:cm[q] for q in cm if q in mi},
        'deleted_original_K230_states':sorted(mi[q] for q in set(mi)-set(cm))})
    record = {
        'status':'EXACT_CONSTRUCTION_PASS', 'pinned_inputs':PINS,
        'upstream_commit':'3142e4dd980f0be12f4abb636c4ae2528afc17eb',
        'provenance_commit':'0128d662fd46f72dc84505176ae8ec28affb2d9d',
        'source_rewrite':{'before':OLD,'after':NEW,'occurrences':roots,
                          'old_metrics':source.metrics(root),'new_metrics':source.metrics(newroot)},
        'stages':[{'name':'loop source port','states':230,'edits':changes(T,R)},
                  {'name':'context fold 90 into 72','states':229,'edits':changes(R,U)},
                  {'name':'delayed erasure 169 into 80','states':228,'edits':changes(U,V)}],
        'boundary_port':boundary_receipt,
        'extension226':extension_receipt,
        'principal_working_states':226,
        'artifacts':artifacts,
        'proof_scope':'Exact construction only. Source and runtime equivalence are separate proof obligations.'}
    dump(output/'evidence/construction.json',record)
    return record

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,default=ROOT)
    args = ap.parse_args()
    result = construct(args.output_dir)
    print(json.dumps({'status':result['status'],'artifacts':result['artifacts']},indent=2))

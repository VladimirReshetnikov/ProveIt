from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-source-selection-plan')
base=Path('research/ordinary13-fixed85-native-composition-draft')
sign=Path('research/ordinary13-signfree-omega-repair-draft')
haz=Path('research/ordinary13-fixed85-omega-hazards-draft')
# Pin the prior local-source inventory and alternative receipts. This plan
# does not open or test any external package or compiled provider.
checks={
 str(base/'manifest.json'):'a4934426329ffedef443a7b6a95bd5fd09d5210c8c9014fb522deed82e65c05e',
 str(sign/'receipt.json'):'f4c5e09a898c99c486f49581e99c69cee1f5425e97e1c28dbd1ac1f6502a0013',
 str(haz/'receipt.json'):'b7f47bd5ab6666a04e7d9dead9217616a613d11ec8fa5fc4c1033ae1e56437b7'}
for file,digest in checks.items():assert sha256(Path(file).read_bytes()).hexdigest()==digest,file
manifest=json.loads((base/'manifest.json').read_text())
signreceipt=json.loads((sign/'receipt.json').read_text())
hazreceipt=json.loads((haz/'receipt.json').read_text())
old=manifest['local_modules']
alt={n:(Path(r['alternative']),r['alternative_sha256']) for n,r in hazreceipt['repaired_alternatives'].items()}
alt['ResidueSignFreePower']=(sign/'ResidueSignFreePowerRepaired.lean.src',
    signreceipt['sha256'][str(sign/'ResidueSignFreePowerRepaired.lean.src')])
assert len(alt)==9 and all(n in old for n in alt)
selected={};frontier=set();queue=['Fixed85Endpoint'];edges={};overrides={}
while queue:
    name=queue.pop()
    if name in selected or name in frontier:continue
    if name not in old:
        frontier.add(name);continue
    orig=old[name];path=Path(orig['path']);digest=orig['sha256']
    assert sha256(path.read_bytes()).hexdigest()==digest,name
    if name in alt:
        path,digest=alt[name]
        assert sha256(path.read_bytes()).hexdigest()==digest,name
        overrides[name]={'previous_path':orig['path'],'previous_sha256':orig['sha256'],
            'alternative_path':str(path),'alternative_sha256':digest}
    imports=[]
    for line in path.read_text().splitlines():
        match=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$',line)
        if match:imports.extend(match.group(1).split())
    if name in alt:
        added=set(imports)-set(orig['imports']);removed=set(orig['imports'])-set(imports)
        assert added <= {'Mathlib.Tactic.NormNum','Mathlib.Tactic.Ring'},(name,added)
        assert removed <= {'Mathlib.Tactic.Omega'},(name,removed)
    virtual='/'.join(name.split('.'))+'.lean'
    selected[name]={'source_path':str(path),'sha256':digest,'virtual_logical_path':virtual,
                    'imports':imports,'alternative':name in alt}
    edges[name]=imports;queue.extend(imports)
assert set(overrides)==set(alt),'an intended alternative became unreachable'
# A unique assignment in this plan only, not an object/source-root audit.
virtual=[x['virtual_logical_path'] for x in selected.values()]
assert len(virtual)==len(set(virtual))
paths=[x['source_path'] for x in selected.values()]
assert len(paths)==len(set(paths))
state={};stack=[];order=[]
def visit(n):
    if state.get(n)==1:
        i=stack.index(n);raise RuntimeError('local lexical cycle: '+' -> '.join(stack[i:]+[n]))
    if state.get(n)==2:return
    state[n]=1;stack.append(n)
    for dep in edges.get(n,[]):
        if dep in selected:visit(dep)
    stack.pop();state[n]=2;order.append(n)
for n in sorted(selected):visit(n)
assert 'Mathlib.Tactic.Omega' not in frontier
reverse=defaultdict(set)
for n,deps in edges.items():
    for dep in deps:
        if dep in selected:reverse[dep].add(n)
affected=set(alt);walk=deque(sorted(affected))
while walk:
    for n in reverse[walk.popleft()]:
        if n not in affected:affected.add(n);walk.append(n)
affected_order=[n for n in order if n in affected]
assert 'Fixed85Endpoint' in affected
print(json.dumps({'root':'Fixed85Endpoint','baseline_manifest_sha256':sha256((base/'manifest.json').read_bytes()).hexdigest(),
 'signfree_receipt_sha256':sha256((sign/'receipt.json').read_bytes()).hexdigest(),
 'eight_alternative_receipt_sha256':sha256((haz/'receipt.json').read_bytes()).hexdigest(),
 'selected_local_module_count':len(selected),'local_alternatives':overrides,
 'external_frontier_count':len(frontier),'external_frontier':sorted(frontier),
 'selected_modules':selected,'dependency_first_order':order,
 'reverse_affected_local_count':len(affected),'reverse_affected_order':affected_order,
 'scope':'Read-only lexical source assignment only; external source, object search path, provider, Lean, axioms, resource and PDF checks excluded.'},sort_keys=True,indent=2))

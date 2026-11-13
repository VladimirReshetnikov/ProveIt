from pathlib import Path
from collections import defaultdict
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-native-composition-draft')
root='Fixed85Endpoint'
index=defaultdict(list)
for p in Path('research').rglob('*.lean*'):
    name=p.name[:-9] if p.name.endswith('.lean.src') else (p.name[:-5] if p.name.endswith('.lean') else None)
    if name:index[name].append(p)
# Root and all other bare names are selected only when every observed
# candidate has identical bytes. This lexical scan does not inspect oleans.
index[root].append(D/'Fixed85Endpoint.lean.src') if D/'Fixed85Endpoint.lean.src' not in index[root] else None
selected={};edges={};frontier=set();queue=[root]
while queue:
    name=queue.pop()
    if name in selected or name in frontier:continue
    if '.' in name:
        p=Path('Lean')/('/'.join(name.split('.'))+'.lean')
        candidates=[p] if p.is_file() else []
    else:candidates=index[name]
    if not candidates:
        frontier.add(name);continue
    hashes={sha256(p.read_bytes()).hexdigest() for p in candidates}
    if len(hashes)!=1:raise RuntimeError('ambiguous source bytes for '+name+': '+str(sorted(map(str,candidates))))
    # Prefer retained research sources to overlay aliases when bytes match.
    file=sorted(candidates,key=lambda p:('overlay' in str(p),str(p)))[0]
    imports=[]
    for line in file.read_text().splitlines():
        m=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$',line)
        if m:imports.extend(m.group(1).split())
    selected[name]={'path':str(file),'sha256':next(iter(hashes)),
                    'same_byte_candidates':len(candidates),'imports':imports}
    edges[name]=imports
    queue.extend(imports)
state={};stack=[];order=[]
def visit(name):
    if state.get(name)==1:
        i=stack.index(name);raise RuntimeError('lexical import cycle: '+' -> '.join(stack[i:]+[name]))
    if state.get(name)==2:return
    state[name]=1;stack.append(name)
    for dep in edges.get(name,[]):
        if dep in edges:visit(dep)
    stack.pop();state[name]=2;order.append(name)
for name in sorted(selected):visit(name)
print(json.dumps({'root':root,'local_module_count':len(selected),
 'external_frontier_count':len(frontier),'external_frontier':sorted(frontier),
 'local_modules':selected,'dependency_first_order':order,
 'scope':'Lexical local-source scan only; no provider, olean, external-source, Lean or axiom validation.'},sort_keys=True,indent=2))

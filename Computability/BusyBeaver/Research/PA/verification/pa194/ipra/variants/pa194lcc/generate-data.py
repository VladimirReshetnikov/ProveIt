"""Generate a compact PA194LC_C specialization, sharing LC's physical
runtime and hash-consed trie subtrees. Input files are exact-byte pinned.
"""
from pathlib import Path
from hashlib import sha256
import json
import re
import sys
if len(sys.argv) != 4:
    raise SystemExit("usage: generate-data.py REPO OUTPUT VERIFIED_LC_DATA")
repo, out, lc_data = map(Path, sys.argv[1:])
base=repo/'Computability/BusyBeaver/Research/PA/docs/pa194_loop_continuation_research_2026-11-14/machines'
pins={
 ('PA194LC_C','machine.tm'):'7de80d804e5994db6008687421b0c5b4e96c9c87097fb293269406e9009a5753',
 ('PA194LC_C','labels.json'):'dedb6297f4e43a0b6b1a3867be950ce9ca8ba8cc72c2a0297ce99fe071f11112',
 ('PA194LC_C','sites.json'):'4e3c1e0bd48668a63923192e9c55e22ee2f6d5442aee030f3788fbd8e00d28f4',
 ('PA194LC_C','instructions.json'):'6c3127cd0da15fda49ed99cea199a009b9bc1e1707100846df9a2df02a22d507',
 ('PA194LC','machine.tm'):'9cb620ba1b869fb793fd9ba0a99e90dcc85d9a6d62a42f48109743a7fbeda3c8',
 ('PA194LC','labels.json'):'86a4619d85d97849d0169c8c9773a37bcc8d1d05356451e6c761ab3bfcdda691',
 ('PA194LC','sites.json'):'4ceafb0e8b1e7b983f2b25d7b4c0902c34a6544142f7fd8a715c4b9bb8ef0e6d',
 ('PA194LC','instructions.json'):'6c3127cd0da15fda49ed99cea199a009b9bc1e1707100846df9a2df02a22d507',
}
raw={k:(base/k[0]/k[1]).read_bytes() for k in pins}
for k,h in pins.items(): assert sha256(raw[k]).hexdigest()==h,k
assert raw['PA194LC_C','instructions.json']==raw['PA194LC','instructions.json']
labels=json.loads(raw['PA194LC_C','labels.json'])
assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254 and labels[24]==84
rows={}
for line in raw['PA194LC_C','machine.tm'].decode('ascii').splitlines():
    q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
    assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R') and 0<=n<=194
    rows[q,b]=(w, int(d=='R'), n)
assert set(rows)=={(q,b) for q in range(194) for b in range(2)}
native={(labels[q],b):(w,d,labels[n]) for (q,b),(w,d,n) in rows.items()}
assert set(native)=={(q,b) for q in labels[:-1] for b in (0,1)}

def trie(sites):
    assert len(sites)==3673 and [r[0] for r in sites]==sorted(set(r[0] for r in sites))
    root={}
    for path,op,arg in sites:
        node=root
        for b in path:
            assert b in '01' and 'leaf' not in node
            node=node.setdefault(b,{})
        assert not node and op in ('inc','dec','breakTo','continueTo','halt')
        node['leaf']=(op,arg)
    return root

def canonical(node):
    if 'leaf' in node: return ('leaf',)+node['leaf']
    assert set(node)=={'0','1'}
    return ('node',canonical(node['0']),canonical(node['1']))

old={};old_defs=[]
def build_old(key):
    if key in old:return old[key]
    if key[0]=='leaf':
        op,arg=key[1:];body='.leaf .halt' if op=='halt' else f'.leaf (.{op} {arg})'
    else: body=f'.node {build_old(key[1])} {build_old(key[2])}'
    name=f'sourceNode{len(old_defs)}';old[key]=name;old_defs.append(f'def {name} : M6.Source.PathTrie.Tree := {body}')
    return name
build_old(canonical(trie(json.loads(raw['PA194LC','sites.json']))))
original=lc_data.read_text()
for line in old_defs: assert line in original, f'LC shared node mismatch: {line}'
new={};new_defs=[];used_old=set()
def build_new(key):
    if key in old:
        used_old.add(old[key]); return 'PA194LCData.'+old[key]
    if key in new:return new[key]
    assert key[0]=='node'
    body=f'.node {build_new(key[1])} {build_new(key[2])}'
    name=f'newSourceNode{len(new_defs)}';new[key]=name;new_defs.append(f'def {name} : M6.Source.PathTrie.Tree := {body}')
    return name
root=build_new(canonical(trie(json.loads(raw['PA194LC_C','sites.json']))))
# Exact reachable native changes from the checked LC table. Nonworking native
# controls 41 and 190 must be removed, even though raw.native.tm retains them.
patch={
 (28,0):(0,1,331), (70,0):(0,1,331),
 (139,0):(0,1,330),(139,1):(1,1,331),
 (330,0):(0,1,99),(330,1):(1,1,61),
 (331,0):(0,0,30),(331,1):(1,0,46),
}
for k,v in patch.items():assert native[k]==v,(k,native.get(k),v)
assert 41 not in labels and 190 not in labels
old_labels=json.loads(raw['PA194LC','labels.json'])
old_native={}
for line in raw['PA194LC','machine.tm'].decode('ascii').splitlines():
    q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
    old_native[old_labels[q],b]=(w,int(d=='R'),old_labels[n])
def proposed(q,b):
    if q in (41,190): return None
    if (q,b) in patch: return patch[q,b]
    return old_native.get((q,b))
for q in set(old_labels)|set(labels):
    for b in (0,1): assert proposed(q,b)==native.get((q,b)),(q,b,proposed(q,b),native.get((q,b)))

def lean_list(xs):return '[\n'+',\n'.join(','.join(map(str,xs[i:i+12])) for i in range(0,len(xs),12))+'\n]'
row_lit=[str(rows[q,b]).replace(' ','') for q in range(194) for b in range(2)]
src='''import PA194LCData\nset_option autoImplicit false\nset_option maxRecDepth 65536\nnamespace PA194LCCData\n\n'''
src+='def labels : List Nat := '+lean_list(labels)+'\n'
src+='def rows : List PA194BRows.Action := '+lean_list(row_lit)+'\n'
src+='''def table : ConPA.Machine.Table := PA194BModelSteps.table rows
/-- Exact LC_C native machine, reusing every unchanged LC native row. -/
def machine (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  if q = 41 ∨ q = 190 then none
  else if q = 28 ∧ b = false then some (false,true,331)
  else if q = 70 ∧ b = false then some (false,true,331)
  else if q = 139 then if b then some (true,true,331) else some (false,true,330)
  else if q = 330 then if b then some (true,true,61) else some (false,true,99)
  else if q = 331 then if b then some (true,false,46) else some (false,false,30)
  else PA194LCData.machine q b

def denseControl (q : Nat) : Nat := labels.idxOf q

'''
src+='\n'.join(new_defs)+f'''\n\ndef sourceTrie : M6.Source.PathTrie.Tree := {root}
def path (i : Nat) : M6.Source.Path := ((M6.Source.PathTrie.nthSite sourceTrie i).map (·.path)).getD []
def codeAt (i : Nat) : Option M6.Source.Instruction := (M6.Source.PathTrie.nthSite sourceTrie i).bind (M6.FastResolve.resolveTree sourceTrie)
end PA194LCCData\n'''
out.mkdir(parents=True,exist_ok=True)
(out/'PA194LCCData.lean').write_text(src)
print(f'PA194LC_C: {len(new_defs)} new trie nodes, {len(used_old)} existing LC subtree roots reused; 388 literal rows.')

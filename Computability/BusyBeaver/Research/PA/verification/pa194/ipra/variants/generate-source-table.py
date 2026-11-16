"""Generate exact table and trie definitions for variants using the primary source."""
from hashlib import sha256
import json
from pathlib import Path
import sys

variants = {
    "PA194OR": (
        "PA194ORH_research_2026-11-15/machines/PA194OR",
        {
            "machine.tm": "379e12957eafc5ecb1ec04868067fe931af913e7bc46e69a36b6067d83c4c79f",
            "labels.json": "50201e76c668de9e019ba164cbfd8678afb9d0681a6082fe859a54acb1d9862c",
            "sites.json": "2abdf5327f0048c9a7bf87367e3b0fabbfa7a848d68efdfa934b494ab78bdf35",
        },
    ),
    "PA194LC": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC",
        {
            "machine.tm": "9cb620ba1b869fb793fd9ba0a99e90dcc85d9a6d62a42f48109743a7fbeda3c8",
            "labels.json": "86a4619d85d97849d0169c8c9773a37bcc8d1d05356451e6c761ab3bfcdda691",
            "sites.json": "4ceafb0e8b1e7b983f2b25d7b4c0902c34a6544142f7fd8a715c4b9bb8ef0e6d",
        },
    ),
    "PA1944L": (
        "pa1944l_research_2026-11-14/machine",
        {
            "machine.tm": "c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253",
            "labels.json": "2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b",
            "sites.json": "bccf0a80ffdf4ff48c4457adf7331aa4c4d2a7742712983dd45ab4b243ed8820",
        },
    ),
    "PA194LCA": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC_A",
        {
            "machine.tm": "382663bad011e958b51221a589e47880d434172d2f3417d2f3e940acda33cbdf",
            "labels.json": "21bb75424719d5d6718ca654d41f22b0467d3758d2cdd439a6000584a2399b53",
            "sites.json": "9fb634b85041caf1acd31ea022249475a0cfcacd51d19337723abe231448a0fe",
        },
    ),
    "PA194M4R": (
        "pa194_radix_family_2026-11-13/machines/4R",
        {
            "machine.tm": "a3c1d556d61b37d60639801accacfa595df4b2c9d2b2a0a46978425b10c459a8",
            "labels.json": "2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b",
            "sites.json": "153efd28b8b07de416bd842fcd4976170ffcc33a8f63ce4e6bd37f97ae8a440d",
        },
    ),
}
if len(sys.argv) != 4 or sys.argv[1] not in variants:
    raise SystemExit(f"usage: generate-source-table.py {{{','.join(variants)}}} REPO OUTPUT")
variant = sys.argv[1]
repo, out = map(Path, sys.argv[2:])
packets = repo / "Computability/BusyBeaver/Research/PA/docs"
relative, pins = variants[variant]
folder = packets / relative
raw = {name: (folder / name).read_bytes() for name in pins}
for name, digest in pins.items():
    assert sha256(raw[name]).hexdigest() == digest, name
primary = (packets / "pa194_conpa_2026-11-13/construction/source/pa194.instructions.json").read_bytes()
assert sha256(primary).hexdigest() == "6c3127cd0da15fda49ed99cea199a009b9bc1e1707100846df9a2df02a22d507"
assert (folder / "instructions.json").read_bytes() == primary
labels=json.loads(raw['labels.json'])
assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254
sites=json.loads(raw['sites.json'])
assert len(sites)==3673 and [r[0] for r in sites]==sorted(set(r[0] for r in sites))
rows={}
for line in raw['machine.tm'].decode('ascii').splitlines():
 q,b,w,d,n=line.split()
 q,b,w,n=map(int,(q,b,w,n))
 assert (q,b) not in rows and w in (0,1) and d in ('L','R') and 0<=n<=194
 rows[q,b]=w,int(d=='R'),n
assert set(rows)=={(q,b) for q in range(194) for b in range(2)}
assert labels[24]==84
native={(labels[q],b):(w,d,labels[n]) for (q,b),(w,d,n) in rows.items()}

def token(b): return 'true' if b else 'false'
def action(q,b):
 w,d,n=native[q,b]
 return f'(some ({token(w)},{token(d)},{n}))'

def balanced(states):
 if not states: return '.empty'
 mid=len(states)//2
 q=states[mid]
 return f'(.node {q} {action(q,0)} {action(q,1)}\n{balanced(states[:mid])}\n{balanced(states[mid+1:])})'

def lean_rows(records):
 return '[\n'+',\n'.join(','.join(map(str,records[i:i+12])) for i in range(0,len(records),12))+'\n]'

trie={}
for path,op,arg in sites:
 node=trie
 for b in path:
  assert b in '01' and 'leaf' not in node
  node=node.setdefault(b,{})
 assert not node and op in ('inc','dec','breakTo','continueTo','halt')
 assert op not in ('inc','dec') or 0 <= arg < 9
 node['leaf']=(op,arg)

tree_cache={}
definitions=[]
def build(node):
 if 'leaf' in node:
  op,arg=node['leaf']
  body=f'.leaf .halt' if op=='halt' else f'.leaf (.{op} {arg})'
 else:
  assert set(node)=={'0','1'}
  l=build(node['0']); r=build(node['1'])
  body=f'.node {l} {r}'
 if body not in tree_cache:
  name=f'sourceNode{len(definitions)}'
  tree_cache[body]=name
  definitions.append(f'def {name} : M6.Source.PathTrie.Tree := {body}')
 return tree_cache[body]
root=build(trie)
out.mkdir(parents=True,exist_ok=True)
(out/f'{variant}Data.lean').write_text(f'''import PA194FoldedCache
import PA194BModelSteps
import PA194SourceProgram

set_option autoImplicit false
set_option maxRecDepth 65536

namespace {variant}Data

'''+f'''def labels : List Nat := {lean_rows(labels)}
def rows : List PA194BRows.Action := {lean_rows([str(rows[q,b]).replace(' ','') for q in range(194) for b in range(2)])}
def table : ConPA.Machine.Table := PA194BModelSteps.table rows
def nativeTree : PA194FoldedCache.Tree := {balanced(sorted(labels[:-1]))}
def machine : M6.Zip.TMN := nativeTree.read
def denseControl (q : Nat) : Nat := labels.idxOf q

'''+'\n'.join(definitions)+f'''

def sourceTrie : M6.Source.PathTrie.Tree := {root}

def path (i : Nat) : M6.Source.Path :=
  ((M6.Source.PathTrie.nthSite sourceTrie i).map (·.path)).getD []

def codeAt (i : Nat) : Option M6.Source.Instruction :=
  (M6.Source.PathTrie.nthSite sourceTrie i).bind (M6.FastResolve.resolveTree sourceTrie)

end {variant}Data
''')

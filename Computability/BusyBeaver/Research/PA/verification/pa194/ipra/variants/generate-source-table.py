"""Generate exact table and trie definitions for pinned source variants."""
from hashlib import sha256
import json
from pathlib import Path
import sys

variants = {
    "PA194M5": (
        "pa194_radix_family_2026-11-13/machines/5",
        {
            "machine.tm": "180a0fd1f046d4cbd687b43979f0605619ad5f53054d32b9f62f33e7a3bccab8",
            "labels.json": "2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b",
            "sites.json": "bcdacaa1eb2f6be28cea742eb9d553d885a3ae490c9b307d2986fcde75d3b5b1",
        },
    ),
    "PA194M6": (
        "pa194_radix_family_2026-11-13/machines/6",
        {
            "machine.tm": "725ce8474d7b83473488fc9466548ed2de3744d9a80183467894f9d719103ab2",
            "labels.json": "2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b",
            "sites.json": "57e57debadcfd4108cf96c4bcea8bab110ee68726bbc3eccb03f79ce1379e8cf",
            "nodes.json": "766d660e161aa1f763d2d86080ba876062df990b4d5f65629c25f9240477b915",
        },
    ),
    "PA194LCB": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC_B",
        {
            "machine.tm": "4b2b45e97fdd5f8a6e22c4f552dc3f26252c170e85cdb5ddb27ad5d5c580982a",
            "labels.json": "fb3e694862543de6011c30dcc1b71be0a6b4082a310e03de72146597c77ef7bf",
            "sites.json": "f8bbc75985b4e63bd1afe49ff8a7628cf45d1b8a2f0a309bdbef61b47165ecae",
        },
    ),
    "PA194AX11H": (
        "pa194_ax11h_research_2026-11-14/machine",
        {
            "machine.tm": "c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a",
            "labels.json": "1d2af5a756e731ce2d8d88811a6c8d3c37373f0d5d51586f12ae49c53e40a37c",
            "sites.json": "fd50d10d10052ddf5cd35cbbe221793366c1e3e703c18426596103ecd6b0edb7",
        },
    ),
    "PA194LCAX11H": (
        "pa194_loop_continuation_research_2026-11-14/additional/PA194LC_AX11H",
        {
            "machine.tm": "5f10f071e7118ff33aba822e05bae0331b4c78508656c3e945c31b0c6788f9c5",
            "labels.json": "f3cd162dc606d85dc68db8059a44d251ddefb5db167dd06e3140ed9abb891f3b",
            "sites.json": "85947f638c6a4f922752982886c4442bcd75f9550be93412872d018ee5fafd60",
        },
    ),
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
instructions = (folder / "instructions.json").read_bytes()
site_count = 3673
if variant in ("PA194AX11H", "PA194LCAX11H"):
    assert sha256(instructions).hexdigest() == "43a4ba0d62f95fe766d5369940b0aa8b7a4da04824feb8836905e289640f59f7"
    site_count = 3671
elif variant == "PA194M5":
    assert sha256(instructions).hexdigest() == "34375509c46552ff7f5c84e24d265cdf56ecd97b41fad3da14787232aa601ca4"
    site_count = 3734
elif variant == "PA194M6":
    assert sha256(instructions).hexdigest() == "03afe51960fe2345637a0e3ea25987a8544612124ad728874cbc45ef1de9126d"
    site_count = 3795
else:
    assert instructions == primary
labels=json.loads(raw['labels.json'])
assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254
sites=json.loads(raw['sites.json'])
assert len(sites)==site_count and [r[0] for r in sites]==sorted(set(r[0] for r in sites))
rows={}
for line in raw['machine.tm'].decode('ascii').splitlines():
 q,b,w,d,n=line.split()
 q,b,w,n=map(int,(q,b,w,n))
 assert (q,b) not in rows and w in (0,1) and d in ('L','R') and 0<=n<=194
 rows[q,b]=w,int(d=='R'),n
assert set(rows)=={(q,b) for q in range(194) for b in range(2)}
assert labels[24]==84
native={(labels[q],b):(w,d,labels[n]) for (q,b),(w,d,n) in rows.items()}
native_pins = {
    "PA194AX11H": "6022711dcc0a025eb4b7a5a8f690d6b52f45f3d963a0868afef10962ccc49bd3",
    "PA194M6": "759255b48e7c2bd2e4c25e755639c6302ad14f5c33ed6fcc3af1a4534ba9ae5e",
}
if variant in native_pins:
    native_bytes = "".join(
        f"{q} {b} {w} {'R' if d else 'L'} {n}\n"
        for (q, b), (w, d, n) in sorted(native.items())
    ).encode("ascii")
    assert sha256(native_bytes).hexdigest() == native_pins[variant]

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

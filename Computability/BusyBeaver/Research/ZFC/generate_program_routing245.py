#!/usr/bin/env python3
"""Emit an exact source-only Routing245 program/tree unit from pinned plain JSON.
No supplied code imports, compiler, checker, network or maintained writes.
"""
from pathlib import Path
import argparse,collections,hashlib,json,re
def repository_root():
 # Installed location is Research/ZFC; scratch use passes --repo explicitly.
 early=argparse.ArgumentParser(add_help=False)
 early.add_argument('--repo',type=Path)
 known,_=early.parse_known_args()
 if known.repo is not None:
  root=known.repo.resolve()
  if not (root/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Prog254.lean').is_file():
   raise SystemExit('--repo does not contain the expected Prog254 source')
  return root
 for root in Path(__file__).resolve().parents:
  if (root/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Prog254.lean').is_file():
   return root
 raise SystemExit('Cannot locate repository from this script; pass --repo')
R=repository_root()
DEFAULT=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-sites_logical.json'
EXPECTED='f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'
BASE=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Prog254.lean'
BASE_SHA='6e564bd1ba179b2d39fccc3b8c86a681ec0dd6529df9cfa2522500eef140cfde'
KIND={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
sha=lambda b:hashlib.sha256(b).hexdigest()
def desc(p):
 b=p.read_bytes();return {'path':str(p),'sha256':sha(b),'bytes':len(b)}
def edge(e):return '.halt' if e[0]=='halt' else f'(.{e[0]} {e[1]})'
def tedge(e):return f't{e[1]:03}' if e[0]=='node' else f'(.leaf {edge(e)})'
def childproof(e):return f'(fun f hf => node{e[1]:03}_eq f hf)' if e[0]=='node' else '(fun _ _ => rfl)'
def generate(inp,out):
 if not __debug__:raise RuntimeError('Assertions must remain enabled')
 assert out.is_absolute() and not out.is_relative_to(R)
 assert sha(inp.read_bytes())==EXPECTED and sha(BASE.read_bytes())==BASE_SHA
 sites=json.loads(inp.read_text());assert len(sites)==6460
 leaf={};prefixes=set()
 for r in sites:
  assert len(r)==3 and isinstance(r[0],str) and r[0] and set(r[0])<={'0','1'}
  path,kind,arg=r;assert kind in KIND
  if kind=='CH':assert arg is None
  elif kind in ('CI','CD'):assert type(arg) is int and 0<=arg<9
  else:assert type(arg) is int and arg>=1
  assert path not in leaf;leaf[path]=(KIND[kind],arg)
  prefixes.update(path[:i]for i in range(len(path)))
 assert len(prefixes)==6459 and not set(leaf)&prefixes
 assert all(p+'0' in leaf or p+'0' in prefixes for p in prefixes)
 assert all(p+'1' in leaf or p+'1' in prefixes for p in prefixes)
 rows=[];seen={};heights=[]
 def trie(p):
  if p in leaf:return leaf[p]
  a,b=trie(p+'0'),trie(p+'1');key=(a,b)
  if key not in seen:
   i=len(rows);seen[key]=i;rows.append(key)
   heights.append(max(heights[e[1]] if e[0]=='node' else 0 for e in key)+1)
  return ('node',seen[key])
 root=trie('');assert len(rows)==203 and root==('node',202) and heights[-1]==51
 assert all(e[1]<i for i,row in enumerate(rows)for e in row if e[0]=='node')
 # Parse the existing original DFS row source directly, without importing its generator.
 oldrows={}
 pat=re.compile(r'^  \((\.halt|\.[a-z]+ \d+), (\.halt|\.[a-z]+ \d+)\), -- (\d+)$',re.M)
 def parseedge(s):
  z=s[1:].split();return (z[0],int(z[1]) if len(z)==2 else None)
 for m in pat.finditer(BASE.read_text()):oldrows[int(m[3])]=(parseedge(m[1]),parseedge(m[2]))
 assert set(oldrows)==set(range(6459))
 oldsites=[]
 def oldwalk(i,p):
  for bit,e in zip('01',oldrows[i]):
   if e[0]=='node':oldwalk(e[1],p+bit)
   else:oldsites.append((p+bit,e))
 oldwalk(0,'')
 assert len(oldsites)==6460
 assert [(KIND[k],a)for _,k,a in sites]==[e for _,e in oldsites]
 changed=sum(p!=r[0] for (p,_),r in zip(oldsites,sites));assert changed==6241
 # Independently expand the hash-consed row program into full paths and compare exact data.
 unfolded=[]
 def expand(i,p):
  for bit,e in zip('01',rows[i]):
   if e[0]=='node':expand(e[1],p+bit)
   else:unfolded.append((p+bit,e))
 expand(202,'');assert unfolded==[(p,(KIND[k],a))for p,k,a in sites]
 out.mkdir(parents=True,exist_ok=True)
 for fn in ['ProgramRouting245.lean','Audit.lean','source-inventory.json','program-data.json']:
  assert not (out/fn).exists(),f'Preserve prior attempt before overwriting {fn}'
 text=['''import BusyBeaver.ZFC.RMBisim

/-!
Exact logical decoder for the routed 245 candidate, arrival 8286787dd0.
The pinned 6460-leaf certificate is stored as 203 distinct binary subtrees;
its complete unfolding still has 6459 internal nodes and maximum depth 51.
203 is a register-program storage count, not a binary Turing-machine state count.
All logical register indices and break/continue depths are retained exactly.
The proof below identifies this program's decoder for every fuel >= 51, then
uses RegisterPath's full consume/execute semantics for arbitrary pointers and
register files. No equivalence to Prog254, machine simulation, or consistency
calibration is asserted by this unit.

Original machine/calculus: Mira-Cult; public verification: Jeff Ketchersid;
compiler framework: Andrew James Wade. The new grammar/routing submission and
prior ProveIt constructions retain their original attribution and notices.
-/
set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.ProgramRouting245
open RegisterPath

abbrev Row := Edge × Edge
''']
 for i,(a,b)in enumerate(rows):text.append(f'private def row{i:03} : Row := ({edge(a)}, {edge(b)})\n')
 def lookup(lo,hi,indent):
  if hi-lo==1:return f'row{lo:03}'
  mid=(lo+hi)//2;pad=' '*indent
  return f'if n < {mid} then\n{pad}  {lookup(lo,mid,indent+2)}\n{pad}else\n{pad}  {lookup(mid,hi,indent+2)}'
 text.append('\nprivate def rawLookup (n : Nat) : Row :=\n  '+lookup(0,203,2)+'\n')
 text.append('''
def nodes (n : Nat) : Row :=
  if n < 203 then rawLookup n else (.halt, .halt)

def program : Program where
  nodes := nodes
  root := 202
  nnodes := 203

theorem program_root : program.root = 202 := rfl
theorem program_nnodes : program.nnodes = 203 := rfl

theorem nodes_default (n : Nat) (hn : 203 ≤ n) : program.nodes n = (.halt, .halt) := by
  simp only [program, nodes, if_neg (Nat.not_lt.mpr hn)]

end ProgramRouting245

namespace TreeRouting245
open RegisterPath RMBisim ProgramRouting245

/-- Compose exact child unfoldings; the fuel bound is explicit and arbitrary. -/
private theorem parent_eq {p : Program} {n h₀ h₁ : Nat} {e₀ e₁ : Edge} {t₀ t₁ : Tree}
    (hrow : p.nodes n = (e₀, e₁))
    (hl : ∀ f, h₀ ≤ f → sub p f e₀ = t₀)
    (hr : ∀ f, h₁ ≤ f → sub p f e₁ = t₁) :
    ∀ f, max h₀ h₁ + 1 ≤ f → toTree p f n = .node t₀ t₁ := by
  intro f hf
  cases f with
  | zero => cases hf
  | succ f =>
      have hm : max h₀ h₁ ≤ f := Nat.le_of_succ_le_succ hf
      rw [toTree_succ, hrow]
      change Tree.node (sub p f e₀) (sub p f e₁) = .node t₀ t₁
      rw [hl f (Nat.le_trans (Nat.le_max_left _ _) hm),
        hr f (Nat.le_trans (Nat.le_max_right _ _) hm)]

''')
 for i,(a,b)in enumerate(rows):
  h0=heights[a[1]]if a[0]=='node'else 0;h1=heights[b[1]]if b[0]=='node'else 0
  text.append(f'''private def t{i:03} : Tree := .node {tedge(a)} {tedge(b)}
private theorem row{i:03}_eq : program.nodes {i} = ({edge(a)}, {edge(b)}) := by decide +kernel
private theorem node{i:03}_eq (f : Nat) (hf : {heights[i]} ≤ f) : toTree program f {i} = t{i:03} := by
  exact parent_eq (h₀ := {h0}) (h₁ := {h1}) row{i:03}_eq
    {childproof(a)} {childproof(b)} f hf

''')
 text.append('''/-- The exact complete certificate tree, with shared subterms only. -/
def tree : Tree := t202

/-- Exact identity for every sufficient decoder fuel, not one sampled execution. -/
theorem tree_eq_fuel (f : Nat) (hf : 51 ≤ f) :
    toTree program f program.root = tree := node202_eq f hf

/-- The tree used by the actual RegisterPath program semantics. -/
theorem tree_eq : ptree program = tree := tree_eq_fuel 204 (by decide)

theorem walk_eq_tree (P : List Bool) (i : Nat) :
    walk program (program.nnodes + 1) program.root P i = twalk tree (P.drop i) i := by
  rw [walk_tree]
  change twalk (toTree program 204 program.root) (P.drop i) i = twalk tree (P.drop i) i
  rw [tree_eq_fuel 204 (by decide)]

/-- Complete pointer consumption and all five leaf effects are inherited exactly. -/
theorem step_eq_tree (P : List Bool) (R : Registers) :
    step program ⟨P, R⟩ = match tsite tree P with
      | some (e, Q) => execute e Q R
      | none => none := by
  rw [step_tsite, tree_eq]
  cases hsite : tsite tree P with
  | none => rfl
  | some eQ =>
      rcases eQ with ⟨e, Q⟩
      rfl

def leafCount : Tree → Nat
  | .none => 0
  | .leaf _ => 1
  | .node a b => leafCount a + leafCount b

def nodeCount : Tree → Nat
  | .none | .leaf _ => 0
  | .node a b => nodeCount a + nodeCount b + 1

def depth : Tree → Nat
  | .none | .leaf _ => 0
  | .node a b => max (depth a) (depth b) + 1

def haltCount : Tree → Nat
  | .none => 0
  | .leaf e => if e = .halt then 1 else 0
  | .node a b => haltCount a + haltCount b

theorem leaf_count : leafCount tree = 6460 := by decide +kernel
theorem node_count : nodeCount tree = 6459 := by decide +kernel
theorem depth_eq : depth tree = 51 := by decide +kernel
theorem halt_count : haltCount tree = 1 := by decide +kernel

end TreeRouting245
end SetTheory.BusyBeaver.ZFC
''')
 # The two nested namespaces above share this explicit enclosing namespace.
 text[0]=text[0].replace('namespace SetTheory.BusyBeaver.ZFC.ProgramRouting245','namespace SetTheory.BusyBeaver.ZFC\nnamespace ProgramRouting245')
 source=''.join(text);(out/'ProgramRouting245.lean').write_text(source)
 audit='''import BusyBeaver.ZFC.ProgramRouting245

/-! Focused source/tree identity audit, not source bisimulation or binary simulation. -/
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim

'''
 probes=['ProgramRouting245.program_root','ProgramRouting245.program_nnodes','ProgramRouting245.nodes_default','TreeRouting245.tree_eq_fuel','TreeRouting245.tree_eq','TreeRouting245.walk_eq_tree','TreeRouting245.step_eq_tree','TreeRouting245.leaf_count','TreeRouting245.node_count','TreeRouting245.depth_eq','TreeRouting245.halt_count']
 audit+=''.join('#print axioms '+n+'\n'for n in probes)
 audit+='''
example : ProgramRouting245.program.root = 202 := ProgramRouting245.program_root
example : ProgramRouting245.program.nnodes = 203 := ProgramRouting245.program_nnodes
example (n : Nat) (hn : 203 ≤ n) : ProgramRouting245.program.nodes n = (.halt, .halt) :=
  ProgramRouting245.nodes_default n hn
example (f : Nat) (hf : 51 ≤ f) :
    toTree ProgramRouting245.program f ProgramRouting245.program.root = TreeRouting245.tree :=
  TreeRouting245.tree_eq_fuel f hf
example : ptree ProgramRouting245.program = TreeRouting245.tree := TreeRouting245.tree_eq
example (P : List Bool) (i : Nat) :
    walk ProgramRouting245.program 204 202 P i = twalk TreeRouting245.tree (P.drop i) i :=
  TreeRouting245.walk_eq_tree P i
example (P : List Bool) (R : Registers) :
    step ProgramRouting245.program ⟨P, R⟩ = match tsite TreeRouting245.tree P with
      | some (e, Q) => execute e Q R
      | none => none := TreeRouting245.step_eq_tree P R
example : TreeRouting245.leafCount TreeRouting245.tree = 6460 := TreeRouting245.leaf_count
example : TreeRouting245.nodeCount TreeRouting245.tree = 6459 := TreeRouting245.node_count
example : TreeRouting245.depth TreeRouting245.tree = 51 := TreeRouting245.depth_eq
example : TreeRouting245.haltCount TreeRouting245.tree = 1 := TreeRouting245.halt_count

-- Concrete break/continue clients retain their path depths and operands.
example : walk ProgramRouting245.program 204 202 [false, false, true] 0 = some (.brk 1, 3) := by
  calc
    _ = twalk TreeRouting245.tree [false, false, true] 0 :=
      TreeRouting245.walk_eq_tree [false, false, true] 0
    _ = some (.brk 1, 3) := by decide +kernel
example : walk ProgramRouting245.program 204 202 [false, true, false, true, true, true] 0 =
    some (.cont 3, 6) := by
  calc
    _ = twalk TreeRouting245.tree [false, true, false, true, true, true] 0 :=
      TreeRouting245.walk_eq_tree [false, true, false, true, true, true] 0
    _ = some (.cont 3, 6) := by decide +kernel
'''
 (out/'Audit.lean').write_text(audit)
 # Separate parse of rendered rows and rendered Tree children, with no Python object reuse.
 rowpat=re.compile(r'^private def row(\d+) : Row := \((.+), (.+)\)$',re.M)
 parsed=[]
 def rendered_edge(s):return parseedge(s.strip('()'))
 for m in rowpat.finditer(source):
  assert int(m[1])==len(parsed);parsed.append((rendered_edge(m[2]),rendered_edge(m[3])))
 assert parsed==rows
 treepat=re.compile(r'^private def t(\d+) : Tree := \.node (.*)$',re.M)
 # Each right-hand side has two atoms: either tNNN or parenthesized leaf terms.
 def atoms(s):
  out=[];start=0;depth=0
  for i,c in enumerate(s+' '):
   if c=='(':depth+=1
   elif c==')':depth-=1
   if c==' 'and depth==0:
    if i>start:out.append(s[start:i])
    start=i+1
  return out
 for m in treepat.finditer(source):
  i=int(m[1]);ss=atoms(m[2]);assert len(ss)==2
  for atom,e in zip(ss,parsed[i]):assert atom==tedge(e)
 # Compare every expanded rendered row path directly with original ordered data.
 check=[]
 def parsedwalk(i,p):
  for bit,e in zip('01',parsed[i]):
   if e[0]=='node':parsedwalk(e[1],p+bit)
   else:check.append([p+bit,{'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}[e[0]],e[1]])
 parsedwalk(202,'');assert check==sites
 data={'root':202,'nnodes':203,'rows':rows,'heights':heights,'ordered_sites':sites,'full_internal_node_count':6459,'full_leaf_count':6460,'changed_paths_against_Prog254':6241}
 (out/'program-data.json').write_text(json.dumps(data,indent=2)+'\n')
 inventory={'status':'SOURCE_ONLY_DRAFT_NOT_COMPILED','module':'BusyBeaver.ZFC.ProgramRouting245','namespaces':['ProgramRouting245','TreeRouting245'],'source':desc(out/'ProgramRouting245.lean'),'audit':desc(out/'Audit.lean'),'generator':desc(Path(__file__)),'plain_input':desc(inp),'original_program':desc(BASE),'parser_certificate':desc(out/'program-data.json'),'shared_nodes':203,'root_index':202,'decoder_fuel':204,'arbitrary_sufficient_fuel_bound':51,'full_nodes':6459,'leaves':6460,'changed_paths':6241,'counts':dict(collections.Counter(r[1]for r in sites)),'independent_rendered_program_and_tree_parse_matches_all_sites':True,'complete_prefix_tree':True,'every_node_target_has_lower_index':True,'logical_register_and_break_continue_operands_preserved':True,'public_probes':11,'typed_callers':13,'private_node_identity_lemmas':203,'private_row_equality_lemmas':203,'imports':['BusyBeaver.ZFC.RMBisim'],'proof_options':'default','compiler_execution':False,'checker_execution':False,'scope':'Exact new-program decoder and complete consumed-pointer leaf semantics only. No Prog254 halting equivalence, binary simulation or consistency endpoint.'}
 (out/'source-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
 print(json.dumps({'status':inventory['status'],'source':inventory['source'],'audit':inventory['audit'],'shared_nodes':203,'leaves':6460,'changed_paths':6241},indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,help='Repository root; defaults to discovery from the installed script');ap.add_argument('--input',type=Path,default=DEFAULT);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();generate(a.input.resolve(),a.output.resolve())

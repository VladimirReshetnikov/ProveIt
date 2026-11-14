from pathlib import Path
import sys,json,hashlib,argparse,tempfile
BASE=Path(__file__).resolve().parent
REF=BASE/'qh5_reference'
sys.path.insert(0,str(REF/'construction'))
import compiler as c
import support as s
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def grammar_json(t):
 rules={};names={}
 def rec(t):
  if not c.isnode(t):return t
  if t in names:return names[t]
  name='g'+str(len(names));names[t]=name;rules[name]=[rec(x) for x in t];return name
 root=rec(t);return dict(root=root,rules=rules)
parser=argparse.ArgumentParser(description='Reconstruct AX11QH5 and check all symbolic source contracts.')
parser.add_argument('--output',type=Path)
parser.add_argument('--quick',action='store_true',help='Skip construction runtime replay; no independent literal replay is performed by this builder.')
args=parser.parse_args()
assert __debug__ and not sys.flags.optimize
raw0=s.read_table(REF/'machine/raw.native.tm')
nodes={k:tup(v)for k,v in json.loads((REF/'machine/nodes.json').read_text()).items()}
c.raw_nodes=lambda:nodes;c.machine=lambda:(raw0,[])
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
g=c.read_grammar(REF/'construction/inputs/q.grammar.json')
oldsites,oldins,oldcontracts=c.source(g)
assert json.loads(json.dumps(oldins))==json.loads((REF/'machine/instructions.json').read_text())
count=0
def replace(t):
 global count
 if t==c.BREAK:count+=1;return 'node49'
 return tuple(map(replace,t))if c.isnode(t)else t
newg=replace(g);assert count==1
raw,idx,shape=c.build(newg)
folds=json.loads((REF/'machine/folds.json').read_text())
rows,aliases=s.apply_folds(raw,folds)
local=s.check_local_folds(raw,rows,aliases,folds)
sites,ins,contracts=c.source(newg)
print('raw',len(raw)//2,'new',len(rows)//2,'readers',len(shape),'sites',len(sites),'contracts',len(contracts),flush=True)
runtime=None if args.quick else c.validate(rows,contracts)
if runtime is not None:assert runtime['ok'],runtime
startup=s.startup(rows,sites[25][0])
dense,labels=s.dense_table(rows,194)
out=args.output or Path(tempfile.mkdtemp(prefix='AX11QH5-'));out.mkdir(parents=True,exist_ok=True)
for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
 (out/name).write_text(s.table_text(table))
for name,data in [('nodes.json',nodes),('grammar.json',grammar_json(newg)),('labels.json',labels),('folds.json',folds),('local_folds.json',local),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins)]:dump(out/name,data)
diff=[{'state':q,'read':b,'old':raw0[q,b],'new':a}for (q,b),a in raw.items()if raw0.get((q,b))!=a]
receipt=dict(name='AX11QH5',working_states=len(rows)//2,raw_states=len(raw)//2,reader_states=len(shape),folds=len(folds),source_sites=len(sites),source_outcomes=len(contracts),local_fold_cases=len(local['cases']),runtime=runtime,startup=startup,raw_diff=diff,hashes={x:hashlib.sha256((out/x).read_bytes()).hexdigest()for x in ['machine.tm','machine.native.tm']},absolute_ipra_calibration_proved=False)
assert receipt['hashes']['machine.tm']=='f7f52501055ff4fe47aab51acc6536adf3823afca4016a670c67b2c592ed4b02'
assert receipt['hashes']['machine.native.tm']=='a311c42e7839951cc1763a91b4546a7989176bc922e966d3313cba97e4d6f1e2'
dump(out/'receipt.json',receipt)
print(json.dumps(receipt,indent=2))

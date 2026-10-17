"""Exact one-edge source change, MP helper contracts, and complete Wade cost.

The theorem EnumNoFiller254.lean covers the changed abstract enumerator.
These helper tests do not replace a modified compiler simulation proof.
"""
from pathlib import Path
import sys,importlib,copy,json,hashlib,time,argparse
ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,default=ROOT/'ProveIt')
parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'mp_no_filler')
args=parser.parse_args()
RESEARCH=args.repo.resolve()/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(RESEARCH))
import recover_wade_dag as r
from pairing_backend_experiment import execute_helper
from register_lifetime_experiment import compile_measure
out=args.output.resolve()
out.mkdir(exist_ok=True)
backenddir=out/'backend';backenddir.mkdir(exist_ok=True)
for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
 (backenddir/name).write_bytes(r.git_bytes(None,'ZF/generator/'+name))
sys.path.insert(0,str(backenddir));backend=importlib.import_module('TMBuilder')
nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
original=r.builder_from_dag(backend,nodes,names)
modified=copy.deepcopy(original)
assert modified.sequences[130].seq==(123,166)
modified.sequences[130].seq=(123,167)
P=lambda a,b:(a+b)*(a+b+1)//2+b
cases=[]
for top in range(4):
 for d in range(4):
  for stack in range(3):
   expected_h=4*P(top,d)
   for successful in (False,True):
    h=expected_h if successful else (0 if expected_h else 1)
    initial=[7,top,stack,13,d,h,0,0,17]
    expected0=initial.copy();expected1=initial.copy()
    expected0[1]=expected1[1]=d if successful else 0
    expected0[5]=expected1[5]=0
    expected0[2]=P(0,stack) if successful else stack
    expected1[2]=stack
    for which,b,expect in [('original',original,expected0),('no_filler',modified,expected1)]:
     actual=initial.copy()
     status=execute_helper(b,150,actual,fuel=1_000_000)
     if status!=('normal',) or actual!=expect:
      raise AssertionError((which,initial,status,actual,expect))
    cases.append(dict(top=top,d=d,stack=stack,success=successful))
result=dict(source_commit='85633fd2f57b5dca16f87667699134d1b500ebc0',upstream_commit=r.COMMIT,
 source_dag_sha256=hashlib.sha256(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v')).hexdigest(),
 source_edit={'node':130,'old':list(original.sequences[130].seq),'new':list(modified.sequences[130].seq)},
 exact_register_cases=len(cases),all_nine_registers_compared=True,
 helper_claim='original successful MP pushes truth0; new successful MP preserves prior stack',
 original=compile_measure(backend,original,'original-nine',out/'original'),
 no_filler=compile_measure(backend,modified,'original-nine',out/'no_filler'),
 abstract_refutation_equivalence='EnumNoFiller254.lean:halts_iff_original',
 modified_binary_simulation_proved=False,new_sub252_machine_claimed=False,
 driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

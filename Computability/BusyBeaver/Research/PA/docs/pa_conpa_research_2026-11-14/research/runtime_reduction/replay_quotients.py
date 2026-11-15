#!/usr/bin/env python3
"""Replay the four finite two-row quotient searches with fresh symbolic contexts."""
import argparse,hashlib,json,pathlib,re,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=pathlib.Path,required=True)
p.add_argument('--candidate-root',type=pathlib.Path,default=ROOT.parents[1]/'machines')
a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
if out==ROOT:raise SystemExit('Use a separate replay-output directory.')
expected={('PA194AX11GH',4):(8789,23887996,139688),('PA194AX11GHS',4):(8830,23579196,129742),('PA194AX11GH',6):(30755,25753148,181936),('PA194AX11GHS',6):(30860,25589484,174778)}
records=[]
with tempfile.TemporaryDirectory(prefix='pa194-two-row-') as temporary:
 exe=pathlib.Path(temporary)/'merge'
 subprocess.run(['g++','-std=c++17','-O3',str(ROOT/'inherited/src/joint_return_merge.cpp'),'-o',str(exe)],check=True)
 for (name,radius),(windows,trials,combos) in expected.items():
  candidate=a.candidate_root/name;contexts=out/f'{name}_contexts{radius}.txt'
  run=subprocess.run([sys.executable,'-B',str(ROOT/'inherited/src/collect_source_contexts.py'),str(candidate/'machine.native.tm'),str(candidate/'sites.json'),str(candidate/'instructions.json'),str(contexts),str(radius)],check=True,capture_output=True,text=True)
  receipt=json.loads(run.stdout);assert receipt['contexts']==windows
  assert contexts.read_bytes()==(ROOT/f'{name}_contexts{radius}.txt').read_bytes()
  (out/f'{name}_contexts{radius}_receipt.json').write_text(run.stdout)
  merged=subprocess.run([str(exe),str(candidate/'machine.native.tm'),str(radius),'100',str(contexts)],check=True,capture_output=True,text=True)
  (out/f'{name}_merge{radius}_log.txt').write_text(merged.stderr)
  (out/f'{name}_merge{radius}_hits.jsonl').write_text(merged.stdout)
  match=re.search(r'DONE pairs (\d+) trials (\d+) combos (\d+) hits (\d+) seconds ',merged.stderr)
  assert match and tuple(map(int,match.groups()))==(18721,trials,combos,0)
  assert not merged.stdout.strip()
  records.append({'candidate':name,'radius':radius,'source_windows':windows,'pairs':18721,'trials':trials,'joint_row_pairs':combos,'hits':0})
result={'ok':True,'records':records,'scope':'Reproduces finite local search results, not a global state lower bound.'}
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

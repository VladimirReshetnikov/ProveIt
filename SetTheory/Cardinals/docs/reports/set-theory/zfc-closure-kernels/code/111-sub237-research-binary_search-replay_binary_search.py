#!/usr/bin/env python3
"""Replay the seven attributed finite search families in search_summary.json.

The default checks input integrity only. --profiles regenerates finite discovery
profiles and neutral substitutions. --full also reruns all seven searches. No
mode proves a lower bound on general machines or verifies a consistency theorem.
"""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path)
p=ap.add_mutually_exclusive_group();p.add_argument('--profiles',action='store_true');p.add_argument('--full',action='store_true')
a=ap.parse_args()
assert __debug__ and not sys.flags.optimize,'Run without -O/-OO'
receipt=json.loads((R/'search_summary.json').read_text())
for name,want in receipt['files_sha256'].items():
 assert hashlib.sha256((R/name).read_bytes()).hexdigest()==want,('input hash',name)
if not a.profiles and not a.full:
 print(json.dumps({'status':'INPUT_INTEGRITY_ONLY','verified_files':len(receipt['files_sha256']),'searches_rerun':False},indent=2));sys.exit(0)
assert a.output is not None,'Provide a fresh --output directory'
W=a.output.resolve();assert W!=R and not (W.exists() and any(W.iterdir())),'Output must be fresh and separate from inputs'
W.mkdir(parents=True,exist_ok=True);commands=[];compiled={}
def run(argv,stdout=None,stderr=None):
 commands.append([str(x) for x in argv])
 with (W/(stdout or 'command_stdout.log')).open('w') as out, (W/(stderr or 'command_stderr.log')).open('w') as err:
  p=subprocess.run([str(x) for x in argv],cwd=W,stdout=out,stderr=err)
 assert p.returncode==0,('command failed',argv,p.returncode)
def build(name):
 if name not in compiled:
  run(['c++','-O3','-std=c++17',R/(name+'.cpp'),'-o',W/name],name+'_compile.log',name+'_compile_errors.log');compiled[name]=W/name
 return compiled[name]
def same(got,expected):assert (W/got).read_bytes()==(R/expected).read_bytes(),('profile/result mismatch',got,expected)
run([build('empirical_contexts'),R/'input237.tm',R/'sites.txt','5',W/'profile237.txt'],'profile237.stdout','profile237.log');same('profile237.txt','profile237.txt')
run([build('empirical_contexts'),R/'input237.tm',R/'sites.txt','7',W/'profile237_r7.txt'],'profile237_r7.stdout','profile237_r7.log');same('profile237_r7.txt','profile237_r7.txt')
run([build('source_constrained_contexts'),R/'input237.tm',R/'sites.txt','5',W/'source_profile237.txt',R/'source_facts16.txt'],'source_profile237.stdout','source_profile237.log');same('source_profile237.txt','source_profile237.txt')
for radius,cap,profile,out in [(5,65,'profile237.txt','neutral237.txt'),(7,97,'profile237_r7.txt','neutral237_r7.txt'),(5,65,'source_profile237.txt','source_neutral237.txt')]:
 run([build('neutral_domains'),R/'input237.tm',str(radius),str(radius),str(cap),str(cap),W/profile],out,out+'.log');same(out,out)
if a.full:
 jobs=[
 ('helper_domains',['5','5','65','65',W/'neutral237.txt',W/'profile237.txt'],'helper237'),
 ('twohelper_domains',['5','5','65','65',W/'neutral237.txt',W/'profile237.txt'],'twohelper237'),
 ('staged_helpers',['5','5','65','65',W/'neutral237.txt',W/'profile237.txt','1'],'staged237'),
 ('offset_domains',[W/'profile237.txt','5','5','65','65'],'offset237'),
 ('helper_domains',['7','7','97','97',W/'neutral237_r7.txt',W/'profile237_r7.txt'],'helper237_r7'),
 ('helper_domains',['5','5','65','65',W/'source_neutral237.txt',W/'source_profile237.txt'],'source_helper237'),
 ('source_staged_helpers',['5','5','65','65',W/'source_neutral237.txt',W/'source_profile237.txt','0'],'source_staged237')]
 for exe,opts,stem in jobs:
  run([build(exe),R/'input237.tm',*opts],stem+'.txt',stem+'.log')
  same(stem+'.txt',stem+'.txt');assert 'FINISHED' in (W/(stem+'.log')).read_text()
  # Exclude elapsed time and compare every deterministic final counter.
  old=[l for l in (R/(stem+'.log')).read_text().splitlines() if l.startswith('FINISHED')][-1].split(' secs ')[0]
  new=[l for l in (W/(stem+'.log')).read_text().splitlines() if l.startswith('FINISHED')][-1].split(' secs ')[0]
  assert old==new,('deterministic search counters',stem,old,new)
result={'status':'FULL_FINITE_SEARCH_REPLAY_PASS' if a.full else 'PROFILE_AND_NEUTRAL_REPLAY_PASS','searches_rerun':a.full,'finite_profiles_regenerated':True,'commands':commands,'scope':receipt['warning']}
(W/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='commands'},indent=2))

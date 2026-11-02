#!/usr/bin/env python3
"""Read-only independent audit of concrete mask source and paired artifacts."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-concrete-mask-prototype'
OUT=Path('/tmp/ipra-compact-concrete-mask-pair-01')
WINDOW=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
SCALED=Path('/tmp/ipra-compact-list-mask-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
WINDOW_AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
SCALED_AUDIT=BASE/'reviews/compact44-list-mask-independent-audit'
SOURCE='7f3c735747e88ecf1dfbf9d6b759a578ec768a857d3d553c06e8656d7be76ece'
OBJECT='741c13117025cac74b3f94eb229f88f764aa101bf3cd9e4af3d4c0c43176cd0b'
SEED='1f94ce66997b99f723f9abb990ba91574d0574c10a56d0b514f210a930907c99'
LOG='e184d3ce3df1fbb06a99b6ea32268952dbc3454fb86af1b3154a76c62b27b2a4'
RECEIPT='65a893c524bff130c16e63687a9e0aa896f2246ac5a1e57fdca149096de59fbd'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/'
    paths=subprocess.run(['git','ls-tree','-r','--name-only','20b9a0a28d','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(paths)>=6 and prefix+'evidence/author.log' in paths and prefix+'evidence/peer.log' in paths,'complete committed packet')
    for name in paths:
        committed=subprocess.run(['git','show','20b9a0a28d:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(committed).hexdigest()==sha(ROOT/name),'committed byte drift '+name)
    terminal=(PKG/'evidence/terminal.txt').read_text()
    need(terminal.startswith('Observed outer session 23362 exit 0.\n') and terminal.endswith('PASS_PAIRED_COMPACT_CONCRETE_MASK '+RECEIPT+'\n') and 'PASS_PAIRED_COMPACT_CONCRETE_MASK '+RECEIPT in terminal,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    receipt=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(receipt['status']=='PASS_PAIRED_COMPACT_CONCRETE_MASK' and len(receipt['runs'])==2,'status')
    for p,h in receipt['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
    need(receipt['parent_audit']==json.loads((WINDOW_AUDIT/'CHECK.json').read_bytes()),'window parent receipt')
    parent_results=[]
    for parent in (SCALED_AUDIT,):
        q=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],capture_output=True,timeout=900)
        need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((parent/'CHECK.json').read_bytes()),'parent audit '+str(parent))
        parent_results.append(q.returncode)
    runs=[]
    for row,side in zip(receipt['runs'],('author','peer')):
        run=OUT/side;src=Path(row['command'][-3]);obj=run/'CompactConcreteMask.olean';log=run/'compiler.log'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits')
        need(sha(src)==sha(PKG/'CompactConcreteMask.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT,'object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and log.read_text()==row['stdout'],'log')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        lib=run/'lib';win=WINDOW/side/'lib';seed=lib/'DiophantineConsistency/CompactListMask.olean'
        wf={p.relative_to(win) for p in win.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
        need(lf==wf|{Path('DiophantineConsistency/CompactListMask.olean')},'overlay inventory')
        for rel in wf:need((lib/rel).resolve()==(win/rel).resolve() and sha(lib/rel)==sha(win/rel),'overlay '+str(rel))
        need(sha(seed)==sha(SCALED/side/'CompactListMask.olean')==row['seed_sha256']==SEED,'scaled seed')
        deps={str(PACKAGE/'Init.olean'),str(seed)}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct imports')
        reports=re.findall(r"^'CompactConcreteMask\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['concrete_bit_recipe','model_class','model_lt','model_origin','concrete_recipe'],'report names')
        need([raw for _,raw in reports]==row['axiom_reports'] and all({a.strip() for a in raw.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,raw in reports),'axioms')
        need(not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'unexpected compiler log')
        runs.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'seed_sha256':SEED,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_CONCRETE_MASK_AUDIT','source_commit':'20b9a0a28d','logs_commit':'20b9a0a28d','receipt_sha256':RECEIPT,'recorded_outer_session':23362,'recorded_outer_exit':0,'parent_audit_rerun_exits':parent_results,'runs':runs,'scope':'Concrete finite support mask symbolic identity and model digit classes; no retained MC bytes or graph port equality, simulation or iPRA; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()

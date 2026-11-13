#!/usr/bin/env python3
"""Read-only independent audit of heterogeneous carry source and paired artifacts."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-heterogeneous-carry-prototype'
OUT=Path('/tmp/ipra-compact-heterogeneous-carry-pair-01')
WINDOW=Path('/tmp/ipra-thirteen-parent-window-pair-01')
SCALED=Path('/tmp/ipra-compact-scaled-carry-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
WINDOW_AUDIT=BASE/'reviews/thirteen-model-parent-window-pair-independent-audit'
SCALED_AUDIT=BASE/'reviews/compact44-scaled-carry-independent-audit'
SOURCE='ce587b76912f7a0579a414a16c59c75a37b5e1b3db930ce57ff7a743c3fa7b2e'
OBJECT='9f666c0181717d70486d4323692ccc5bd9c28f7a0a6b92aedb4074c2e2d43462'
SEED='02e49f7e1a13bbc33859c203b5e93a91a16fadf2bb1d3e8d292ab29963cc4102'
LOG='a29b576365103b1cca3287c0a4f2a23574f43e0c1e73d0d1ebbca3d3f9aee3b7'
RECEIPT='c95c13e7980c80e98ff9bc0172f56b2f08999cef814b0bedac360884ceb903b9'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/'
    paths=subprocess.run(['git','ls-tree','-r','--name-only','b35ed42256','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
    need(len(paths)>=6 and prefix+'evidence/author.log' in paths and prefix+'evidence/peer.log' in paths,'complete committed packet')
    for name in paths:
        committed=subprocess.run(['git','show','b35ed42256:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(committed).hexdigest()==sha(ROOT/name),'committed byte drift '+name)
    terminal=(PKG/'evidence/terminal.txt').read_text()
    need('session 69417' in terminal and terminal.endswith('outer exit 0\n') and 'PASS_PAIRED_COMPACT_HETEROGENEOUS_CARRY '+RECEIPT in terminal,'outer observation')
    need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    receipt=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(receipt['status']=='PASS_PAIRED_COMPACT_HETEROGENEOUS_CARRY' and len(receipt['runs'])==2,'status')
    for p,h in receipt['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
    need(receipt['parent_audit']==json.loads((WINDOW_AUDIT/'CHECK.json').read_bytes()),'window parent receipt')
    parent_results=[]
    for parent in (WINDOW_AUDIT,SCALED_AUDIT):
        q=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],capture_output=True,timeout=900)
        need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((parent/'CHECK.json').read_bytes()),'parent audit '+str(parent))
        parent_results.append(q.returncode)
    runs=[]
    for row,side in zip(receipt['runs'],('author','peer')):
        run=OUT/side;src=Path(row['command'][-3]);obj=run/'CompactHeterogeneousCarry.olean';log=run/'compiler.log'
        need(row['label']==side and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits')
        need(sha(src)==sha(PKG/'CompactHeterogeneousCarry.lean')==row['source_sha256']==SOURCE,'source')
        need(sha(obj)==row['object_sha256']==OBJECT,'object')
        need(sha(log)==sha(PKG/'evidence'/(side+'.log'))==row['log_sha256']==LOG and log.read_text()==row['stdout'],'log')
        need(row['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'command')
        lib=run/'lib';win=WINDOW/side/'lib';seed=lib/'DiophantineConsistency/CompactDigitBound.olean'
        wf={p.relative_to(win) for p in win.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
        need(lf==wf|{Path('DiophantineConsistency/CompactDigitBound.olean')},'overlay inventory')
        for rel in wf:need((lib/rel).resolve()==(win/rel).resolve() and sha(lib/rel)==sha(win/rel),'overlay '+str(rel))
        need(sha(seed)==sha(SCALED/side/'CompactDigitBound.olean')==row['seed_sha256']==SEED,'scaled seed')
        deps={str(PACKAGE/'Init.olean'),str(seed),str(lib/'DiophantineConsistency/ArithmeticWindowCarry.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct imports')
        reports=re.findall(r"^'DiophantineConsistency\.CompactHeterogeneousCarry\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in reports]==['excess_le','carry_le','carry_column','end_around_carry'],'report names')
        need([raw for _,raw in reports]==row['axiom_reports'] and all({a.strip() for a in raw.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,raw in reports),'axioms')
        need(not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'unexpected compiler log')
        runs.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'seed_sha256':SEED,'recorded_compiler_exit':0,'recorded_deps_exit':0,'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_HETEROGENEOUS_CARRY_AUDIT','source_commit':'a863457ff0','logs_commit':'b35ed42256','receipt_sha256':RECEIPT,'recorded_outer_session':69417,'recorded_outer_exit':0,'parent_audit_rerun_exits':parent_results,'runs':runs,'scope':'Conditional all-model carry bound for externally finite family; no graph digit/mass/congruence proof, no fractional-rotation transfer, no iPRA; inherited provider and resource limitations.'},indent=2))
if __name__=='__main__':main()

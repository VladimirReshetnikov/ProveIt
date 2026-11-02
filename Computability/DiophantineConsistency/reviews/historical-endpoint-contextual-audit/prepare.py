#!/usr/bin/env python3
"""Make the bounded historical source view in a fresh direct /tmp directory."""
import argparse,hashlib,os,shutil,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent
HEAD='89dc5054338bba6fcdf742105203148252da2773';OLD='435062d125';SOURCE='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ModelCarrierCurrent.lean';OLDHASH='3f76453da57164d06bd338928d0e3d587df46851c77d5cbc4fbf858119719076';PATTERNS='42493869ab7a51e631c74c02ffe8e558ce353ba25d7208b3d9c8ecf05041a4dc'
def sha(b):return hashlib.sha256(b).hexdigest()
def run(cmd,**kw):return subprocess.run(cmd,check=True,timeout=180,**kw)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve()!=Path('/tmp').resolve() or not out.name.startswith('ipra-historical-audit-review-') or os.path.lexists(out):raise ValueError('need fresh direct /tmp/ipra-historical-audit-review-*')
 if shutil.disk_usage('/tmp').free<1024**3:raise ValueError('less than 1 GiB sampled free disk')
 patterns=(HERE/'sparse-patterns.txt').read_bytes()
 if sha(patterns)!=PATTERNS:raise ValueError('sparse patterns drift')
 run(['git','cat-file','-e',HEAD+'^{commit}'],cwd=ROOT)
 run(['git','clone','--shared','--no-checkout',str(ROOT),str(out)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 run(['git','-C',str(out),'sparse-checkout','init','--no-cone'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 run(['git','-C',str(out),'sparse-checkout','set','--no-cone','--stdin'],input=patterns,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 run(['git','-C',str(out),'checkout','--detach',HEAD],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 blob=run(['git','-C',str(out),'show',OLD+':'+SOURCE],stdout=subprocess.PIPE).stdout
 if sha(blob)!=OLDHASH:raise ValueError('historical source hash mismatch')
 (out/SOURCE).write_bytes(blob)
 status=run(['git','-C',str(out),'status','--short','--untracked-files=no'],stdout=subprocess.PIPE,text=True).stdout.splitlines()
 if status!=[' M '+SOURCE]:raise ValueError(('unexpected clone tracked changes',status))
 print('PREPARED_HISTORICAL_SOURCE_VIEW',out,'head',HEAD,'historical_source_sha256',OLDHASH)
if __name__=='__main__':main()

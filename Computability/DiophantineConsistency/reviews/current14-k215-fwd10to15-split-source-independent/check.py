from pathlib import Path
import hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-k215-fwd10to15-split-draft';template=root/'research/current14-k215-fwd09-split-retry01-draft';src=root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC';pins=json.loads((Path(__file__).parent/'source-pins.json').read_text());assert len(pins)==18 and set(pins)=={x.name for x in d.glob('*.lean')}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
data=(src/'KSource215Data.lean').read_text();assert hashlib.sha256((src/'KSource215Data.lean').read_bytes()).hexdigest()=='23b670c2b6ffd08fa173bbbe54faaf8989aac9b410a41a3332dee3f5fcaa5554';rmb=(src/'RMBisim.lean').read_text();assert '| .branch _ l r => allC f l && allC f r' in rmb
results={}
for i in range(10,16):
 end=f'def fwd{i+1} : CTree :=' if i<15 else 'def fwdCert : CTree :='
 s=data.split(f'def fwd{i} : CTree :=',1)[1].split(end,1)[0].strip();m=re.match(r'\.branch\s+(\d+)\s*',s);assert m;pos=m.end();groups=[]
 for _ in range(2):
  assert s[pos]=='(';start=pos;depth=0
  while True:
   if s[pos]=='(':depth+=1
   elif s[pos]==')':depth-=1
   pos+=1
   if depth==0:break
  groups.append(s[start:pos]);pos+=len(s[pos:])-len(s[pos:].lstrip())
 assert not s[pos:];counts=[len(re.findall(r'\.leaf\b',g)) for g in groups];assert counts==([44,45] if i<15 else [45,45]) and int(m[1])==counts[0]
 for side in ('Left','Right'):
  expected=(template/f'KSource215Fwd09{side}.lean').read_text().replace('fwd9',f'fwd{i}')
  assert (d/f'KSource215Fwd{i}{side}.lean').read_text()==expected
 original=(src/f'KSource215FwdCheck{i}.lean').read_text();imp='import BusyBeaver.ZFC.KSource215Data\n';assert original.count(imp)==1
 proposed=original.replace(imp,imp+f'import BusyBeaver.ZFC.KSource215Fwd{i}Left\nimport BusyBeaver.ZFC.KSource215Fwd{i}Right\n')
 before=f'theorem fwd_ok{i} : allC fwdF fwd{i} = true := by decide +kernel';assert proposed.count(before)==1
 after=f'theorem fwd_ok{i} : allC fwdF fwd{i} = true := by\n  change (allC fwdF fwd{i}Left && allC fwdF fwd{i}Right) = true\n  rw [fwd{i}Left_ok, fwd{i}Right_ok]\n  rfl';proposed=proposed.replace(before,after);proposed+=f'\n#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok{i}\n';assert proposed==(d/f'KSource215FwdCheck{i}.lean').read_text()
 results[str(i)]={'cut':int(m[1]),'left':counts[0],'right':counts[1]}
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-fwd09-split-retry01-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_ONLY','trees':results,'lean_run':False,'scope':'Six proposed source splits; child kernel checks and joins uncompiled'},indent=2))

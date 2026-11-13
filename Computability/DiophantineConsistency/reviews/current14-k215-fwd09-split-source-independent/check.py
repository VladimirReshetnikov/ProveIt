from pathlib import Path
import hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-k215-fwd09-split-draft';orig=root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck09.lean';data=root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean';rmb=root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean'
pins={orig:'1081f5dbe35de086481840dc57c19fd31776c18202cdc70c944a6a10c2f52d91',data:'23b670c2b6ffd08fa173bbbe54faaf8989aac9b410a41a3332dee3f5fcaa5554',rmb:'c18b757a0b981a6e78c7a1fbe449fe6d53f38039f7d99cdf0021b2a151166f81',d/'KSource215Fwd09Left.lean':'7a951dd61be5d34fbd00cece8140cbf2f0d05cb453a032711c2d3520575375c5',d/'KSource215Fwd09Right.lean':'25f1d17e3c5cc07c1ed1e29e76aa3f4171f4789c3dbd3afa586c63551705d308',d/'KSource215FwdCheck09.lean':'363c7725685da5281ecc91f0ac65cada6fed706dd439c9dd31c8b4122adfcc79'}
for p,h in pins.items():assert hashlib.sha256(p.read_bytes()).hexdigest()==h,str(p)
s=data.read_text().split('def fwd9 : CTree :=',1)[1].split('def fwd10 : CTree :=',1)[0].strip();m=re.match(r'\.branch\s+(\d+)\s*',s);assert m and m[1]=='44';pos=m.end();groups=[]
for i in range(2):
 assert s[pos]=='(';start=pos;depth=0
 while True:
  if s[pos]=='(':depth+=1
  elif s[pos]==')':depth-=1
  pos+=1
  if depth==0:break
 groups.append(s[start:pos]);pos+=len(s[pos:])-len(s[pos:].lstrip())
assert not s[pos:] and [len(re.findall(r'\.leaf\b',g)) for g in groups]==[44,45]
r=rmb.read_text();assert '| branch (cut : Nat) (l r : CTree)' in r and '| .branch _ l r => allC f l && allC f r' in r
for name,selector in [('Left','.branch _ l _ => l'),('Right','.branch _ _ r => r')]:
 text=(d/f'KSource215Fwd09{name}.lean').read_text();assert re.findall(r'^import (\S+)',text,re.M)==['BusyBeaver.ZFC.KSource215Data'];assert f'def fwd9{name} : CTree := match fwd9 with' in text and selector in text and '| _ => .empty' in text and f'theorem fwd9{name}_ok : allC fwdF fwd9{name} = true := by\n  decide +kernel' in text
x=orig.read_text();imp='import BusyBeaver.ZFC.KSource215Data\n';x=x.replace(imp,imp+'import BusyBeaver.ZFC.KSource215Fwd09Left\nimport BusyBeaver.ZFC.KSource215Fwd09Right\n');x=x.replace('theorem fwd_ok9 : allC fwdF fwd9 = true := by decide +kernel','theorem fwd_ok9 : allC fwdF fwd9 = true := by\n  change (allC fwdF fwd9Left && allC fwdF fwd9Right) = true\n  rw [fwd9Left_ok, fwd9Right_ok]');x+='\n#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok9\n';assert x==(d/'KSource215FwdCheck09.lean').read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-coherent-extension-refactor-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_ONLY','root_cut':44,'left_leaves':44,'right_leaves':45,'lean_run':False,'scope':'Proposed 2-child source split; definitional equality and memory feasibility untested'},indent=2))

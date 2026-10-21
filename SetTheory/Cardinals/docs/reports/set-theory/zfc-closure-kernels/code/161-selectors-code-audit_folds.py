"""Independent literal census and all-initial-tape checks of inherited folds in K215."""
from pathlib import Path
import argparse,json,hashlib
import check_joint_fold as ck
def encode(table):
 return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(table.items()))).encode()
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--parent-native',type=Path,required=True)
parser.add_argument('--candidate-native',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
a=parser.parse_args(); a.output.mkdir(parents=True,exist_ok=True)
OLD=a.parent_native;NEW=a.candidate_native
assert hashlib.sha256(OLD.read_bytes()).hexdigest()=='2efb7adf9cfcbea58197a2bde2610b22f58b647f05385bc716b036242be6fa6c'
assert hashlib.sha256(NEW.read_bytes()).hexdigest()=='2bae0de1f3388fc46c0558da3cf66d17e0d597ec0ae843731300e825f26fb3ba'
old,start=ck.read(OLD);new,nstart=ck.read(NEW)
assert start==nstart==0 and len(new)==430 and len({q for q,b in new})==215
Q={q for q,b in new};reach={0};todo=[0]
for q in todo:
 for b in(0,1):
  z=new[q,b][2]
  if z!=254 and z not in reach:reach.add(z);todo.append(z)
assert reach==Q
changed=[dict(state=q,read=b,old=old[q,b],new=new[q,b])for q,b in sorted(new)if old[q,b]!=new[q,b]]
assert len(changed)==36
assert {q for q,b in old}-Q=={185}
# Restore the source-context split at 164/183, preserving every unrelated row.
unfold164=dict(new);unfold164[205,0]=(0,1,183);unfold164[164,0]=(0,1,77)
unfold164[183,0]=(0,1,150);unfold164[183,1]=(1,1,98)
assert [(k,v)for k,v in new.items()if v[2]==164]==[((117,1),(1,1,164)),((205,0),(0,1,164))]
assert new[201,0]==(0,1,195) and new[201,1]==(1,1,196)
assert new[195,0]==(0,1,150) and new[196,0]==(0,1,77)
f164=ck.check(unfold164,new,0,0,164,183,radius=5,fuel=97)
# Restore the older 69/400 split in that table; both selectors remain allocated.
unfold69=dict(unfold164);unfold69[224,0]=(0,1,400);unfold69[69,0]=(0,1,105)
unfold69[400,0]=(0,1,104);unfold69[400,1]=(1,1,31)
assert [(k,v)for k,v in new.items()if v[2]==69]==[((53,1),(1,1,69)),((224,0),(0,1,69))]
assert new[213,0]==(0,1,92) and new[213,1]==(1,1,90)
assert new[92,0]==(0,1,104) and new[90,0]==(0,1,105)
f69=ck.check(unfold69,unfold164,0,0,69,400,radius=5,fuel=97)
# Primitive helper rewrite must be checked in the PRE-allocation partial table.
rewritten=dict(old);rewritten[81,0]=(0,-1,111)
three=[]
for left in(0,1):
 def execute(t):
  bits={-1:left,0:0};q=81;h=0
  for _ in range(3):
   assert h in bits
   w,d,z=t[q,bits[h]];bits[h]=w;q=z;h+=d
  return(q,h,bits)
 before,after=execute(old),execute(rewritten);assert before==after
 three.append(dict(left=left,state=before[0],head=before[1],tape=before[2]))
# Mutation controls must reject initially forced halting.
for label,O,N,keep,drop in [('164',unfold164,new,164,183),('69',unfold69,unfold164,69,400)]:
 bad=dict(N);bad[0,0]=(0,1,254)
 try:ck.check(O,bad,0,0,keep,drop,radius=5,fuel=97)
 except ValueError:pass
 else:raise AssertionError('Negative control accepted')
output={'status':'PASS_INDEPENDENT_K215_LITERAL_AND_INHERITED_FOLDS','native_sha256':hashlib.sha256(NEW.read_bytes()).hexdigest(),'working_states':215,'rows':430,'all_states_graph_reachable':True,'changed_retained_rows_from_partial216':36,'removed_native_states':[185],'marker164_incoming':[[117,1,1,1,164],[205,0,0,1,164]],'marker69_incoming':[[53,1,1,1,69],[224,0,0,1,69]],'all_tape_fold164':f164,'all_tape_fold69':f69,'helper81_preallocation_three_step':three,'negative_control':'Both initial forced-halt mutations rejected','scope':'Independent literal finite census, exact surviving marker conditions, two all-initial-tape inherited local folds, and preallocation81 helper rewrite. These are not a proof of the complete newly allocated runtime; that separately requires all primitive cases and blank startup.'}
(a.output/'review215.json').write_text(json.dumps(output,indent=2)+'\n')
(a.output/'unfolded216.native.tm').write_bytes(encode(unfold164));(a.output/'unfolded217.native.tm').write_bytes(encode(unfold69))
print(json.dumps(output,indent=2))

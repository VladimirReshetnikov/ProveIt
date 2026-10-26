"""Replay the explicit private Horn-wire basis certificate."""
import copy
from operations import poly,terms,add,mul,subst,compact,need

def build(source,cert):
 e=copy.deepcopy(source);rows=[poly(r['terms'])for r in e['residuals']];edits={i:poly(t)for i,t in cert['edits']};deleted=set(cert['removed_rows']);erase=cert['erase_private_variable'];new=[];labels=[]
 for j,r in enumerate(rows):
  if j in deleted:continue
  new.append(edits.get(j,{m:c for m,c in r.items()if erase not in m}));labels.append(e['residuals'][j]['label'])
 new.append(poly(cert['new_row']));labels.append('shared F times S');e['variables'].append(cert['new_variable']);i,v=cert['renamed_variable'];e['variables'][i]=v
 out=compact(e,new)
 for row,label in zip(out['residuals'],labels):row['label']=label
 return out

"""Persistent HiGHS restricted master for integer SOS pricing.

Uses SciPy's already-installed native backend. Numerical results remain heuristic;
all certificates must pass the producer's separate exact reconstruction.
"""
import numpy as np
from scipy.sparse import eye
from scipy.optimize._highspy import _core
from types import SimpleNamespace

class WarmMaster:
 def __init__(self):
  self.h=None;self.rays=[];self.slacks=[];self.loaded=0
 def _add(self,A,cost):
  A=A.tocsc();h=self.h;first=h.getNumCol();n=A.shape[1]
  status=h.addCols(n,np.asarray(cost,float),np.zeros(n),np.full(n,np.inf),A.nnz,np.asarray(A.indptr,np.int32),np.asarray(A.indices,np.int32),np.asarray(A.data,float))
  assert status!=_core.HighsStatus.kError,status
  if status==_core.HighsStatus.kWarning:print("HiGHS column warning; final exact verification remains mandatory",flush=True)
  return list(range(first,first+n))
 def solve(self,A,target):
  fresh=self.h is None
  if fresh:
   self.h=_core._Highs();h=self.h
   h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
   h.setOptionValue('primal_feasibility_tolerance',1e-9);h.setOptionValue('dual_feasibility_tolerance',1e-9)
   m=A.shape[0]
   assert h.addRows(m,np.full(m,-np.inf),np.asarray(target,float),0,np.zeros(m+1,np.int32),np.empty(0,np.int32),np.empty(0,float))==_core.HighsStatus.kOk
   self.rays=self._add(A,np.zeros(A.shape[1]));self.slacks=self._add(-eye(m,format='csc'),np.ones(m));self.loaded=A.shape[1]
   h.setOptionValue('solver','ipm')
  else:
   h=self.h
   assert A.shape[1]>=self.loaded,'Warm master does not support column pruning'
   if A.shape[1]>self.loaded:self.rays.extend(self._add(A[:,self.loaded:],np.zeros(A.shape[1]-self.loaded)))
   self.loaded=A.shape[1];h.setOptionValue('solver','simplex');h.setOptionValue('simplex_strategy',4)
   h.setOptionValue('presolve','off')
  h.setOptionValue('time_limit',h.getRunTime()+300)
  h.run();status=h.getModelStatus();s=h.getSolution()
  x=np.array([s.col_value[j] for j in self.rays+self.slacks])
  return SimpleNamespace(success=status==_core.HighsModelStatus.kOptimal,fun=h.getObjectiveValue(),x=x,ineqlin=SimpleNamespace(marginals=np.asarray(s.row_dual)),message=h.modelStatusToString(status))

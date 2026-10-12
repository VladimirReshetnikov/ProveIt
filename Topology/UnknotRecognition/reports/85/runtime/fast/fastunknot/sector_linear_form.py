"""Exact sparse linear forms with the dense sequence interface for rank tests."""
from collections.abc import Sequence
from operator import index


class SparseLinearForm(Sequence):
    """Own nonzero coefficients; materialize zeros only when iterated."""
    def __init__(self,width,coefficients):
        self.width=width
        self.coefficients={i:value for i,value in coefficients.items()if value}

    def __len__(self):return self.width

    def __getitem__(self,item):
        if isinstance(item,slice):
            return tuple(self.coefficients.get(i,0)for i in range(self.width)[item])
        item=index(item)
        if item<0:item+=self.width
        if not 0<=item<self.width:raise IndexError('linear form index out of range')
        return self.coefficients.get(item,0)

    def __iter__(self):
        return (self.coefficients.get(i,0)for i in range(self.width))

    def dot(self,vector):
        return sum(value*vector[i]for i,value in self.coefficients.items())

    def project(self,forms,width):
        return tuple(sum(value*forms[i][j]for i,value in self.coefficients.items())for j in range(width))

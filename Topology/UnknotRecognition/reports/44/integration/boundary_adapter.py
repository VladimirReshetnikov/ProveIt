"""Additive research adapter for the maintained BoundaryTait interface.

The maintained geometry's partition() checks MUST run. This module neither
imports a recognizer nor returns a knot verdict. Its batch path validates all
matchings before compiling their terminal partitions into a merge trie.
Upstream integration is not automatically enabled by importing this file.
"""
from __future__ import annotations
from terminal_updates.linear import Budget, tick
from terminal_updates.terminal import SignedGraph,ExactObserver
from terminal_updates.batch import MergePlan

class ModularBoundaryObserver:
    def __init__(self, boundary_tait, budget: Budget | None = None):
        self.geometry=boundary_tait
        graph=SignedGraph.from_laplacian(boundary_tait.laplacian)
        self.engine=ExactObserver(graph,boundary_tait.terminals,budget)

    @staticmethod
    def phased(value: int, data: dict):
        unit=((1,0),(0,-1),(-1,0),(0,1))[data['phase']]
        return (unit[0]*value,unit[1]*value),data

    def evaluate(self,pairs):
        data=self.geometry.partition(pairs)
        if data['shadow_components']!=1:return (0,0),data
        return self.phased(self.engine.query(data['partition']),data)

    def evaluate_many(self,matchings,budget: Budget | None=None):
        metadata=[];partitions=[];accepted=[]
        for i,pairs in enumerate(matchings):
            tick(budget,1)
            data=self.geometry.partition(pairs);metadata.append(data)
            if data['shadow_components']==1:
                accepted.append(i);partitions.append(data['partition'])
        plan=MergePlan.compile(len(self.engine.terminals),partitions)
        values=plan.evaluate(self.engine,budget) if partitions else []
        out=[((0,0),data) for data in metadata]
        for i,value in zip(accepted,values):out[i]=self.phased(value,metadata[i])
        return out

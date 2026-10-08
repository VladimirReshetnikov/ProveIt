"""Exact Frobenius kernels for the ProveIt unknot-recognition project."""
from .kernel import CompiledPlan, contract, contract_reference
from .subset import subset_product, subset_product_fast, subset_product_sparse
__all__ = ["CompiledPlan", "contract", "contract_reference", "subset_product", "subset_product_fast", "subset_product_sparse"]
__version__ = "0.1.0"

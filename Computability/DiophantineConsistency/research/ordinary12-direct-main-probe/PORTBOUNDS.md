# Generic port-bound casting helper

`DirectPortBounds.bounds` proves the three `ports beta K L H` bounds from explicit inequalities in an arbitrary IΣ₁ model. It is generic in the four natural numerals; this lets a client specialize the high port without reducing the large fixed addition during kernel checking.

`run-portbounds.py` produced `observations/portbounds-attempt01/` with exit 0 and no reported warnings. Source SHA-256 is `40a3015bb7b3b526f14e6403121055845ff70d368c789daa5ee48567cfce2ae8`, output object is `e3299142c98787101f5f96cdddfe25a0faea2bd41b40311be8fdd005d15ddfa6`, and the axiom report lists `propext`, `Classical.choice`, and `Quot.sound`. The inherited source-object, package, and dynamic ancestry and temporary-path limitations are recorded in the receipt.

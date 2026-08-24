/-!
# Native support shim for finite Ramsey-paper certificates

This intentionally tiny module lets Lake build and load the C implementation
of the reviewed prefix-extension counter without compiling the entire Mathlib
dependency closure into a shared library.
-/

def RamseyCounterShim.loaded : Bool := true

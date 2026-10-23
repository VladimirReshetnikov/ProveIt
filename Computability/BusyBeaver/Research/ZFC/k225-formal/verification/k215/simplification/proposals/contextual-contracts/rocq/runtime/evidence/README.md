# Evidence layout

`core/` is the accepted nine-module clean build and recursive kernel check.
`templates/` is the accepted final added module compile against the exact
recorded core objects. `development/initial_template_compile/` preserves the
first failed draft and is not accepted evidence for the final module.

The original receipts retain their execution-time absolute compiler paths.
Those paths are provenance, not requirements for reproduction; `../build.py`
uses PATH or an explicitly provided toolchain. Compiled `.vo` files are not
shipped. Source and object hashes record what was checked.

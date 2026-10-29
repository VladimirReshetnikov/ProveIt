# Local normalization: additional client build

The local marker simplification in commit `74f0ca2a17` was initially checked against `ArithmeticConstructionBound`, while its other tracked direct client, `HACurrentEquation2011`, lacked a usable cached bridge. A subsequent isolated build of the current `HACurrentEquation2011` source succeeded with an empty log. It selected the final `ArithmeticLocalNormalization` object from the earlier paired validation, built from source matching the committed file. This is a final-source client build, not a baseline/final client comparison.

The reconstruction compiled 37 modules from current source, including the missing C222 interpretation chain, `HACurrentAssembly2011`, `ArithmeticSoundness2011`, and `HACurrentPolynomialBridge2011`. Initial attempts exposed cached providers with older IΣ2 assumptions; affected providers were rebuilt from current source. The build also used historical cached transitive objects whose entire source closure was not verified, so it is not a clean source-current rebuild of the full dependency graph.

- Endpoint source SHA-256: `b041f0815e52985a3c60eed5bed9648a62f1bfd5f495d72d2ce3797b94e71e3e`.
- Selected local-normalization object SHA-256: `e394b8520d8b1940746dd7411cc28dd136d14a117e7271a86905f500ad8ba4b5`; its source SHA-256: `5d0ac1625dd03ed79f50e9d71edac75bb14547f6f6961316769c887db31c905b`.
- Endpoint object SHA-256: `139adc47e8f48eee0df7fe0ab7f996dd675967473e764fdd9036e8d9fab6e6d1`.
- External build records: `/tmp/hacurrent-client-audit-20261029/records.json`, SHA-256 `bd6416cf49c103faf6a5b5397d2ca88f732f526241b4ea7758113bc219fad255`.
- External build script: `/tmp/hacurrent-client-audit-20261029/build.py`, SHA-256 `a93c8ca6de85a28413fb5c9d186883e9249d78681846036e64d3cccedf3bdf87`.

The temporary build objects and records are not included in this note and may later be unavailable.

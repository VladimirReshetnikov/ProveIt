# Exact Foundation bounded refutation: conditional author replay

The guarded author run `/tmp/ipra-zfc-witness-bound-mypp5ntd` passed. It rebuilds `StrictSigmaOneInduction` from the current source, defines `boundedRefutation := ∃ b, bnd rho` for the literal Foundation ZFC refutation, and proves its one-bound matrix is `Hierarchy Σ 0`. For any language map f and intuitionistic theory T in the target language, `mappedZFCNegationOfBound` constructs `(lMap f sourceSentence)ᴺ ↔ ¬native (lMap f rho)` from three explicit T-proofs: `(lMap f rho)ᴺ → (lMap f boundedRefutation)ᴺ`, the translated bounded sentence implies double-negated native bounded sentence, and native bounded sentence implies native rho. None of these premises is proved here. In particular, the syntactic Σ₀ certificate is not an iPRA decision proof; the native reader's correspondence with the separate PAHF interpretation is not established.

The replay authenticates previously replayed mapped-ZFC and pure witness-bridge parents, the direct ZFC object anchors, five external Foundation anchors and Lean executable. The 1,136-object HA/ZF boundary is not rehashed in this narrow replay; remaining HA/Foundation/package ancestry and inherited source/object correspondence remain historical. `StrictSigmaOneInduction` contains other semantic results, but this client uses only its syntactic bounding definition and hierarchy certificate. Check logs retain Lean metatheory axiom reports. Independent replay is required.

Replay: `python3 Computability/DiophantineConsistency/research/ipra-refutation-logic/build-zfc-witness-bound.py`.

- `StrictSigmaOneInduction`: source `8890617ceaf7da27827cd5557191ca5c7b439431cfe13b1e19114926f77a13b3`, object `a3ed47478745403d6fc90ad6d6082a56cba175465d6161dca6a1278007742735`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRAFoundationZFCWitnessBound`: source `72ec1237b4478c92d15fe0d0e8066041f9d55192fe643fd07da33ab59407f5c9`, object `53b14bdea1274963f3424850b51908a98f4c813ab97b42f063d4466df39d7f19`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRAFoundationZFCWitnessBoundChecks`: source `98ee459ced7b9dcda4cf3c19cc1ef759ff8dbd44b7c3be3e57ecb571dd762ff6`, object `37b49db8e19db278c135c8b9d05e008021dad14a75349d150d7aaea2a5247f7d`, full log `4054da5318e7be53ccfbdd5e05d273ca48d42ca3ce887b4ec9a4c1b427f0bb97`.

State `97d3457fba9349fb9bc0d85a8d6d7548ddbff8f756610cb0ec5ec57604040fec`; manifest `978ed263c921a276c40c050ee3d120278f75016e59181b4c12e306a3c0a8768d`.

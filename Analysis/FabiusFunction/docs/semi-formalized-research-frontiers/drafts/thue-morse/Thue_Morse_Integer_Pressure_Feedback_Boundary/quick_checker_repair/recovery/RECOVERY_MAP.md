# Recovery map for existing companion archives

All ten original ZIPs were read without extraction or modification. Every one of their 178 members matches existing source bytes and the original source manifests. No data was regenerated.

## Boundary source and five trace parts

Extract ProveIt_Thue_Morse_Boundary_Source.zip first. Extract each of the following five trace ZIPs into the same parent directory. They all carry the prefix ProveIt_Thue_Morse_First_Feedback_Boundary/data/certificates/. Together they supply precisely 68 compressed traces, m=2 through 69, without duplicates. The moment sets are interleaved, not contiguous.

The repaired checker takes the resulting ProveIt_Thue_Morse_First_Feedback_Boundary/data/ directory as --data-dir. It requires all 158 sealed certificate inputs (JSON, traces and original comparison certificates).

- ProveIt_Thue_Morse_Boundary_Traces_1_of_5.zip
  - Bytes: 8945968
  - SHA256: 5c7c03baeace61e3ecfcc836562abf3d01a6c89c95f115bd056d226763ec61d1
  - Moments: 8, 14, 15, 20, 29, 33, 36, 44, 45, 54, 55, 60, 69
- ProveIt_Thue_Morse_Boundary_Traces_2_of_5.zip
  - Bytes: 8947946
  - SHA256: cd69351c91bca1373cb345184897cec01f53ba8819ef32efc9bce8380545d0b7
  - Moments: 9, 13, 16, 24, 25, 30, 39, 42, 47, 53, 56, 61, 68
- ProveIt_Thue_Morse_Boundary_Traces_3_of_5.zip
  - Bytes: 8944874
  - SHA256: 1625fcdd74d0b4a95c0c0eec9989ce9f631d7d5f1070b526daa38bba4797fe98
  - Moments: 3, 5, 10, 19, 23, 26, 34, 35, 40, 49, 52, 57, 62, 67
- ProveIt_Thue_Morse_Boundary_Traces_4_of_5.zip
  - Bytes: 8944915
  - SHA256: 3e6c3a4d9e84b39cbb43d4cf4aaef78af45107fc45f31c95519b59e4c377acdd
  - Moments: 2, 7, 12, 17, 21, 28, 32, 37, 41, 48, 51, 58, 63, 66
- ProveIt_Thue_Morse_Boundary_Traces_5_of_5.zip
  - Bytes: 8944838
  - SHA256: 1dc919a9347f1286ebdc32382631e1d1063aeac6a28b1796644bad3965388c14
  - Moments: 4, 6, 11, 18, 22, 27, 31, 38, 43, 46, 50, 59, 64, 65

## All-orders source and five interval parts

Extract ProveIt_Thue_Morse_All_Integer_Orders.zip first, then extract these five ZIPs into that package root, alongside README.md. They supply data/interval_m002.json through data/interval_m111.json. These 110 JSON files are separate from the 68 boundary traces and are not inputs to the repaired boundary quick checker.

- ProveIt_Thue_Morse_All_Orders_Intervals_01.zip
  - Bytes: 7076103
  - SHA256: 0a4205474aee58c8625d201618b5f219ba2da820c12eb189389daefc7f4ea153
  - Moments: 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66
- ProveIt_Thue_Morse_All_Orders_Intervals_02.zip
  - Bytes: 7378896
  - SHA256: b8a4f098dbd55fb49b9e997f5663402aa3a0e449bde161e6426322b0b7293e8d
  - Moments: 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83
- ProveIt_Thue_Morse_All_Orders_Intervals_03.zip
  - Bytes: 7618880
  - SHA256: 37c976aaa6363c7579ea53814e751f1cd82804d782b9b1d77697f3ba82fafafc
  - Moments: 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95
- ProveIt_Thue_Morse_All_Orders_Intervals_04.zip
  - Bytes: 7257793
  - SHA256: 89f5d53d2ca6e0705de3c03b209c0e3b07b2361d67d82fdddc3376691f18d966
  - Moments: 96, 97, 98, 99, 100, 101, 102, 103, 104
- ProveIt_Thue_Morse_All_Orders_Intervals_05.zip
  - Bytes: 6687479
  - SHA256: 650db338b03faf4105e61e6bd29cf25814bede2bdb973b394de55374157966ea
  - Moments: 105, 106, 107, 108, 109, 110, 111

## Reconciliation evidence

recovery_map.json gives every member name, exact byte count, SHA256 and original source-relative path. The original boundary manifest, all-orders chunk manifest and all-orders production manifest are preserved beside it. reconcile_archives.py repeats all comparisons read-only with explicit failures under Python -O. It does not extract ZIP entries or rewrite source files.

## Matching main source archives

- ProveIt_Thue_Morse_Boundary_Source.zip
  - Bytes: 594390
  - SHA256: 114fb0a1f878e1ac9cd73dfb27387787f9198e88b6b313ed7a1897e6baa9987e
- ProveIt_Thue_Morse_All_Integer_Orders.zip
  - Bytes: 2878822
  - SHA256: 1c5323125ff09a2e95e6e0d6102488e571099a96c0c7e02da740664de4729f9a

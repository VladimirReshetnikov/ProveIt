module
public import PA196.Startup.S000
public import PA196.Startup.S001
public import PA196.Startup.S002
public import PA196.Startup.S003
public import PA196.Startup.S004
public import PA196.Startup.S005
public import PA196.Startup.S006
public import PA196.Startup.S007
public import PA196.Startup.S008
public import PA196.Startup.S009
public import PA196.Startup.S010
public import PA196.Startup.S011
public import PA196.Startup.S012
public import PA196.Startup.S013
public import PA196.Startup.S014
public import PA196.Startup.S015
public import PA196.Startup.S016
public import PA196.Startup.S017
public import PA196.Startup.S018
public import PA196.Startup.S019
public import PA196.Startup.S020
public import PA196.Startup.S021
public import PA196.Startup.S022
public import PA196.Startup.S023
public import PA196.Startup.S024
public import PA196.Startup.S025
public import PA196.Startup.S026
public import PA196.Startup.S027
public import PA196.Startup.S028
public import PA196.Startup.S029
public import PA196.Startup.S030
public import PA196.Startup.S031
public import PA196.Startup.S032
public import PA196.Startup.S033
public import PA196.Startup.S034
public import PA196.Startup.S035
public import PA196.Startup.S036
public import PA196.Startup.S037
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private theorem compose {M : TMN} {a b c : Conf} {n m : Nat}
    (ha : run M n a = some b) (hb : run M m b = some c) :
    run M (n+m) a = some c := by rw [run_add,ha]; exact hb

/-- The complete blank-tape startup, composed from bounded kernel checks. -/
theorem startup_exact : run Literal.machine 58154 blank = some clean := by
  have step0000 := run0000
  have step0001 := compose step0000 run0001
  have step0002 := compose step0001 run0002
  have step0003 := compose step0002 run0003
  have step0004 := compose step0003 run0004
  have step0005 := compose step0004 run0005
  have step0006 := compose step0005 run0006
  have step0007 := compose step0006 run0007
  have step0008 := compose step0007 run0008
  have step0009 := compose step0008 run0009
  have step0010 := compose step0009 run0010
  have step0011 := compose step0010 run0011
  have step0012 := compose step0011 run0012
  have step0013 := compose step0012 run0013
  have step0014 := compose step0013 run0014
  have step0015 := compose step0014 run0015
  have step0016 := compose step0015 run0016
  have step0017 := compose step0016 run0017
  have step0018 := compose step0017 run0018
  have step0019 := compose step0018 run0019
  have step0020 := compose step0019 run0020
  have step0021 := compose step0020 run0021
  have step0022 := compose step0021 run0022
  have step0023 := compose step0022 run0023
  have step0024 := compose step0023 run0024
  have step0025 := compose step0024 run0025
  have step0026 := compose step0025 run0026
  have step0027 := compose step0026 run0027
  have step0028 := compose step0027 run0028
  have step0029 := compose step0028 run0029
  have step0030 := compose step0029 run0030
  have step0031 := compose step0030 run0031
  have step0032 := compose step0031 run0032
  have step0033 := compose step0032 run0033
  have step0034 := compose step0033 run0034
  have step0035 := compose step0034 run0035
  have step0036 := compose step0035 run0036
  have step0037 := compose step0036 run0037
  have step0038 := compose step0037 run0038
  have step0039 := compose step0038 run0039
  have step0040 := compose step0039 run0040
  have step0041 := compose step0040 run0041
  have step0042 := compose step0041 run0042
  have step0043 := compose step0042 run0043
  have step0044 := compose step0043 run0044
  have step0045 := compose step0044 run0045
  have step0046 := compose step0045 run0046
  have step0047 := compose step0046 run0047
  have step0048 := compose step0047 run0048
  have step0049 := compose step0048 run0049
  have step0050 := compose step0049 run0050
  have step0051 := compose step0050 run0051
  have step0052 := compose step0051 run0052
  have step0053 := compose step0052 run0053
  have step0054 := compose step0053 run0054
  have step0055 := compose step0054 run0055
  have step0056 := compose step0055 run0056
  have step0057 := compose step0056 run0057
  have step0058 := compose step0057 run0058
  have step0059 := compose step0058 run0059
  have step0060 := compose step0059 run0060
  have step0061 := compose step0060 run0061
  have step0062 := compose step0061 run0062
  have step0063 := compose step0062 run0063
  have step0064 := compose step0063 run0064
  have step0065 := compose step0064 run0065
  have step0066 := compose step0065 run0066
  have step0067 := compose step0066 run0067
  have step0068 := compose step0067 run0068
  have step0069 := compose step0068 run0069
  have step0070 := compose step0069 run0070
  have step0071 := compose step0070 run0071
  have step0072 := compose step0071 run0072
  have step0073 := compose step0072 run0073
  have step0074 := compose step0073 run0074
  have step0075 := compose step0074 run0075
  have step0076 := compose step0075 run0076
  have step0077 := compose step0076 run0077
  have step0078 := compose step0077 run0078
  have step0079 := compose step0078 run0079
  have step0080 := compose step0079 run0080
  have step0081 := compose step0080 run0081
  have step0082 := compose step0081 run0082
  have step0083 := compose step0082 run0083
  have step0084 := compose step0083 run0084
  have step0085 := compose step0084 run0085
  have step0086 := compose step0085 run0086
  have step0087 := compose step0086 run0087
  have step0088 := compose step0087 run0088
  have step0089 := compose step0088 run0089
  have step0090 := compose step0089 run0090
  have step0091 := compose step0090 run0091
  have step0092 := compose step0091 run0092
  have step0093 := compose step0092 run0093
  have step0094 := compose step0093 run0094
  have step0095 := compose step0094 run0095
  have step0096 := compose step0095 run0096
  have step0097 := compose step0096 run0097
  have step0098 := compose step0097 run0098
  have step0099 := compose step0098 run0099
  have step0100 := compose step0099 run0100
  have step0101 := compose step0100 run0101
  have step0102 := compose step0101 run0102
  have step0103 := compose step0102 run0103
  have step0104 := compose step0103 run0104
  have step0105 := compose step0104 run0105
  have step0106 := compose step0105 run0106
  have step0107 := compose step0106 run0107
  have step0108 := compose step0107 run0108
  have step0109 := compose step0108 run0109
  have step0110 := compose step0109 run0110
  have step0111 := compose step0110 run0111
  have step0112 := compose step0111 run0112
  have step0113 := compose step0112 run0113
  have step0114 := compose step0113 run0114
  have step0115 := compose step0114 run0115
  have step0116 := compose step0115 run0116
  have step0117 := compose step0116 run0117
  have step0118 := compose step0117 run0118
  have step0119 := compose step0118 run0119
  have step0120 := compose step0119 run0120
  have step0121 := compose step0120 run0121
  have step0122 := compose step0121 run0122
  have step0123 := compose step0122 run0123
  have step0124 := compose step0123 run0124
  have step0125 := compose step0124 run0125
  have step0126 := compose step0125 run0126
  have step0127 := compose step0126 run0127
  have step0128 := compose step0127 run0128
  have step0129 := compose step0128 run0129
  have step0130 := compose step0129 run0130
  have step0131 := compose step0130 run0131
  have step0132 := compose step0131 run0132
  have step0133 := compose step0132 run0133
  have step0134 := compose step0133 run0134
  have step0135 := compose step0134 run0135
  have step0136 := compose step0135 run0136
  have step0137 := compose step0136 run0137
  have step0138 := compose step0137 run0138
  have step0139 := compose step0138 run0139
  have step0140 := compose step0139 run0140
  have step0141 := compose step0140 run0141
  have step0142 := compose step0141 run0142
  have step0143 := compose step0142 run0143
  have step0144 := compose step0143 run0144
  have step0145 := compose step0144 run0145
  have step0146 := compose step0145 run0146
  have step0147 := compose step0146 run0147
  have step0148 := compose step0147 run0148
  have step0149 := compose step0148 run0149
  have step0150 := compose step0149 run0150
  have step0151 := compose step0150 run0151
  have step0152 := compose step0151 run0152
  have step0153 := compose step0152 run0153
  have step0154 := compose step0153 run0154
  have step0155 := compose step0154 run0155
  have step0156 := compose step0155 run0156
  have step0157 := compose step0156 run0157
  have step0158 := compose step0157 run0158
  have step0159 := compose step0158 run0159
  have step0160 := compose step0159 run0160
  have step0161 := compose step0160 run0161
  have step0162 := compose step0161 run0162
  have step0163 := compose step0162 run0163
  have step0164 := compose step0163 run0164
  have step0165 := compose step0164 run0165
  have step0166 := compose step0165 run0166
  have step0167 := compose step0166 run0167
  have step0168 := compose step0167 run0168
  have step0169 := compose step0168 run0169
  have step0170 := compose step0169 run0170
  have step0171 := compose step0170 run0171
  have step0172 := compose step0171 run0172
  have step0173 := compose step0172 run0173
  have step0174 := compose step0173 run0174
  have step0175 := compose step0174 run0175
  have step0176 := compose step0175 run0176
  have step0177 := compose step0176 run0177
  have step0178 := compose step0177 run0178
  have step0179 := compose step0178 run0179
  have step0180 := compose step0179 run0180
  have step0181 := compose step0180 run0181
  have step0182 := compose step0181 run0182
  have step0183 := compose step0182 run0183
  have step0184 := compose step0183 run0184
  have step0185 := compose step0184 run0185
  have step0186 := compose step0185 run0186
  have step0187 := compose step0186 run0187
  have step0188 := compose step0187 run0188
  have step0189 := compose step0188 run0189
  have step0190 := compose step0189 run0190
  have step0191 := compose step0190 run0191
  have step0192 := compose step0191 run0192
  have step0193 := compose step0192 run0193
  have step0194 := compose step0193 run0194
  have step0195 := compose step0194 run0195
  have step0196 := compose step0195 run0196
  have step0197 := compose step0196 run0197
  have step0198 := compose step0197 run0198
  have step0199 := compose step0198 run0199
  have step0200 := compose step0199 run0200
  have step0201 := compose step0200 run0201
  have step0202 := compose step0201 run0202
  have step0203 := compose step0202 run0203
  have step0204 := compose step0203 run0204
  have step0205 := compose step0204 run0205
  have step0206 := compose step0205 run0206
  have step0207 := compose step0206 run0207
  have step0208 := compose step0207 run0208
  have step0209 := compose step0208 run0209
  have step0210 := compose step0209 run0210
  have step0211 := compose step0210 run0211
  have step0212 := compose step0211 run0212
  have step0213 := compose step0212 run0213
  have step0214 := compose step0213 run0214
  have step0215 := compose step0214 run0215
  have step0216 := compose step0215 run0216
  have step0217 := compose step0216 run0217
  have step0218 := compose step0217 run0218
  have step0219 := compose step0218 run0219
  have step0220 := compose step0219 run0220
  have step0221 := compose step0220 run0221
  have step0222 := compose step0221 run0222
  have step0223 := compose step0222 run0223
  have step0224 := compose step0223 run0224
  have step0225 := compose step0224 run0225
  have step0226 := compose step0225 run0226
  have step0227 := compose step0226 run0227
  have step0228 := compose step0227 run0228
  have step0229 := compose step0228 run0229
  have step0230 := compose step0229 run0230
  have step0231 := compose step0230 run0231
  have step0232 := compose step0231 run0232
  have step0233 := compose step0232 run0233
  have step0234 := compose step0233 run0234
  have step0235 := compose step0234 run0235
  have step0236 := compose step0235 run0236
  have step0237 := compose step0236 run0237
  have step0238 := compose step0237 run0238
  have step0239 := compose step0238 run0239
  have step0240 := compose step0239 run0240
  have step0241 := compose step0240 run0241
  have step0242 := compose step0241 run0242
  have step0243 := compose step0242 run0243
  have step0244 := compose step0243 run0244
  have step0245 := compose step0244 run0245
  have step0246 := compose step0245 run0246
  have step0247 := compose step0246 run0247
  have step0248 := compose step0247 run0248
  have step0249 := compose step0248 run0249
  have step0250 := compose step0249 run0250
  have step0251 := compose step0250 run0251
  have step0252 := compose step0251 run0252
  have step0253 := compose step0252 run0253
  have step0254 := compose step0253 run0254
  have step0255 := compose step0254 run0255
  have step0256 := compose step0255 run0256
  have step0257 := compose step0256 run0257
  have step0258 := compose step0257 run0258
  have step0259 := compose step0258 run0259
  have step0260 := compose step0259 run0260
  have step0261 := compose step0260 run0261
  have step0262 := compose step0261 run0262
  have step0263 := compose step0262 run0263
  have step0264 := compose step0263 run0264
  have step0265 := compose step0264 run0265
  have step0266 := compose step0265 run0266
  have step0267 := compose step0266 run0267
  have step0268 := compose step0267 run0268
  have step0269 := compose step0268 run0269
  have step0270 := compose step0269 run0270
  have step0271 := compose step0270 run0271
  have step0272 := compose step0271 run0272
  have step0273 := compose step0272 run0273
  have step0274 := compose step0273 run0274
  have step0275 := compose step0274 run0275
  have step0276 := compose step0275 run0276
  have step0277 := compose step0276 run0277
  have step0278 := compose step0277 run0278
  have step0279 := compose step0278 run0279
  have step0280 := compose step0279 run0280
  have step0281 := compose step0280 run0281
  have step0282 := compose step0281 run0282
  have step0283 := compose step0282 run0283
  have step0284 := compose step0283 run0284
  have step0285 := compose step0284 run0285
  have step0286 := compose step0285 run0286
  have step0287 := compose step0286 run0287
  have step0288 := compose step0287 run0288
  have step0289 := compose step0288 run0289
  have step0290 := compose step0289 run0290
  have step0291 := compose step0290 run0291
  have step0292 := compose step0291 run0292
  have step0293 := compose step0292 run0293
  have step0294 := compose step0293 run0294
  have step0295 := compose step0294 run0295
  have step0296 := compose step0295 run0296
  have step0297 := compose step0296 run0297
  have step0298 := compose step0297 run0298
  have step0299 := compose step0298 run0299
  have step0300 := compose step0299 run0300
  have step0301 := compose step0300 run0301
  have step0302 := compose step0301 run0302
  have step0303 := compose step0302 run0303
  have step0304 := compose step0303 run0304
  have step0305 := compose step0304 run0305
  have step0306 := compose step0305 run0306
  have step0307 := compose step0306 run0307
  have step0308 := compose step0307 run0308
  have step0309 := compose step0308 run0309
  have step0310 := compose step0309 run0310
  have step0311 := compose step0310 run0311
  have step0312 := compose step0311 run0312
  have step0313 := compose step0312 run0313
  have step0314 := compose step0313 run0314
  have step0315 := compose step0314 run0315
  have step0316 := compose step0315 run0316
  have step0317 := compose step0316 run0317
  have step0318 := compose step0317 run0318
  have step0319 := compose step0318 run0319
  have step0320 := compose step0319 run0320
  have step0321 := compose step0320 run0321
  have step0322 := compose step0321 run0322
  have step0323 := compose step0322 run0323
  have step0324 := compose step0323 run0324
  have step0325 := compose step0324 run0325
  have step0326 := compose step0325 run0326
  have step0327 := compose step0326 run0327
  have step0328 := compose step0327 run0328
  have step0329 := compose step0328 run0329
  have step0330 := compose step0329 run0330
  have step0331 := compose step0330 run0331
  have step0332 := compose step0331 run0332
  have step0333 := compose step0332 run0333
  have step0334 := compose step0333 run0334
  have step0335 := compose step0334 run0335
  have step0336 := compose step0335 run0336
  have step0337 := compose step0336 run0337
  have step0338 := compose step0337 run0338
  have step0339 := compose step0338 run0339
  have step0340 := compose step0339 run0340
  have step0341 := compose step0340 run0341
  have step0342 := compose step0341 run0342
  have step0343 := compose step0342 run0343
  have step0344 := compose step0343 run0344
  have step0345 := compose step0344 run0345
  have step0346 := compose step0345 run0346
  have step0347 := compose step0346 run0347
  have step0348 := compose step0347 run0348
  have step0349 := compose step0348 run0349
  have step0350 := compose step0349 run0350
  have step0351 := compose step0350 run0351
  have step0352 := compose step0351 run0352
  have step0353 := compose step0352 run0353
  have step0354 := compose step0353 run0354
  have step0355 := compose step0354 run0355
  have step0356 := compose step0355 run0356
  have step0357 := compose step0356 run0357
  have step0358 := compose step0357 run0358
  have step0359 := compose step0358 run0359
  have step0360 := compose step0359 run0360
  have step0361 := compose step0360 run0361
  have step0362 := compose step0361 run0362
  have step0363 := compose step0362 run0363
  have step0364 := compose step0363 run0364
  have step0365 := compose step0364 run0365
  have step0366 := compose step0365 run0366
  have step0367 := compose step0366 run0367
  have step0368 := compose step0367 run0368
  have step0369 := compose step0368 run0369
  have step0370 := compose step0369 run0370
  have step0371 := compose step0370 run0371
  have step0372 := compose step0371 run0372
  have step0373 := compose step0372 run0373
  have step0374 := compose step0373 run0374
  have step0375 := compose step0374 run0375
  have step0376 := compose step0375 run0376
  have step0377 := compose step0376 run0377
  have step0378 := compose step0377 run0378
  have step0379 := compose step0378 run0379
  have step0380 := compose step0379 run0380
  have step0381 := compose step0380 run0381
  have step0382 := compose step0381 run0382
  have step0383 := compose step0382 run0383
  have step0384 := compose step0383 run0384
  have step0385 := compose step0384 run0385
  have step0386 := compose step0385 run0386
  have step0387 := compose step0386 run0387
  have step0388 := compose step0387 run0388
  have step0389 := compose step0388 run0389
  have step0390 := compose step0389 run0390
  have step0391 := compose step0390 run0391
  have step0392 := compose step0391 run0392
  have step0393 := compose step0392 run0393
  have step0394 := compose step0393 run0394
  have step0395 := compose step0394 run0395
  have step0396 := compose step0395 run0396
  have step0397 := compose step0396 run0397
  have step0398 := compose step0397 run0398
  have step0399 := compose step0398 run0399
  have step0400 := compose step0399 run0400
  have step0401 := compose step0400 run0401
  have step0402 := compose step0401 run0402
  have step0403 := compose step0402 run0403
  have step0404 := compose step0403 run0404
  have step0405 := compose step0404 run0405
  have step0406 := compose step0405 run0406
  have step0407 := compose step0406 run0407
  have step0408 := compose step0407 run0408
  have step0409 := compose step0408 run0409
  have step0410 := compose step0409 run0410
  have step0411 := compose step0410 run0411
  have step0412 := compose step0411 run0412
  have step0413 := compose step0412 run0413
  have step0414 := compose step0413 run0414
  have step0415 := compose step0414 run0415
  have step0416 := compose step0415 run0416
  have step0417 := compose step0416 run0417
  have step0418 := compose step0417 run0418
  have step0419 := compose step0418 run0419
  have step0420 := compose step0419 run0420
  have step0421 := compose step0420 run0421
  have step0422 := compose step0421 run0422
  have step0423 := compose step0422 run0423
  have step0424 := compose step0423 run0424
  have step0425 := compose step0424 run0425
  have step0426 := compose step0425 run0426
  have step0427 := compose step0426 run0427
  have step0428 := compose step0427 run0428
  have step0429 := compose step0428 run0429
  have step0430 := compose step0429 run0430
  have step0431 := compose step0430 run0431
  have step0432 := compose step0431 run0432
  have step0433 := compose step0432 run0433
  have step0434 := compose step0433 run0434
  have step0435 := compose step0434 run0435
  have step0436 := compose step0435 run0436
  have step0437 := compose step0436 run0437
  have step0438 := compose step0437 run0438
  have step0439 := compose step0438 run0439
  have step0440 := compose step0439 run0440
  have step0441 := compose step0440 run0441
  have step0442 := compose step0441 run0442
  have step0443 := compose step0442 run0443
  have step0444 := compose step0443 run0444
  have step0445 := compose step0444 run0445
  have step0446 := compose step0445 run0446
  have step0447 := compose step0446 run0447
  have step0448 := compose step0447 run0448
  have step0449 := compose step0448 run0449
  have step0450 := compose step0449 run0450
  have step0451 := compose step0450 run0451
  have step0452 := compose step0451 run0452
  have step0453 := compose step0452 run0453
  have step0454 := compose step0453 run0454
  simpa only [first_eq,last_eq] using step0454

theorem startup_reach : Reach Literal.machine blank clean := ⟨58154,startup_exact⟩

#print axioms startup_exact
end PA196.Startup

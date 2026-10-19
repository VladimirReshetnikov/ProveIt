#! start 0.boot.A
# Based on the NQL register machine:
# <https://github.com/sorear/metamath-turing-machines>
#
# States that begin with a digit are the states for the framework of the
# register machine implemented in a turing machine. States that don't begin
# with a digit are the decision tree states from the subroutines and main().
#
# 0. boot
#
0.boot.A 0 1 R 0.boot.B
0.boot.A 1 0 L 0.boot.C
0.boot.B 0 0 R 0.boot.C
0.boot.B 1 0 R 0.boot.B
0.boot.C 0 1 L 0.boot.D
0.boot.C 1 0 R 0.boot.E
0.boot.D 0 0 L 0.boot.E
0.boot.D 1 0 L 6.continue.4
0.boot.E 0 1 L 0.boot.A
0.boot.E 1 0 L 0.boot.B
#
# At the end of boot the tape looks like:
# 100 1000^4 <3.continue.4 01^132 011 01^68
#
# 1. 2. Low-level register operations:
#
# SEL - Shift which register is selected:
#
# 1 [IP] 1.sel> [ZEROS] [REG BLOCK 1] 0 [REG] 00 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 3 0s,
#       REG BLOCK 1 starts and ends with 1s and has no run of more than one 0,
#       REG BLOCK 2 can have registers or can be empty.
#
# If 00 does not appear in the register file it is conceptually after the last register.
#
# 00 selects the register that appears after it.
#
# INC - Increment selected register.
#
# 1 [IP] 1.inc> [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] [REG BLOCK 1] 0 [inc(REG)] 0 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 3 0s,
#       REG BLOCK 1 starts and ends with 1s and has no run of more than one 0,
#       REG BLOCK 2 can have registers or can be empty.
#
# DECNZ - Decrement selected register if not zero.
#          Break an extra layer if it was 0.
#
# 1 [IP] 1.decnz> [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] 0 [REG BLOCK 1] 0 [dec(REG)] 0 [REG BLOCK 2] 0
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 2 0s,
#       REG BLOCK 1 starts and ends with 1s and has no runs of more than one 0,
#       REG         is a run of at least two 1s,
#       REG BLOCK 2 is either empty or starts and ends with 1s and has no run of
#                   more than one 0.
#
# or
#
# 1 [IP] 1.decnz> [ZEROS] [REG BLOCK 1] 0010 [REG BLOCK 2]
# ->
# 5.root> 1 [break.1(IP)] [ZEROS] 0 [REG BLOCK 1] 010 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 2 0s,
#       REG BLOCK 1 starts and ends with 1s and has no runs of more than one 0,
#       REG BLOCK 2 is either empty or starts and ends with 1s and has no run of
#                   more than one 0.
#
# Both variants of DECNZ shift [REG BLOCK 1] over to the right one cell,
# thus providing more room for the IP. This is useful as the
# bootstrap does not leave enough room for the longest IP used by the larger
# machines.
#
# For all register operations, when going out to the regiser file a 1 is
# written to the tape after the IP so the end of the IP can be identified
# when returning back from the register file.
#
# DECNZ is implemented by:
#
# 1 [IP] 1.decnz> 0 [>0 0s] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# 1 [IP] 1 [>0 0s] 0 [updated REGS] 0 <1.ret1
# 5.root> 1 [break.0(IP)] 0 [>0 0s] 0 [updated REGS]
#
# or
#
# 1 [IP] 1.decnz> 0 [>0 0s] [REG BLOCK 1] 0 010 [REG BLOCK 2]
# 1 [IP] 1 [>0 0s] 0 [REG BLOCK 1] 0 <1.ret2 10 [REG BLOCK 2]
# 5.root> 1 [break.2(IP)] 0 [>0 0s] 0 [REG BLOCK 1] 010 [REG BLOCK 2]
#
# 1 [IP] 1.decnz> 0 [>0 0s]
# 1 [IP] 1 1.decnz.b> [>0 0s]
1.decnz 0 1 R 1.decnz.b
# with a 1 on the tape 1.decnz is actually 1.decnz.f
# used to skip past the last set 1 on a reg to
# check if it can be decremented
1.decnz 1 1 L 1.decnz.g
# 1 [IP] 1 1.decnz.b> [>0 0s] 1 [REST OF FIRST REG]
# 1 [IP] 1 [>0 0s] 0 1.decnz.c> [REST OF FIRST REG]
1.decnz.b 0 0 R 1.decnz.b
1.decnz.b 1 0 R 1.decnz.c
# 1.decnz.d> [REG] 0
# 0 [REG] decnz.d>
#
# but once we reach the 00 selector we transition into decrement:
#
# 1.decnz.d> 0
# 0 decnz.e>
1.decnz.c 0 1 R 1.decnz.d
1.decnz.c 1 1 R 1.decnz.c
1.decnz.d 0 0 R 1.decnz.e
1.decnz.d 1 0 R 1.decnz.c
1.decnz.e 0 0 L 1.decnz
# Find end of register to decrement:
# decnz.e> [1s] 1 0
# [1s] 1 <1.decnz 0
# [1s] <1.decnz.g 1 0
1.decnz.e 1 1 R 1.decnz.e
# If decnz.g does not find more of the register we cannot decrement:
# Use the alternate return, otherwise move to the right to prepare
# to overwrite the last digit.
1.decnz.g 0 0 L 2.ret2
1.decnz.g 1 1 R 1.decnz.h
# Increment the next register
# (We shift the registers by incrementing to the left then degrementing
# on the right)
1.decnz.h 0 1 R 1.decnz.i
# Decrement the last register:
1.decnz.h 1 0 R 1.decnz.h
# check if we've reached the end of the register file:
# If so we'll use 1.sel to remove the register we just added.
# Otherwise we will transition into decrementing the current register
# (Which will restore it to it's old value shifted one cell to the left.)
1.decnz.i 0 0 L 1.sel
1.decnz.i 1 1 R 1.decnz.e
#
1.inc 0 1 R 1.inc.b
1.inc.b 0 0 R 1.inc.b
1.inc.b 1 1 R 1.inc.c
1.inc.c 0 0 R 1.inc.d
1.inc.c 1 1 R 1.inc.c
1.inc.d 0 1 L 2.ret1
1.inc.d 1 1 R 1.inc.c
#
1.sel 0 1 R 1.sel.b
# with a 1 on the tape 1.sel is actually 1.decnz.j
# used to clear the extra register added after the RF
1.sel 1 0 L 2.ret1
1.sel.b 0 0 R 1.sel.b
1.sel.b 1 1 R 1.sel.c
1.sel.c 0 0 R 1.sel.d
1.sel.c 1 1 R 1.sel.c
1.sel.d 0 0 L 1.sel.e
1.sel.d 1 1 R 1.sel.c
1.sel.e 0 1 L 1.sel.f
1.sel.e 1 0 L 2.ret1
1.sel.f 0 0 R 1.sel.e
1.sel.f 1 1 L 1.sel.f
#
2.ret1 0 0 L 2.ret1.1
2.ret1 1 1 L 2.ret1
2.ret1.1 0 0 L 2.ret1.2
2.ret1.1 1 1 L 2.ret1
# search for the marker after IP
2.ret1.2 0 0 L 2.ret1.2
2.ret1.2 1 0 L 6.break.0
#
2.ret2 0 0 L 2.ret2.1
2.ret2 1 1 L 2.ret2
2.ret2.1 0 0 L 2.ret2.2
2.ret2.1 1 1 L 2.ret2
# search for the marker after IP
2.ret2.2 0 0 L 2.ret2.2
2.ret2.2 1 0 L 6.break.1
3.axiomcode.decnz 0 0 R 1.sel
3.axiomcode.decnz 1 1 R 3.wffstack.decnz
3.axiomcode.inc 0 0 R 1.sel
3.axiomcode.inc 1 1 R 3.wffstack.inc
3.nextproof.decnz 0 0 R 1.sel
3.nextproof.decnz 1 1 R 1.decnz
3.nextproof.inc 0 0 R 1.sel
3.nextproof.inc 1 1 R 1.inc
3.param1.decnz 0 0 R 1.sel
3.param1.decnz 1 1 R 3.axiomcode.decnz
3.param1.inc 0 0 R 1.sel
3.param1.inc 1 1 R 3.axiomcode.inc
3.param2.decnz 0 0 R 1.sel
3.param2.decnz 1 1 R 3.param1.decnz
3.param2.inc 0 0 R 1.sel
3.param2.inc 1 1 R 3.param1.inc
3.prooflist.decnz 0 0 R 1.sel
3.prooflist.decnz 1 1 R 3.scratch2.decnz
3.prooflist.inc 0 0 R 1.sel
3.prooflist.inc 1 1 R 3.scratch2.inc
3.scratch1.decnz 0 0 R 1.sel
3.scratch1.decnz 1 1 R 3.param2.decnz
3.scratch1.inc 0 0 R 1.sel
3.scratch1.inc 1 1 R 3.param2.inc
3.scratch2.decnz 0 0 R 1.sel
3.scratch2.decnz 1 1 R 3.scratch1.decnz
3.scratch2.inc 0 0 R 1.sel
3.scratch2.inc 1 1 R 3.scratch1.inc
3.topwff.decnz 0 0 R 1.sel
3.topwff.decnz 1 1 R 3.nextproof.decnz
3.topwff.inc 0 0 R 1.sel
3.topwff.inc 1 1 R 3.nextproof.inc
3.wffstack.decnz 0 0 R 1.sel
3.wffstack.decnz 1 1 R 3.topwff.decnz
3.wffstack.inc 0 0 R 1.sel
3.wffstack.inc 1 1 R 3.topwff.inc
#
# 4. dispatch
#
# Find the start of the IP. We pass by a set number of 0 cells going
# left (how many depends on the decision tree), then scan right for the
# first 1 cell.
#
4.dispatch.1 0 0 L 4.dispatch.2
4.dispatch.1 1 1 L 6.continue.0
4.dispatch.2 0 0 L 4.dispatch.3
4.dispatch.2 1 1 L 6.continue.0
4.dispatch.3 0 0 L 4.dispatch.4
4.dispatch.3 1 1 L 6.continue.0
4.dispatch.4 0 0 L 4.dispatch.5
4.dispatch.4 1 1 L 6.continue.0
4.dispatch.5 0 0 L 4.dispatch.6
4.dispatch.5 1 1 L 6.continue.0
4.dispatch.6 0 0 L 4.dispatch.7
4.dispatch.6 1 1 L 6.continue.0
4.dispatch.7 0 0 R 5.root
4.dispatch.7 1 1 L 6.continue.0
#
# 5. root - find the root of the IP
#
# There is no special handling to call main() in a loop. At the end
# of main() the IP simply overflows past the marker to the left of the
# IP and creates a new marker with the IP all zeros.
#
5.root 0 0 R 5.root
5.root 1 1 R main().0
#
# 6. IP jump instructions.
#
6.break.0 0 1 L 6.continue.0
6.break.0 1 0 L 6.break.0
6.break.1 0 0 L 6.break.0
6.break.1 1 0 L 6.break.1
6.continue.0 0 0 L 4.dispatch.1
6.continue.0 1 1 L 6.continue.0
6.continue.1 0 0 L 6.continue.1
6.continue.1 1 0 L 6.continue.0
6.continue.2 0 0 L 6.continue.2
6.continue.2 1 0 L 6.continue.1
6.continue.3 0 0 L 6.continue.3
6.continue.3 1 0 L 6.continue.2
6.continue.4 0 0 L 6.continue.4
6.continue.4 1 0 L 6.continue.3
fixed_axiom_219 0 0 R par3().0
fixed_axiom_219 1 1 R fn_59().0
fixed_axiom_220 0 0 R par1().0
fixed_axiom_220 1 1 R fn_59().0
fixed_axiom_221 0 0 R wex().0
fixed_axiom_221 1 1 R wa().0
fixed_axiom_222 0 0 R fixed_axiom_220
fixed_axiom_222 1 1 R weq().0
fixed_axiom_223 0 0 R fn_45().0
fixed_axiom_223 1 1 R fn_45().0
fixed_axiom_224 0 0 R fn_45().0
fixed_axiom_224 1 1 R wal().0
fixed_axiom_225 0 0 R fixed_axiom_219
fixed_axiom_225 1 1 R wel().0
fixed_axiom_226 0 0 R par3().0
fixed_axiom_226 1 1 R par1().0
fixed_axiom_227 0 0 R v_1().0
fixed_axiom_227 1 1 R par3().0
fixed_axiom_228 0 0 R fn_59().0
fixed_axiom_228 1 1 R par3().0
fixed_axiom_229 0 0 R wa().0
fixed_axiom_229 1 1 R fixed_axiom_221
fixed_axiom_230 0 0 R fixed_axiom_220
fixed_axiom_230 1 1 R wel().0
fixed_axiom_231 0 0 R fixed_axiom_220
fixed_axiom_231 1 1 R wal().0
fixed_axiom_232 0 0 R fixed_axiom_227
fixed_axiom_232 1 1 R 3.topwff.inc
fixed_axiom_233 0 0 R wal().0
fixed_axiom_233 1 1 R fn_45().0
fixed_axiom_234 0 0 R par1().0
fixed_axiom_234 1 1 R par3().0
fixed_axiom_235 0 0 R fixed_axiom_224
fixed_axiom_235 1 1 R fixed_axiom_225
fixed_axiom_236 0 0 R fixed_axiom_230
fixed_axiom_236 1 1 R par3().0
fixed_axiom_237 0 0 R fixed_axiom_226
fixed_axiom_237 1 1 R wel().0
fixed_axiom_238 0 0 R fixed_axiom_237
fixed_axiom_238 1 1 R fixed_axiom_225
fixed_axiom_239 0 0 R wex().0
fixed_axiom_239 1 1 R fixed_axiom_224
fixed_axiom_240 0 0 R fn_45().0
fixed_axiom_240 1 1 R fixed_axiom_226
fixed_axiom_241 0 0 R fixed_axiom_232
fixed_axiom_241 1 1 R wel().0
fixed_axiom_242 0 0 R fixed_axiom_234
fixed_axiom_242 1 1 R wal().0
fixed_axiom_243 0 0 R fixed_axiom_223
fixed_axiom_243 1 1 R par1().0
fixed_axiom_244 0 0 R fixed_axiom_233
fixed_axiom_244 1 1 R fixed_axiom_222
fixed_axiom_245 0 0 R fixed_axiom_223
fixed_axiom_245 1 1 R fixed_axiom_220
fixed_axiom_246 0 0 R fixed_axiom_245
fixed_axiom_246 1 1 R par3().0
fixed_axiom_247 0 0 R fixed_axiom_235
fixed_axiom_247 1 1 R fixed_axiom_229
fixed_axiom_248 0 0 R fixed_axiom_240
fixed_axiom_248 1 1 R weq().0
fixed_axiom_249 0 0 R while_decnz(param1,3.param2.inc).0
fixed_axiom_249 1 1 R if_eq(scratch1,param2,77).0
fixed_axiom_250 0 0 R while_decnz(scratch2,3.scratch1.inc).0
fixed_axiom_250 1 1 R fixed_axiom_249
fixed_axiom_251 0 0 R if_eq(scratch1,param2,77).0
fixed_axiom_251 1 1 R fixed_axiom_250
fixed_axiom_252 0 0 R while_decnz(axiomcode,26).0
fixed_axiom_252 1 1 R fixed_axiom_251
fixed_axiom_253 0 0 R wa().0
fixed_axiom_253 1 1 R fixed_axiom_252
fixed_axiom_254 0 0 R fixed_axiom_229
fixed_axiom_254 1 1 R fixed_axiom_253
fixed_axiom_255 0 0 R fixed_axiom_224
fixed_axiom_255 1 1 R fixed_axiom_254
fixed_axiom_256 0 0 R fixed_axiom_239
fixed_axiom_256 1 1 R fixed_axiom_255
fixed_axiom_257 0 0 R wa().0
fixed_axiom_257 1 1 R fixed_axiom_256
fixed_axiom_258 0 0 R fixed_axiom_241
fixed_axiom_258 1 1 R fixed_axiom_257
fixed_axiom_259 0 0 R fixed_axiom_227
fixed_axiom_259 1 1 R fixed_axiom_258
fixed_axiom_260 0 0 R fixed_axiom_227
fixed_axiom_260 1 1 R fixed_axiom_259
fixed_axiom_261 0 0 R wel().0
fixed_axiom_261 1 1 R fixed_axiom_260
fixed_axiom_262 0 0 R v_1().0
fixed_axiom_262 1 1 R fixed_axiom_261
fixed_axiom_263 0 0 R pushwff().0
fixed_axiom_263 1 1 R fixed_axiom_262
fixed_axiom_264 0 0 R pushwff().0
fixed_axiom_264 1 1 R fixed_axiom_263
fixed_axiom_265 0 0 R fixed_axiom_239
fixed_axiom_265 1 1 R fixed_axiom_264
fixed_axiom_266 0 0 R par3().0
fixed_axiom_266 1 1 R fixed_axiom_265
fixed_axiom_267 0 0 R pushwff().0
fixed_axiom_267 1 1 R fixed_axiom_266
fixed_axiom_268 0 0 R fixed_axiom_241
fixed_axiom_268 1 1 R fixed_axiom_267
fixed_axiom_269 0 0 R v_1().0
fixed_axiom_269 1 1 R fixed_axiom_268
fixed_axiom_270 0 0 R 3.topwff.inc
fixed_axiom_270 1 1 R fixed_axiom_269
fixed_axiom_271 0 0 R par3().0
fixed_axiom_271 1 1 R fixed_axiom_270
fixed_axiom_272 0 0 R fixed_axiom_247
fixed_axiom_272 1 1 R fixed_axiom_271
fixed_axiom_273 0 0 R fixed_axiom_247
fixed_axiom_273 1 1 R fixed_axiom_272
fixed_axiom_274 0 0 R wel().0
fixed_axiom_274 1 1 R fixed_axiom_273
fixed_axiom_275 0 0 R fixed_axiom_228
fixed_axiom_275 1 1 R fixed_axiom_274
fixed_axiom_276 0 0 R fixed_axiom_224
fixed_axiom_276 1 1 R fixed_axiom_275
fixed_axiom_277 0 0 R fixed_axiom_237
fixed_axiom_277 1 1 R fixed_axiom_276
fixed_axiom_278 0 0 R fixed_axiom_225
fixed_axiom_278 1 1 R fixed_axiom_277
fixed_axiom_279 0 0 R par3().0
fixed_axiom_279 1 1 R fixed_axiom_278
fixed_axiom_280 0 0 R fixed_axiom_219
fixed_axiom_280 1 1 R fixed_axiom_279
fixed_axiom_281 0 0 R fixed_axiom_224
fixed_axiom_281 1 1 R fixed_axiom_280
fixed_axiom_282 0 0 R fixed_axiom_238
fixed_axiom_282 1 1 R fixed_axiom_281
fixed_axiom_283 0 0 R fixed_axiom_236
fixed_axiom_283 1 1 R fixed_axiom_282
fixed_axiom_284 0 0 R par1().0
fixed_axiom_284 1 1 R fixed_axiom_283
fixed_axiom_285 0 0 R fn_59().0
fixed_axiom_285 1 1 R fixed_axiom_284
fixed_axiom_286 0 0 R fixed_axiom_233
fixed_axiom_286 1 1 R fixed_axiom_285
fixed_axiom_287 0 0 R fixed_axiom_222
fixed_axiom_287 1 1 R fixed_axiom_286
fixed_axiom_288 0 0 R par3().0
fixed_axiom_288 1 1 R fixed_axiom_287
fixed_axiom_289 0 0 R fixed_axiom_244
fixed_axiom_289 1 1 R fixed_axiom_288
fixed_axiom_290 0 0 R fixed_axiom_230
fixed_axiom_290 1 1 R fixed_axiom_289
fixed_axiom_291 0 0 R fixed_axiom_236
fixed_axiom_291 1 1 R fixed_axiom_290
fixed_axiom_292 0 0 R wex().0
fixed_axiom_292 1 1 R fixed_axiom_291
fixed_axiom_293 0 0 R fixed_axiom_222
fixed_axiom_293 1 1 R fixed_axiom_292
fixed_axiom_294 0 0 R fixed_axiom_243
fixed_axiom_294 1 1 R fixed_axiom_293
fixed_axiom_295 0 0 R fixed_axiom_242
fixed_axiom_295 1 1 R fixed_axiom_294
fixed_axiom_296 0 0 R fixed_axiom_231
fixed_axiom_296 1 1 R fixed_axiom_295
fixed_axiom_297 0 0 R fixed_axiom_224
fixed_axiom_297 1 1 R fixed_axiom_296
fixed_axiom_298 0 0 R fixed_axiom_246
fixed_axiom_298 1 1 R fixed_axiom_297
fixed_axiom_299 0 0 R fixed_axiom_238
fixed_axiom_299 1 1 R fixed_axiom_298
fixed_axiom_300 0 0 R fixed_axiom_244
fixed_axiom_300 1 1 R fixed_axiom_299
fixed_axiom_301 0 0 R fixed_axiom_242
fixed_axiom_301 1 1 R fixed_axiom_300
fixed_axiom_302 0 0 R fn_59().0
fixed_axiom_302 1 1 R fixed_axiom_301
fixed_axiom_303 0 0 R wal().0
fixed_axiom_303 1 1 R fixed_axiom_302
fixed_axiom_304 0 0 R wal().0
fixed_axiom_304 1 1 R fixed_axiom_303
fixed_axiom_305 0 0 R fixed_axiom_246
fixed_axiom_305 1 1 R fixed_axiom_304
fixed_axiom_306 0 0 R fixed_axiom_230
fixed_axiom_306 1 1 R fixed_axiom_305
fixed_axiom_307 0 0 R fixed_axiom_225
fixed_axiom_307 1 1 R fixed_axiom_306
fixed_axiom_308 0 0 R fixed_axiom_248
fixed_axiom_308 1 1 R fixed_axiom_307
fixed_axiom_309 0 0 R fn_59().0
fixed_axiom_309 1 1 R fixed_axiom_308
fixed_axiom_310 0 0 R wex().0
fixed_axiom_310 1 1 R fixed_axiom_309
fixed_axiom_311 0 0 R fixed_axiom_231
fixed_axiom_311 1 1 R fixed_axiom_310
fixed_axiom_312 0 0 R fixed_axiom_243
fixed_axiom_312 1 1 R fixed_axiom_311
fixed_axiom_313 0 0 R fixed_axiom_222
fixed_axiom_313 1 1 R fixed_axiom_312
fixed_axiom_314 0 0 R weq().0
fixed_axiom_314 1 1 R fixed_axiom_313
fixed_axiom_315 0 0 R fixed_axiom_219
fixed_axiom_315 1 1 R fixed_axiom_314
fixed_axiom_316 0 0 R fixed_axiom_248
fixed_axiom_316 1 1 R fixed_axiom_315
fixed_axiom_317 0 0 R fixed_axiom_223
fixed_axiom_317 1 1 R fixed_axiom_316
fixed_axiom_318 0 0 R fixed_axiom_228
fixed_axiom_318 1 1 R fixed_axiom_317
fixed_axiom_319 0 0 R fn_45().0
fixed_axiom_319 1 1 R fixed_axiom_318
fixed_axiom_320 0 0 R fixed_axiom_234
fixed_axiom_320 1 1 R fixed_axiom_319
fixed_axiom_321 0 0 R node_111.0
fixed_axiom_321 1 1 R fixed_axiom_320
fixed_axiom_322 0 0 R fn_45().0
fixed_axiom_322 1 1 R fixed_axiom_321
fixed_axiom_323 0 0 R while_decnz(scratch1,3.topwff.inc).0
fixed_axiom_323 1 1 R fixed_axiom_322
fixed_axiom_324 0 0 R node_108.0
fixed_axiom_324 1 1 R fixed_axiom_323
fixed_axiom_325 0 0 R pushwff().0
fixed_axiom_325 1 1 R fixed_axiom_324
fixed_axiom_326 0 0 R par3().0
fixed_axiom_326 1 1 R fixed_axiom_325
fixed_axiom_327 0 0 R read(param2).0
fixed_axiom_327 1 1 R fixed_axiom_326
fixed_axiom_328 0 0 R fixed_axiom_231
fixed_axiom_328 1 1 R fixed_axiom_327
fn_14().0 0 0 R 3.prooflist.decnz
fn_14().0 1 1 R node_013.0
fn_41().0 0 0 R 3.wffstack.decnz
fn_41().0 1 1 R node_013.0
fn_44().0 0 0 R 3.scratch2.decnz
fn_44().0 1 1 R fn_44().1
fn_44().1 0 0 R node_042.0
fn_44().1 1 0 L 6.continue.1
fn_45().0 0 0 R node_110.0
fn_45().0 1 1 R fn_45().1
fn_45().1 0 0 R pair(scratch2,scratch1,topwff).0
fn_45().1 1 1 R fn_44().0
fn_59().0 0 0 R pushwff().0
fn_59().0 1 1 R fn_59().1
fn_59().1 0 0 R while_decnz(param2,37).0
fn_59().1 1 1 R while_decnz(scratch1,3.param2.inc).0
if_eq().n_055.0 0 0 R if_eq().n_055.0.0
if_eq().n_055.0 1 1 R if_eq().n_055.1
if_eq().n_055.0.0 0 0 R 3.scratch1.decnz
if_eq().n_055.0.0 1 1 R if_eq().n_055.0.1
if_eq().n_055.0.1 0 0 R if_eq().n_055.0.1.0
if_eq().n_055.0.1 1 1 R if_eq().n_055.0.2
if_eq().n_055.0.1.0 0 0 R 3.param2.decnz
if_eq().n_055.0.1.0 1 0 L 6.continue.1
if_eq().n_055.0.2 0 0 R while_decnz(scratch1,3.param2.inc).0
if_eq().n_055.0.2 1 1 R 3.param2.inc
if_eq().n_055.1 0 0 R 3.param2.decnz
if_eq().n_055.1 1 1 R if_eq().n_055.2
if_eq().n_055.2 0 0 R while_decnz(param2,()).0
if_eq().n_055.2 1 0 L 6.break.1
if_eq(scratch1,param2,40).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,40).0 1 1 R par1().0
if_eq(scratch1,param2,77).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,77).0 1 1 R while_decnz(topwff,()).0
if_eq(scratch1,param2,halt).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,halt).0 1 1 R halt
if_not_decnz(prooflist,5).0 0 0 R if_not_decnz(prooflist,5).0.0
if_not_decnz(prooflist,5).0 1 1 R if_not_decnz(prooflist,5).1
if_not_decnz(prooflist,5).0.0 0 0 R 3.prooflist.decnz
if_not_decnz(prooflist,5).0.0 1 0 L 6.break.1
if_not_decnz(prooflist,5).1 0 0 R while_decnz(nextproof,0).0
if_not_decnz(prooflist,5).1 1 1 R if_not_decnz(prooflist,5).2
if_not_decnz(prooflist,5).2 0 0 R while_decnz(scratch1,3.nextproof.inc).0
if_not_decnz(prooflist,5).2 1 1 R 3.nextproof.inc
if_not_decnz(scratch1,9).0 0 0 R if_not_decnz(scratch1,9).0.0
if_not_decnz(scratch1,9).0 1 1 R while_decnz(scratch2,3.scratch1.inc).0
if_not_decnz(scratch1,9).0.0 0 0 R 3.scratch1.decnz
if_not_decnz(scratch1,9).0.0 1 0 L 6.break.1
main().0 0 0 R if_not_decnz(prooflist,5).0
main().0 1 1 R main().1
main().1 0 0 R read(axiomcode).0
main().1 1 1 R main().2
main().2 0 0 R read(param1).0
main().2 1 1 R main().3
main().3 0 0 R main().3.0
main().3 1 1 R mp().0
main().3.0 0 0 R 3.axiomcode.decnz
main().3.0 1 1 R main().3.1
main().3.1 0 0 R main().3.1.0
main().3.1 1 0 L 6.break.1
main().3.1.0 0 0 R main().3.1.0.0
main().3.1.0 1 1 R fn_59().0
main().3.1.0.0 0 0 R 3.axiomcode.decnz
main().3.1.0.0 1 1 R main().3.1.0.1
main().3.1.0.1 0 0 R main().3.1.0.1.0
main().3.1.0.1 1 0 L 6.break.1
main().3.1.0.1.0 0 0 R main().3.1.0.1.0.0
main().3.1.0.1.0 1 1 R nip().0
main().3.1.0.1.0.0 0 0 R 3.axiomcode.decnz
main().3.1.0.1.0.0 1 1 R main().3.1.0.1.0.1
main().3.1.0.1.0.1 0 0 R fixed_axiom_328
main().3.1.0.1.0.1 1 0 L 6.break.1
mp().0 0 0 R node_111.0
mp().0 1 1 R mp().1
mp().1 0 0 R while_decnz(topwff,3.scratch1.inc).0
mp().1 1 1 R if_eq(scratch1,param2,40).0
nip().0 0 0 R 3.scratch1.inc
nip().0 1 1 R nip().1
nip().1 0 0 R if_eq(scratch1,param2,halt).0
nip().1 1 1 R pop(param2).0
node_013.0 0 0 R node_013.0.0
node_013.0 1 0 L 6.continue.1
node_013.0.0 0 0 R 3.scratch2.inc
node_013.0.0 1 1 R if_not_decnz(scratch1,9).0
node_042.0 0 0 R node_099.0
node_042.0 1 1 R 3.topwff.inc
node_099.0 0 0 R node_109.0
node_099.0 1 1 R 3.topwff.inc
node_108.0 0 0 R fn_14().0
node_108.0 1 1 R while_decnz(scratch2,3.prooflist.inc).0
node_109.0 0 0 R 3.topwff.inc
node_109.0 1 1 R 3.topwff.inc
node_110.0 0 0 R fn_41().0
node_110.0 1 1 R while_decnz(scratch2,3.wffstack.inc).0
node_111.0 0 0 R par1().0
node_111.0 1 1 R fn_45().0
pair(scratch2,scratch1,topwff).0 0 0 R while_decnz(topwff,26).0
pair(scratch2,scratch1,topwff).0 1 1 R pair(scratch2,scratch1,topwff).1
pair(scratch2,scratch1,topwff).1 0 0 R 3.scratch1.decnz
pair(scratch2,scratch1,topwff).1 1 1 R pair(scratch2,scratch1,topwff).2
pair(scratch2,scratch1,topwff).2 0 0 R pair(scratch2,scratch1,topwff).2.0
pair(scratch2,scratch1,topwff).2 1 0 L 6.continue.2
pair(scratch2,scratch1,topwff).2.0 0 0 R 3.scratch2.inc
pair(scratch2,scratch1,topwff).2.0 1 1 R while_decnz(scratch1,3.topwff.inc).0
par1().0 0 0 R pushwff().0
par1().0 1 1 R par1().1
par1().1 0 0 R while_decnz(param1,37).0
par1().1 1 1 R while_decnz(scratch1,3.param1.inc).0
par3().0 0 0 R pushwff().0
par3().0 1 1 R par3().1
par3().1 0 0 R while_decnz(axiomcode,37).0
par3().1 1 1 R while_decnz(scratch1,3.axiomcode.inc).0
pop(param2).0 0 0 R node_110.0
pop(param2).0 1 1 R while_decnz(scratch1,3.param2.inc).0
pushwff().0 0 0 R while_decnz(topwff,3.scratch1.inc).0
pushwff().0 1 1 R pushwff().1
pushwff().1 0 0 R while_decnz(wffstack,3.topwff.inc).0
pushwff().1 1 1 R pushwff().2
pushwff().2 0 0 R pair(scratch2,scratch1,topwff).0
pushwff().2 1 1 R while_decnz(scratch2,3.wffstack.inc).0
read(axiomcode).0 0 0 R node_108.0
read(axiomcode).0 1 1 R while_decnz(scratch1,3.axiomcode.inc).0
read(param1).0 0 0 R node_108.0
read(param1).0 1 1 R while_decnz(scratch1,3.param1.inc).0
read(param2).0 0 0 R node_108.0
read(param2).0 1 1 R while_decnz(scratch1,3.param2.inc).0
v_1().0 0 0 R pushwff().0
v_1().0 1 1 R 3.topwff.inc
wa().0 0 0 R wn().0
wa().0 1 1 R wa().1
wa().1 0 0 R fn_45().0
wa().1 1 1 R wn().0
wal().0 0 0 R fn_45().0
wal().0 1 1 R node_109.0
wel().0 0 0 R fn_45().0
wel().0 1 1 R 3.topwff.inc
weq().0 0 0 R fn_45().0
weq().0 1 1 R node_099.0
wex().0 0 0 R wn().0
wex().0 1 1 R wex().1
wex().1 0 0 R wal().0
wex().1 1 1 R wn().0
while_decnz().n_008.0 0 0 R 3.scratch1.inc
while_decnz().n_008.0 1 0 L 6.continue.1
while_decnz().n_024.0 0 0 R 3.topwff.inc
while_decnz().n_024.0 1 0 L 6.continue.1
while_decnz().n_027.0 0 0 R while_decnz().n_027.0.0
while_decnz().n_027.0 1 0 L 6.continue.1
while_decnz().n_027.0.0 0 0 R 3.scratch1.inc
while_decnz().n_027.0.0 1 1 R 3.scratch2.inc
while_decnz().n_038.0 0 0 R while_decnz().n_038.0.0
while_decnz().n_038.0 1 0 L 6.continue.1
while_decnz().n_038.0.0 0 0 R 3.scratch1.inc
while_decnz().n_038.0.0 1 1 R 3.topwff.inc
while_decnz().n_046.0 0 0 R 3.param2.inc
while_decnz().n_046.0 1 0 L 6.continue.1
while_decnz(axiomcode,26).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,26).0 1 1 R while_decnz().n_027.0
while_decnz(axiomcode,37).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,37).0 1 1 R while_decnz().n_038.0
while_decnz(nextproof,0).0 0 0 R 3.nextproof.decnz
while_decnz(nextproof,0).0 1 1 R while_decnz(nextproof,0).1
while_decnz(nextproof,0).1 0 0 R while_decnz(nextproof,0).1.0
while_decnz(nextproof,0).1 1 0 L 6.continue.1
while_decnz(nextproof,0).1.0 0 0 R 3.prooflist.inc
while_decnz(nextproof,0).1.0 1 1 R 3.scratch1.inc
while_decnz(param1,3.param2.inc).0 0 0 R 3.param1.decnz
while_decnz(param1,3.param2.inc).0 1 1 R while_decnz().n_046.0
while_decnz(param1,37).0 0 0 R 3.param1.decnz
while_decnz(param1,37).0 1 1 R while_decnz().n_038.0
while_decnz(param2,()).0 0 0 R 3.param2.decnz
while_decnz(param2,()).0 1 0 L 6.continue.0
while_decnz(param2,37).0 0 0 R 3.param2.decnz
while_decnz(param2,37).0 1 1 R while_decnz().n_038.0
while_decnz(scratch1,3.axiomcode.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.axiomcode.inc).0 1 1 R while_decnz(scratch1,3.axiomcode.inc).1
while_decnz(scratch1,3.axiomcode.inc).1 0 0 R 3.axiomcode.inc
while_decnz(scratch1,3.axiomcode.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.nextproof.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.nextproof.inc).0 1 1 R while_decnz(scratch1,3.nextproof.inc).1
while_decnz(scratch1,3.nextproof.inc).1 0 0 R 3.nextproof.inc
while_decnz(scratch1,3.nextproof.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.param1.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.param1.inc).0 1 1 R while_decnz(scratch1,3.param1.inc).1
while_decnz(scratch1,3.param1.inc).1 0 0 R 3.param1.inc
while_decnz(scratch1,3.param1.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.param2.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.param2.inc).0 1 1 R while_decnz().n_046.0
while_decnz(scratch1,3.topwff.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.topwff.inc).0 1 1 R while_decnz().n_024.0
while_decnz(scratch2,3.prooflist.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.prooflist.inc).0 1 1 R while_decnz(scratch2,3.prooflist.inc).1
while_decnz(scratch2,3.prooflist.inc).1 0 0 R 3.prooflist.inc
while_decnz(scratch2,3.prooflist.inc).1 1 0 L 6.continue.1
while_decnz(scratch2,3.scratch1.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(scratch2,3.wffstack.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.wffstack.inc).0 1 1 R while_decnz(scratch2,3.wffstack.inc).1
while_decnz(scratch2,3.wffstack.inc).1 0 0 R 3.wffstack.inc
while_decnz(scratch2,3.wffstack.inc).1 1 0 L 6.continue.1
while_decnz(topwff,()).0 0 0 R 3.topwff.decnz
while_decnz(topwff,()).0 1 0 L 6.continue.0
while_decnz(topwff,26).0 0 0 R 3.topwff.decnz
while_decnz(topwff,26).0 1 1 R while_decnz().n_027.0
while_decnz(topwff,3.scratch1.inc).0 0 0 R 3.topwff.decnz
while_decnz(topwff,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(wffstack,3.topwff.inc).0 0 0 R 3.wffstack.decnz
while_decnz(wffstack,3.topwff.inc).0 1 1 R while_decnz().n_024.0
wn().0 0 0 R v_1().0
wn().0 1 1 R fn_45().0

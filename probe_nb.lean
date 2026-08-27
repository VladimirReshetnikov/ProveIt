import Mathlib

open MeasureTheory Set Filter Complex

#check @tendstoUniformlyOn_tsum_nat
#check @TendstoLocallyUniformlyOn.differentiableOn
#check @tendstoLocallyUniformlyOn_iff_forall_isCompact
#check @Summable.tsum_even_add_odd
#check @AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
#check @DifferentiableOn.analyticOnNhd
#check @Complex.norm_eq_abs
#check @Complex.abs_mul_exp_arg_mul_I
#check @Complex.exp_int_mul_two_pi_mul_I
#check @squeeze_zero_norm
#check @tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
#check @Filter.Tendsto.frequently
#check @Complex.ofReal_tsum
#check @pow_eq_one_iff_of_orderOf_eq_zero
#check @Convex.isPreconnected
#check @convex_ball
#check @Complex.norm_intCast
#check (inferInstance : Filter.NeBot (nhdsWithin (1:ℝ) (Set.Iio 1)))
#check (inferInstance : Filter.NeBot (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ))
#check @Filter.Eventually.frequently
#check @Complex.ofReal_pow
#check @FormalMultilinearSeries.ofScalars
#check @Metric.mem_ball_self
#check @Real.rpow_natCast
#check @Complex.arg
#check @tendsto_pow_atTop_nhds_zero_of_lt_one

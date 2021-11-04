/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.exponential
import data.complex.exponential
import topology.metric_space.cau_seq_filter

/-!
# Compatibilty of `real.exp` and `complex.exp` with the exponential map

- `complex.exp_eq_exp_ℂ_ℂ` : `complex.exp = exp ℂ ℂ`
- `real.exp_eq_exp_ℝ_ℝ` : `real.exp = exp ℝ ℝ`

-/

open is_R_or_C

section complex

lemma complex.exp_eq_exp_ℂ_ℂ : complex.exp = exp ℂ ℂ :=
begin
  refine funext (λ x, _),
  rw [complex.exp, exp_eq_tsum_field],
  exact tendsto_nhds_unique x.exp'.tendsto_limit
    (exp_series_field_summable x).has_sum.tendsto_sum_nat
end

end complex

section real

lemma real.exp_eq_exp_ℝ_ℝ : real.exp = exp ℝ ℝ :=
begin
  refine funext (λ x, _),
  rw [real.exp, complex.exp_eq_exp_ℂ_ℂ, ← exp_ℝ_ℂ_eq_exp_ℂ_ℂ, exp_eq_tsum, exp_eq_tsum_field,
      ← re_to_complex, ← re_clm_apply, re_clm.map_tsum (exp_series_summable' (x : ℂ))],
  refine tsum_congr (λ n, _),
  rw [re_clm.map_smul, ← complex.of_real_pow, re_clm_apply, re_to_complex, complex.of_real_re,
      smul_eq_mul, one_div, mul_comm, div_eq_mul_inv]
end

end real

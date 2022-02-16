/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.function.convergence_in_measure

/-!
# Uniform integrability


## Main results

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

open set filter topological_space

variables {α β ι : Type*} {m : measurable_space α} {μ : measure α}
variables [measurable_space β] [normed_group β]

/-- Also known as uniformly absolutely continuous integrals. -/
def unif_integrable {m : measurable_space α} (f : ι → α → β) (p : ℝ≥0∞) (μ : measure α) : Prop :=
∀ ⦃ε : ℝ⦄ (hε : 0 < ε), ∃ (δ : ℝ) (hδ : 0 < δ), ∀ i s, measurable_set s → μ s ≤ ennreal.of_real δ →
snorm (s.indicator (f i)) p μ ≤ ennreal.of_real ε

/-- In probability theory, a family of functions is uniformly integrable if it is uniformly
integrable in the measure theory sense and is uniformly bounded. -/
def uniform_integrable {m : measurable_space α}
  (μ : measure α) (f : ι → α → β) (p : ℝ≥0∞) : Prop :=
(∀ i, measurable (f i)) ∧ unif_integrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, snorm (f i) p μ ≤ C

section unif_integrable

variables (μ)
variables [borel_space β] [second_countable_topology β] [is_finite_measure μ] {p : ℝ≥0∞}

lemma tendsto_indicator_ge_zero (f : α → β) (x : α):
  tendsto (λ M : ℕ, {x | (M : ℝ) ≤ ∥f x∥₊}.indicator f x) at_top (𝓝 0) :=
begin
  refine @tendsto_at_top_of_eventually_const _ _ _ _ _ _ _ (nat.ceil (∥f x∥₊ : ℝ) + 1) (λ n hn, _),
  rw indicator_of_not_mem,
  simp only [not_le, mem_set_of_eq],
  refine lt_of_le_of_lt (nat.le_ceil _) _,
  refine lt_of_lt_of_le (lt_add_one _) _,
  norm_cast,
  rwa [ge_iff_le, coe_nnnorm] at hn,
end

lemma mem_ℒp.integral_indicator_ge_le'
  {f : α → β} (hf : mem_ℒp f 1 μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, ∫⁻ x, ∥{x | M ≤ ∥f x∥₊}.indicator f x∥₊ ∂μ ≤ ennreal.of_real ε :=
begin
  have htendsto : ∀ᵐ x ∂μ, tendsto (λ M : ℕ, {x | (M : ℝ) ≤ ∥f x∥₊}.indicator f x) at_top (𝓝 0) :=
    univ_mem' (id $ λ x, tendsto_indicator_ge_zero f x),
  have hmeas : ∀ M : ℕ, ae_measurable ({x | (M : ℝ) ≤ ∥f x∥₊}.indicator f) μ,
  { cases hf,
    measurability },
  have hbound : has_finite_integral (λ x, ∥f x∥) μ,
  { rw mem_ℒp_one_iff_integrable at hf,
    exact hf.norm.2 },
  have := tendsto_lintegral_norm_of_dominated_convergence hmeas hbound _ htendsto,
  { rw ennreal.tendsto_at_top ennreal.zero_ne_top at this,
    { obtain ⟨M, hM⟩ := this (ennreal.of_real ε) (ennreal.of_real_pos.2 hε),
      simp only [true_and, ge_iff_le, zero_tsub, zero_le,
                sub_zero, zero_add, coe_nnnorm, mem_Icc] at hM,
      refine ⟨M, _⟩,
      convert hM M le_rfl,
      ext1 x,
      simp only [coe_nnnorm, ennreal.of_real_eq_coe_nnreal (norm_nonneg _)],
      refl },
    { apply_instance } },
  { refine λ n, univ_mem' (id $ λ x, _),
    by_cases hx : (n : ℝ) ≤ ∥f x∥,
    { dsimp,
      rwa indicator_of_mem },
    { dsimp,
      rw [indicator_of_not_mem, norm_zero],
      { exact norm_nonneg _ },
      { assumption } } }
end

lemma mem_ℒp.integral_indicator_ge_le
  {f : α → β} (hf : mem_ℒp f 1 μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, 0 ≤ M ∧ ∫⁻ x, ∥{x | M ≤ ∥f x∥₊}.indicator f x∥₊ ∂μ ≤ ennreal.of_real ε :=
let ⟨M, hM⟩ := hf.integral_indicator_ge_le' μ hmeas hε in ⟨max M 0, le_max_right _ _, by simpa⟩

--move
lemma ennreal.lt_add_one {a : ℝ≥0∞} (ha : a ≠ ∞) : a < a + 1 :=
ennreal.lt_add_right ha one_ne_zero

lemma ennreal.rpow_inv_le_iff
  {a : ℝ} {b c : ℝ≥0∞} (ha : 0 < a) : b ^ (1 / a) ≤ c ↔ b ≤ c ^ a :=
begin
  nth_rewrite 0 ← ennreal.rpow_one c,
  nth_rewrite 1 ← @_root_.mul_inv_cancel _ _ a ha.ne.symm,
  rw [ennreal.rpow_mul, ← one_div, ennreal.rpow_le_rpow_iff (one_div_pos.2 ha)],
end

-- lemma ennreal.pow_one_div_lt_iff_lt_pow
--   {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : b ^ (1 / a) < c ↔ b < c ^ a :=
-- begin
--   refine ⟨lt_pow_of_pow_one_div_lt ha hb, λ h, _⟩,
--   convert real.rpow_lt_rpow hb h (one_div_pos.2 ha),
--   rw [← real.rpow_mul, mul_one_div_cancel ha.ne.symm, real.rpow_one],
--   sorry
-- end

lemma mem_ℒp.snorm_ess_sup_indicator_ge_eq_zero
  {f : α → β} (hf : mem_ℒp f ∞ μ) (hmeas : measurable f) :
  ∃ M : ℝ, snorm_ess_sup ({x | M ≤ ∥f x∥₊}.indicator f) μ = 0 :=
begin
  have hbdd : snorm_ess_sup f μ < ∞ := hf.snorm_lt_top,
  refine ⟨(snorm f ∞ μ + 1).to_real, _⟩,
  rw snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict,
  have : μ.restrict {x : α | (snorm f ⊤ μ + 1).to_real ≤ ∥f x∥₊} = 0,
  { simp only [coe_nnnorm, snorm_exponent_top, measure.restrict_eq_zero],
    have : {x : α | (snorm_ess_sup f μ + 1).to_real ≤ ∥f x∥} ⊆
      {x : α | snorm_ess_sup f μ < ∥f x∥₊},
    { intros x hx,
      rw [mem_set_of_eq, ← ennreal.to_real_lt_to_real hbdd.ne ennreal.coe_lt_top.ne,
          ennreal.coe_to_real, coe_nnnorm],
      refine lt_of_lt_of_le _ hx,
      rw ennreal.to_real_lt_to_real hbdd.ne,
      { exact ennreal.lt_add_one hbdd.ne },
      { exact (ennreal.add_lt_top.2 ⟨hbdd, ennreal.one_lt_top⟩).ne } },
    rw ← nonpos_iff_eq_zero,
    refine (measure_mono this).trans _,
    have hle := coe_nnnorm_ae_le_snorm_ess_sup f μ,
    simp_rw [ae_iff, not_le] at hle,
    exact nonpos_iff_eq_zero.2 hle },
  rw [this, snorm_ess_sup_measure_zero],
  exact measurable_set_le measurable_const hmeas.nnnorm.subtype_coe,
end

-- example {f : α → β} (hf : mem_ℒp f p μ) : integrable (λ x, ∥f x∥₊ ^ p.to_real) μ :=

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
lemma mem_ℒp.snorm_indicator_ge_le'
  {f : α → β} (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, snorm ({x | M ≤ ∥f x∥₊}.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  by_cases hp_ne_zero : p = 0,
  { refine ⟨1, hp_ne_zero.symm ▸ _⟩,
    simp [snorm_exponent_zero] },
  by_cases hp_ne_top : p = ∞,
  { subst hp_ne_top,
    obtain ⟨M, hM⟩ := hf.snorm_ess_sup_indicator_ge_eq_zero μ hmeas,
    refine ⟨M, _⟩,
    simp only [snorm_exponent_top, hM, zero_le] },
  obtain ⟨M, hM', hM⟩ := @mem_ℒp.integral_indicator_ge_le _ _ _ μ _ _ _ _ _
    (λ x, ∥f x∥^p.to_real) _ _ _ (real.rpow_pos_of_pos hε p.to_real),
  { refine ⟨M ^(1 / p.to_real), _⟩,
    rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top,
        ← ennreal.rpow_one (ennreal.of_real ε)],
    conv_rhs { rw ← mul_one_div_cancel (ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm },
    rw [ennreal.rpow_mul,
        ennreal.rpow_le_rpow_iff (one_div_pos.2 $ ennreal.to_real_pos hp_ne_zero hp_ne_top),
        ennreal.of_real_rpow_of_pos hε],
    convert hM,
    ext1 x,
    rw [ennreal.coe_rpow_of_nonneg _ ennreal.to_real_nonneg,
        nnnorm_indicator_eq_indicator_nnnorm, nnnorm_indicator_eq_indicator_nnnorm],
    have hiff : M ^ (1 / p.to_real) ≤ ∥f x∥₊ ↔ M ≤ ∥∥f x∥ ^ p.to_real∥₊,
    { rw [coe_nnnorm, coe_nnnorm, real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
          ← real.rpow_le_rpow_iff hM' (real.rpow_nonneg_of_nonneg (norm_nonneg _) _)
          (one_div_pos.2 $ ennreal.to_real_pos hp_ne_zero hp_ne_top),
          ← real.rpow_mul (norm_nonneg _),
          mul_one_div_cancel (ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm, real.rpow_one] },
    by_cases hx : x ∈ {x : α | M ^ (1 / p.to_real) ≤ ∥f x∥₊},
    { rw [set.indicator_of_mem hx,set.indicator_of_mem, real.nnnorm_of_nonneg], refl,
      change _ ≤ _,
      rwa ← hiff },
    { rw [set.indicator_of_not_mem hx, set.indicator_of_not_mem],
      { simp [(ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm] },
      { change ¬ _ ≤ _,
        rwa ← hiff } } },
  { have := hf.snorm_lt_top,
    rw snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top at this,
    rw mem_ℒp_one_iff_integrable,
    refine ⟨hf.1.norm.pow_const _, _⟩,
    rw has_finite_integral,
    convert ennreal.rpow_lt_top_of_nonneg (@ennreal.to_real_nonneg p) this.ne,
    rw [← ennreal.rpow_mul, one_div_mul_cancel (ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm,
        ennreal.rpow_one],
    congr,
    ext1 x,
    rw [ennreal.coe_rpow_of_nonneg _ ennreal.to_real_nonneg, real.nnnorm_of_nonneg],
    congr },
  { exact hmeas.norm.pow_const _ }
end

lemma mem_ℒp.snorm_indicator_ge_le_pos
  {f : α → β} (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ M : ℝ, 0 < M ∧ snorm ({x | M ≤ ∥f x∥₊}.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  obtain ⟨M, hM⟩ := hf.snorm_indicator_ge_le' μ hmeas hε,
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    le_trans (snorm_mono (λ x, _)) hM⟩,
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm],
  refine indicator_le_indicator_of_subset (λ x hx, _) (λ x, norm_nonneg _) x,
  change max _ _ ≤ _ at hx, -- removing the `change` breaks the proof!
  exact (max_le_iff.1 hx).1,
end

lemma mem_ℒp.snorm_indicator_ge_le_of_bound (hp_top : p ≠ ∞) {f : α → β} (hf : mem_ℒp f p μ)
  {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hf : ∀ x, ∥f x∥ < M) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  by_cases hM : M ≤ 0,
  { refine ⟨1, zero_lt_one, λ s hs hμ, _⟩,
    rw (_ : f = 0),
    { simp [hε.le] },
    { ext x,
      rw [pi.zero_apply, ← norm_le_zero_iff],
      exact (lt_of_lt_of_le (hf x) hM).le } },
  rw not_le at hM,
  refine ⟨(ε / M) ^ p.to_real, real.rpow_pos_of_pos (div_pos hε hM) _, λ s hs hμ, _⟩,
  by_cases hp : p = 0,
  { simp [hp] },
  rw snorm_indicator_eq_snorm_restrict hs,
  have haebdd : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ M,
  { filter_upwards,
    exact (λ x, (hf x).le) },
  refine le_trans (snorm_le_of_ae_bound haebdd) _,
  rw [measure.restrict_apply measurable_set.univ, univ_inter,
    ← ennreal.le_div_iff_mul_le (or.inl _) (or.inl ennreal.of_real_ne_top)],
  { rw [← one_div, ennreal.rpow_inv_le_iff (ennreal.to_real_pos hp hp_top)],
    refine le_trans hμ _,
    rw [← ennreal.of_real_rpow_of_pos (div_pos hε hM),
      ennreal.rpow_le_rpow_iff (ennreal.to_real_pos hp hp_top), ennreal.of_real_div_of_pos hM],
    exact le_rfl },
  { simpa only [ennreal.of_real_eq_zero, not_le, ne.def] },
end

-- move
lemma snorm_le_snorm_of_measure_le {m : measurable_space α} {f : α → β} {μ ν : measure α}
  (hμν : μ ≤ ν) : snorm f p μ ≤ snorm f p ν :=
begin
  by_cases hp_zero : p = 0,
  { rw hp_zero,
    simp },
  by_cases hp_top : p = ∞,
  { rw hp_top,
    simp only [snorm_exponent_top, snorm_ess_sup],
    refine ess_sup_mono_measure (measure.ae_le_iff_absolutely_continuous.1 (ae_mono hμν)) },
  rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top, snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top],
  exact ennreal.rpow_le_rpow (lintegral_mono' hμν le_rfl)
    (one_div_nonneg.2 ennreal.to_real_nonneg),
end

lemma mem_ℒp.snorm_indicator_ge_le'' (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  {f : α → β} (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ 2 * ennreal.of_real ε :=
begin
  obtain ⟨M, hMpos, hM⟩ :=  hf.snorm_indicator_ge_le_pos μ hmeas hε,
  obtain ⟨δ, hδpos, hδ⟩ := @mem_ℒp.snorm_indicator_ge_le_of_bound _ _ _ μ _ _ _ _ _ _ hp_top
    ({x | ∥f x∥ < M}.indicator f)
    (hf.indicator (measurable_set_lt hmeas.nnnorm.subtype_coe measurable_const)) _ hε M _,
  { refine ⟨δ, hδpos, λ s hs hμs, _⟩,
    rw (_ : f = {x : α | M ≤ ∥f x∥₊}.indicator f + {x : α | ∥f x∥ < M}.indicator f),
    { rw snorm_indicator_eq_snorm_restrict hs,
      refine le_trans (snorm_add_le _ _ hp_one) _,
      { exact measurable.ae_measurable (hmeas.indicator
        (measurable_set_le measurable_const hmeas.nnnorm.subtype_coe)) },
      { exact measurable.ae_measurable (hmeas.indicator
        (measurable_set_lt hmeas.nnnorm.subtype_coe measurable_const)) },
      { rw two_mul,
        refine add_le_add (le_trans (snorm_le_snorm_of_measure_le measure.restrict_le_self) hM) _,
        rw ← snorm_indicator_eq_snorm_restrict hs,
        exact hδ s hs hμs } },
    { ext x,
      by_cases hx : M ≤ ∥f x∥,
      { rw [pi.add_apply, indicator_of_mem, indicator_of_not_mem, add_zero];
        simpa },
      { rw [pi.add_apply, indicator_of_not_mem, indicator_of_mem, zero_add];
        simpa using hx } } },
  { intros x,
    rw [norm_indicator_eq_indicator_norm, indicator_apply],
    split_ifs,
    exacts [h, hMpos] }
end

lemma mem_ℒp.snorm_indicator_ge_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
  {f : α → β} (hf : mem_ℒp f p μ) (hmeas : measurable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ ≤ ennreal.of_real ε :=
begin
  obtain ⟨δ, hδpos, hδ⟩ := hf.snorm_indicator_ge_le'' μ hp_one hp_top hmeas (half_pos hε),
  refine ⟨δ, hδpos, λ s hs hμs, le_trans (hδ s hs hμs) _⟩,
  rw [ennreal.of_real_div_of_pos zero_lt_two, (by norm_num : ennreal.of_real 2 = 2),
    ennreal.mul_div_cancel'];
  norm_num,
end

lemma unif_integrable_subsingleton [subsingleton ι] {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  sorry
end

lemma unif_integrable_finite [fintype ι] {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  sorry
end

lemma snorm_sub_le_of_dist_bdd
  {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞) {s : set α} (hs : measurable_set[m] s)
  {f g : α → β} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x ∈ s, dist (f x) (g x) ≤ c) :
  snorm (s.indicator (f - g)) p μ ≤ ennreal.of_real c * μ s ^ (1 / p.to_real) :=
begin
  have : ∀ x, ∥s.indicator (f - g) x∥ ≤ ∥s.indicator (λ x, c) x∥,
  { intro x,
    by_cases hx : x ∈ s,
    { rw [indicator_of_mem hx, indicator_of_mem hx, pi.sub_apply, ← dist_eq_norm,
          real.norm_eq_abs, abs_of_nonneg hc],
      exact hf x hx },
    { simp [indicator_of_not_mem hx] } },
  refine le_trans (snorm_mono this) _,
  rw snorm_indicator_const hs hp hp',
  by_cases hμs : μ s = 0,
  { rw [hμs, ennreal.zero_rpow_of_pos, mul_zero, mul_zero],
    { exact le_rfl },
    { rw one_div_pos,
      exact ennreal.to_real_pos hp hp' } },
  { rw [ennreal.mul_le_mul_right, real.nnnorm_of_nonneg hc, ennreal.coe_nnreal_eq],
    { exact le_rfl },
    { intro h,
      obtain (h' | h') := ennreal.rpow_eq_zero_iff.1 h,
      { exact hμs h'.1 },
      { exact (measure_lt_top μ s).ne h'.1 } },
    { intro h,
      obtain (h' | h') := ennreal.rpow_eq_top_iff.1 h,
      { exact hμs h'.1 },
      { exact (measure_lt_top μ s).ne h'.1 } } }
end

-- We can remove the measurability assumption so this lemma should be private once we have
-- generalized it

-- To generalize the below to convergence in measure we need that convergence in measure implies
-- existence of convergent a.e. subsequence
-- We have this now: `tendsto_in_measure.exists_seq_tendsto_ae`

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
lemma tendsto_Lp_of_unif_integrable (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  (hg' : mem_ℒp g p μ) (hui : unif_integrable f p μ)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
begin
  rw ennreal.tendsto_at_top ennreal.zero_ne_top,
  swap, apply_instance,
  intros ε hε,
  by_cases ε < ∞,
  { by_cases hμ : μ = 0,
    { exact ⟨0, λ n hn, by simp [hμ]⟩ },
    have hε' : 0 < ε.to_real / 3 :=
      div_pos (ennreal.to_real_pos (gt_iff_lt.1 hε).ne.symm h.ne) (by norm_num),
    have hdivp : 0 ≤ 1 / p.to_real,
    { refine one_div_nonneg.2 _,
      rw [← ennreal.zero_to_real, ennreal.to_real_le_to_real ennreal.zero_ne_top hp'],
      exact le_trans ennreal.zero_lt_one.le hp },
    have hpow : 0 < (measure_univ_nnreal μ) ^ (1 / p.to_real) :=
      real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _,
    obtain ⟨δ₁, hδ₁, hsnorm₁⟩ := hui hε',
    obtain ⟨δ₂, hδ₂, hsnorm₂⟩ := hg'.snorm_indicator_ge_le μ hp hp' hg hε',
    obtain ⟨t, htm, ht₁, ht₂⟩ := tendsto_uniformly_on_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂),
    rw metric.tendsto_uniformly_on_iff at ht₂,
    specialize ht₂ (ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))
      (div_pos (ennreal.to_real_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by norm_num) hpow)),
    obtain ⟨N, hN⟩ := eventually_at_top.1 ht₂, clear ht₂,
    refine ⟨N, λ n hn, _⟩,
    simp only [mem_Icc, true_and, zero_tsub, zero_le, zero_add],
    rw [← t.indicator_self_add_compl (f n - g)],
    refine le_trans (snorm_add_le ((((hf n).sub hg).indicator htm).ae_measurable)
      (((hf n).sub hg).indicator htm.compl).ae_measurable hp) _,
    rw [sub_eq_add_neg, indicator_add' t, indicator_neg'],
    refine le_trans (add_le_add_right (snorm_add_le ((hf n).indicator htm).ae_measurable
      (hg.indicator htm).neg.ae_measurable hp) _) _,
    have hnf : snorm (t.indicator (f n)) p μ ≤ ennreal.of_real (ε.to_real / 3),
    { refine hsnorm₁ n t htm (le_trans ht₁ _),
      rw ennreal.of_real_le_of_real_iff hδ₁.le,
      exact min_le_left _ _ },
    have hng : snorm (t.indicator g) p μ ≤ ennreal.of_real (ε.to_real / 3),
    { refine hsnorm₂ t htm (le_trans ht₁ _),
      rw ennreal.of_real_le_of_real_iff hδ₂.le,
      exact min_le_right _ _ },
    have hlt : snorm (tᶜ.indicator (f n - g)) p μ ≤ ennreal.of_real (ε.to_real / 3),
    { specialize hN n hn,
      have := snorm_sub_le_of_dist_bdd μ ((lt_of_lt_of_le ennreal.zero_lt_one hp).ne.symm)
        hp' htm.compl _ (λ x hx, (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) ≤ ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))),
      refine le_trans this _,
      rw [div_mul_eq_div_mul_one_div, ← ennreal.of_real_to_real (measure_lt_top μ tᶜ).ne,
          ennreal.of_real_rpow_of_nonneg ennreal.to_real_nonneg hdivp, ← ennreal.of_real_mul,
          mul_assoc],
      { refine ennreal.of_real_le_of_real (mul_le_of_le_one_right hε'.le _),
        rw [mul_comm, mul_one_div, div_le_one],
        { refine real.rpow_le_rpow ennreal.to_real_nonneg
            (ennreal.to_real_le_of_le_of_real (measure_univ_nnreal_pos hμ).le _) hdivp,
          rw [ennreal.of_real_coe_nnreal, coe_measure_univ_nnreal],
          exact measure_mono (subset_univ _) },
        { exact real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _ } },
      { refine mul_nonneg (hε').le (one_div_nonneg.2 hpow.le) },
      { rw div_mul_eq_div_mul_one_div,
        exact mul_nonneg hε'.le (one_div_nonneg.2 hpow.le) } },
    have : ennreal.of_real (ε.to_real / 3) = ε / 3,
    { rw [ennreal.of_real_div_of_pos (show (0 : ℝ) < 3, by norm_num), ennreal.of_real_to_real h.ne],
      simp },
    rw this at hnf hng hlt,
    rw [snorm_neg, ← ennreal.add_thirds ε, ← sub_eq_add_neg],
    exact add_le_add_three hnf hng hlt },
  { rw [not_lt, top_le_iff] at h,
    exact ⟨0, λ n hn, by simp [h]⟩ }
end

lemma unif_integrable_of_tendsto_Lp {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  unif_integrable f p μ :=
begin
  sorry
end

lemma ae_tendsto_of_tendsto_Lp {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  tendsto_in_measure μ f g :=
sorry

end unif_integrable

variables {f : ι → α → β} {p : ℝ≥0∞}

lemma uniform_integrable.mem_ℒp (hf : uniform_integrable μ f p) (i : ι) :
  mem_ℒp (f i) p μ :=
⟨(hf.1 i).ae_measurable, let ⟨_, _, hC⟩ := hf.2 in lt_of_le_of_lt (hC i) ennreal.coe_lt_top⟩

end measure_theory

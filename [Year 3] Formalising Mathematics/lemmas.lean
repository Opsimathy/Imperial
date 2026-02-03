import analysis.special_functions.pow
import measure_theory.function.lp_space

/-! This file contains some lemmas required to the results in `main.lean`. -/
open_locale ennreal filter nnreal

variables {α E : Type*} 

lemma ennreal.rpow_one_div_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : 
  x ^ (1 / z) ≤ y ↔ x ≤ y ^ z :=
begin
  nth_rewrite 0 ← ennreal.rpow_one y,
  nth_rewrite 1 ← @_root_.mul_inv_cancel _ _ z hz.ne.symm,
  rw [ennreal.rpow_mul, ← one_div, ennreal.rpow_le_rpow_iff (one_div_pos.2 hz)],
end

namespace measure_theory

variables [measurable_space α] [measurable_space E] [normed_group E] {μ : measure α} {p : ℝ≥0∞}

lemma mem_ℒp.norm_rpow [opens_measurable_space E] {f : α → E}
  (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp (λ (x : α), ∥f x∥ ^ p.to_real) 1 μ :=
begin
  refine ⟨hf.1.norm.pow_const _, _⟩,
  have := hf.snorm_ne_top,
  rw snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top at this,
  rw snorm_one_eq_lintegral_nnnorm,
  convert ennreal.rpow_lt_top_of_nonneg (@ennreal.to_real_nonneg p) this,
  rw [← ennreal.rpow_mul, one_div_mul_cancel (ennreal.to_real_pos hp_ne_zero hp_ne_top).ne.symm,
      ennreal.rpow_one],
  congr,
  ext1 x,
  rw [ennreal.coe_rpow_of_nonneg _ ennreal.to_real_nonneg, real.nnnorm_of_nonneg],
  congr
end

lemma _root_.filter.eventually_eq.restrict {δ : Type*} 
  {f g : α → δ} {s : set α} (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.restrict s] g :=
begin -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono _,
  rw measure.ae_le_iff_absolutely_continuous,
  exact measure.absolutely_continuous_of_le measure.restrict_le_self,
end

lemma indicator_meas_zero {β : Type*} [has_zero β] {f : α → β} {s : set α} (hs : μ s = 0) : 
  set.indicator s f =ᵐ[μ] 0 :=
(set.indicator_empty' f) ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)

lemma indicator_ae_eq_zero_of_ae_eq_zero {s : set α} {f : α → E} (hf : f =ᵐ[μ] 0) : 
  s.indicator f =ᵐ[μ] 0 :=
begin
  filter_upwards [hf] with x hx,
  by_cases x ∈ s,
  { rwa set.indicator_of_mem h },
  { rw set.indicator_of_not_mem h,
    refl }
end

lemma snorm_indicator_ge_of_bdd_below (hp : p ≠ 0) (hp' : p ≠ ∞)
  {f : α → E} (C : ℝ≥0) {s : set α} (hs : measurable_set s)
  (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ∥s.indicator f x∥₊) :
  C • μ s ^ (1 / p.to_real) ≤ snorm (s.indicator f) p μ :=
begin
  rw [ennreal.smul_def, smul_eq_mul, snorm_eq_lintegral_rpow_nnnorm hp hp',
    ennreal.le_rpow_one_div_iff (ennreal.to_real_pos hp hp'),
    ennreal.mul_rpow_of_nonneg _ _ ennreal.to_real_nonneg,
    ← ennreal.rpow_mul, one_div_mul_cancel (ennreal.to_real_pos hp hp').ne.symm, ennreal.rpow_one,
    ← set_lintegral_const, ← lintegral_indicator _ hs],
  refine lintegral_mono_ae _,
  filter_upwards [hf] with x hx,
  rw nnnorm_indicator_eq_indicator_nnnorm,
  by_cases hxs : x ∈ s,
  { simp only [set.indicator_of_mem hxs] at ⊢ hx,
    exact ennreal.rpow_le_rpow (ennreal.coe_le_coe.2 (hx hxs)) ennreal.to_real_nonneg },
  { simp [set.indicator_of_not_mem hxs] },
end

end measure_theory

section tendsto

open filter

/-! This section shows a sequence converges if and only if all of its subsequence 
  has a convergent subsequence. -/

lemma tendsto_iff_forall_eventually_mem {α ι : Type*} {x : ι → α} {f : filter α} {l : filter ι} :
  tendsto x l f ↔ ∀ s ∈ f, ∀ᶠ n in l, x n ∈ s :=
by { rw tendsto_def, refine forall_congr (λ s, imp_congr_right (λ hsf, _)), refl, }

lemma not_tendsto_iff_exists_frequently_nmem {α ι : Type*} {x : ι → α} {f : filter α}
  {l : filter ι} :
  ¬ tendsto x l f ↔ ∃ s ∈ f, ∃ᶠ n in l, x n ∉ s :=
begin
  rw tendsto_iff_forall_eventually_mem,
  push_neg,
  refine exists_congr (λ s, _),
  rw [not_eventually, exists_prop],
end

lemma frequently_iff_seq_frequently {ι : Type*} {l : filter ι} {p : ι → Prop}
  [hl : l.is_countably_generated] :
  (∃ᶠ n in l, p n) ↔ ∃ (x : ℕ → ι), tendsto x at_top l ∧ ∃ᶠ (n : ℕ) in at_top, p (x n) :=
begin
  refine ⟨λ h_freq, _, λ h_exists_freq, _⟩,
  { haveI : ne_bot (l ⊓ 𝓟 {x : ι | p x}), by simpa [ne_bot_iff, inf_principal_eq_bot],
    obtain ⟨x, hx⟩ := exists_seq_tendsto (l ⊓ (𝓟 {x : ι | p x})),
    rw tendsto_inf at hx,
    cases hx with hx_l hx_p,
    refine ⟨x, hx_l, _⟩,
    rw tendsto_principal at hx_p,
    exact hx_p.frequently, },
  { obtain ⟨x, hx_tendsto, hx_freq⟩ := h_exists_freq,
    simp_rw [filter.frequently, filter.eventually] at hx_freq ⊢,
    have : {n : ℕ | ¬p (x n)} = {n | x n ∈ {y | ¬ p y}} := rfl,
    rw [this, ← mem_map'] at hx_freq,
    contrapose! hx_freq,
    exact hx_tendsto hx_freq, },
end

lemma subseq_forall_of_frequently {ι : Type*} {x : ℕ → ι} {p : ι → Prop} {l : filter ι}
  (h_tendsto : tendsto x at_top l) (h : ∃ᶠ n in at_top, p (x n)) :
  ∃ ns : ℕ → ℕ, tendsto (λ n, x (ns n)) at_top l ∧ ∀ n, p (x (ns n)) :=
begin
  rw tendsto_iff_seq_tendsto at h_tendsto,
  choose ns hge hns using frequently_at_top.1 h,
  exact ⟨ns, h_tendsto ns (tendsto_at_top_mono hge tendsto_id), hns⟩,
end

lemma exists_seq_forall_of_frequently {ι : Type*} {l : filter ι} {p : ι → Prop}
  [hl : l.is_countably_generated] (h : ∃ᶠ n in l, p n) :
  ∃ ns : ℕ → ι, tendsto ns at_top l ∧ ∀ n, p (ns n) :=
begin
  rw frequently_iff_seq_frequently at h,
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h,
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq,
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩,
end

/-- A sequence converges if every subsequence has a convergent subsequence. -/
lemma tendsto_of_subseq_tendsto {α ι : Type*}
  {x : ι → α} {f : filter α} {l : filter ι} [l.is_countably_generated]
  (hxy : ∀ ns : ℕ → ι, tendsto ns at_top l →
    ∃ ms : ℕ → ℕ, tendsto (λ n, x (ns $ ms n)) at_top f) :
  tendsto x l f :=
begin
  by_contra h,
  obtain ⟨s, hs, hfreq⟩ : ∃ s ∈ f, ∃ᶠ n in l, x n ∉ s,
    by rwa not_tendsto_iff_exists_frequently_nmem at h,
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq,
  specialize hxy y hy_tendsto,
  obtain ⟨ms, hms_tendsto⟩ := hxy,
  specialize hms_tendsto hs,
  rw mem_map at hms_tendsto,
  have hms_freq : ∀ (n : ℕ), x (y (ms n)) ∉ s, from λ n, hy_freq (ms n),
  have h_empty : (λ (n : ℕ), x (y (ms n))) ⁻¹' s = ∅,
  { ext1 n,
    simp only [set.mem_preimage, set.mem_empty_eq, iff_false],
    exact hms_freq n, },
  rw h_empty at hms_tendsto,
  exact empty_not_mem at_top hms_tendsto,
end

end tendsto

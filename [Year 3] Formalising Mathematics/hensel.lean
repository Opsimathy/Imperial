
import tools

variables {𝕜 : Type} [normed_field 𝕜] [nonarchimedean 𝕜]

variables (f : polynomial (disc 𝕜)) (t₀ : disc 𝕜) (ht₀ : ∥f.eval t₀∥ < ∥f.derivative.eval t₀∥ ^ 2)

/-- A Newton-style sequence converging to a root of `f` near `t₀`. -/
noncomputable def seq : ℕ → disc 𝕜
| 0     := t₀
| (n+1) :=
  if h : ∥f.eval (seq n)∥ ≤ ∥f.derivative.eval (seq n)∥ then
    seq n - disc.divide h
  else t₀

namespace seq
  /-- The first term of `seq` is `t₀`. -/
  theorem def_zero : seq f t₀ 0 = t₀ := rfl

  variables {f} {t₀}
  
  /-- Subsequent terms `tₙ₊₁` of `seq` are formed by subtracting `f(tₙ)/f'(tₙ)` from `tₙ`,
    the definition of which requires `∥f(tₙ)∥ ≤ ∥f'(tₙ)∥`. -/
  theorem def_succ {n : ℕ} (h : ∥f.eval (seq f t₀ n)∥ ≤ ∥f.derivative.eval (seq f t₀ n)∥) :
    seq f t₀ (n+1) = seq f t₀ n - disc.divide h := by simp only [seq, dif_pos h]
end seq

/-- The constant `κ` is defined as `∥f(t₀)∥ / ∥f'(t₀)∥^2`. -/
noncomputable def κ : ℝ := ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥ ^ 2

/-- The constant `κ` is non-negative. -/
theorem zero_le_κ : 0 ≤ κ f t₀ := div_nonneg (norm_nonneg _) (sq_nonneg _)

include ht₀

/-- Given the inequality `∥f(t₀)∥ < ∥f'(t₀)∥^2`, the constant `κ` is strictly
  less than `1`. -/
theorem κ_lt_one : κ f t₀ < 1 := (div_lt_one (lt_of_le_of_lt (norm_nonneg _) ht₀)).mpr ht₀

/-- For every `n : ℕ`, `seq` satisfies the following properties:
    • `∥f(tₙ₊₁) ∥ ≤ κ * ∥f(tₙ)∥`,
    • `∥f'(tₙ₊₁)∥ = ∥f(t₀)∥`,
    • `∥tₙ₊₁ - tₙ∥ ≤ κⁿ * ∥f(t₀)∥/∥f'(t₀)∥`,
    • `∥f(tₙ₊₁)∥ ≤ κⁿ⁺¹ * ∥f(t₀)∥`. -/
theorem seq_properties (n : ℕ) :
  ∥f.eval (seq f t₀ (n+1))∥ ≤ (κ f t₀) * ∥f.eval (seq f t₀ n)∥ ∧
  ∥f.derivative.eval (seq f t₀ (n+1))∥ = ∥f.derivative.eval t₀∥ ∧
  ∥seq f t₀ (n+1) - seq f t₀ n∥ ≤ (κ f t₀) ^ n * ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥ ∧
  ∥f.eval (seq f t₀ (n+1))∥ ≤ (κ f t₀) ^ (n + 1) * ∥f.eval t₀∥ :=
begin
  have hf' : f.derivative.eval t₀ ≠ 0,
    { intro h,
      have := lt_of_le_of_lt (norm_nonneg _) ht₀,
      rw [h, norm_zero, zero_pow zero_lt_two] at this,
      exact lt_irrefl 0 this },
  induction n with n ih,
  { have h : ∥f.eval (seq f t₀ 0)∥ ≤ ∥f.derivative.eval (seq f t₀ 0)∥ :=
      le_of_lt (lt_of_lt_of_le ht₀ (sq_le (norm_nonneg _) (disc.norm_le_one _))),
    have h' : ∥f.eval (seq f t₀ 0 - disc.divide h)∥ ≤ κ f t₀ * ∥f.eval (seq f t₀ 0)∥,
    { cases taylor₂ f (seq f t₀ 0) with g hg,
      rw [hg ((seq f t₀ 0) - disc.divide h), sub_right_comm, sub_self, zero_sub,
        neg_mul, disc.divide.mul_cancel h hf', add_neg_self, zero_add, disc.norm_mul],
      have : ∥(-disc.divide h) ^ 2∥ = κ f t₀ * ∥f.eval (seq f t₀ 0)∥,
      { rw [disc.norm_pow, norm_neg, disc.divide.norm, div_pow,
          sq, mul_div_assoc, mul_comm], refl },
      exact this ▸ mul_le_of_le_one_right (norm_nonneg _) (disc.norm_le_one _) },
    rw [seq.def_succ h], split,
    { exact h' },
    { split,
      { conv_rhs { rw [←norm_neg (f.derivative.eval t₀), ←seq.def_zero f t₀] },
        apply nonarchimedean.eq_norm_of_ne_max,
        cases taylor₁ f.derivative (seq f t₀ 0) with g hg,
        conv_lhs { rw [hg (seq f t₀ 0 - disc.divide h), add_right_comm, add_neg_self,
          zero_add, sub_right_comm, sub_self, zero_sub] },
        apply ne_of_lt,
        refine lt_of_lt_of_le _ (le_max_right _ _),
        rw [disc.norm_mul],
        apply lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (disc.norm_le_one _)),
        rw [norm_neg, norm_neg, disc.divide.norm],
        apply (div_lt_iff (lt_of_le_of_ne (norm_nonneg _) (λ h, hf' (norm_eq_zero.mp h.symm)))).mpr,
        exact sq (∥f.derivative.eval t₀∥) ▸ ht₀ },
      { split,
        { rw [pow_zero, one_mul, sub_right_comm, sub_self, zero_sub, norm_neg],
          exact le_of_eq (disc.divide.norm h) },
        { rw [pow_one], exact h' } } } },
  { rcases ih with ⟨h₁, h₂, h₃, h₄⟩,
    have : ∥f.eval (seq f t₀ (n + 1))∥ ≤ ∥f.eval t₀∥ :=
      le_trans h₄ (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one (n+1)
        (zero_le_κ f t₀) (le_of_lt (κ_lt_one f t₀ ht₀)))),
    have h : ∥f.eval (seq f t₀ (n+1))∥ ≤ ∥f.derivative.eval (seq f t₀ (n+1))∥ :=
      h₂.symm ▸ le_trans this (le_trans (le_of_lt ht₀) (sq_le (norm_nonneg _) (disc.norm_le_one _))),
    have hfn' : f.derivative.eval (seq f t₀ (n+1)) ≠ 0,
    { intro h, rw [h, norm_zero] at h₂,
      exact absurd (norm_eq_zero.mp h₂.symm) hf' },
    have h' : ∥f.eval (seq f t₀ (n+1) - disc.divide h)∥ ≤ κ f t₀ * ∥f.eval (seq f t₀ (n+1))∥,
    { cases taylor₂ f (seq f t₀ (n+1)) with g hg,
      rw [hg ((seq f t₀ (n+1)) - disc.divide h), sub_right_comm, sub_self, zero_sub,
        neg_mul, disc.divide.mul_cancel h hfn', add_neg_self, zero_add, disc.norm_mul],
      apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (disc.norm_le_one _)),
      rw [disc.norm_pow, norm_neg, disc.divide.norm, h₂, div_pow, sq, mul_div_assoc, mul_comm],
      exact mul_mono_nonneg (norm_nonneg _) (div_le_div_of_le (sq_nonneg _) this) },
    rw [seq.def_succ h],
    split,
    { exact h' },
    { split,
      { rw [←h₂, ←norm_neg (f.derivative.eval (seq f t₀ (n+1)))],
        apply nonarchimedean.eq_norm_of_ne_max,
        cases taylor₁ f.derivative (seq f t₀ (n+1)) with g hg,
        conv_lhs { rw [hg (seq f t₀ (n+1) - disc.divide h), add_right_comm, add_neg_self,
          zero_add, sub_right_comm, sub_self, zero_sub] },
        apply ne_of_lt,
        refine lt_of_lt_of_le _ (le_max_right _ _),
        rw [disc.norm_mul],
        apply lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (disc.norm_le_one _)),
        rw [norm_neg, norm_neg, disc.divide.norm],
        apply (div_lt_iff (lt_of_le_of_ne (norm_nonneg _) (λ h, hfn' (norm_eq_zero.mp h.symm)))).mpr,
        rw [←sq, h₂], exact lt_of_le_of_lt this ht₀ },
      { split,
        { rw [sub_right_comm, sub_self, zero_sub, norm_neg, disc.divide.norm, h₂],
          exact div_le_div_of_le (norm_nonneg _) h₄ },
        { apply le_trans h', rw [pow_succ, mul_assoc],
          exact mul_le_mul_of_nonneg_left h₄ (zero_le_κ f t₀) } } } }
end

/-- Hensel's Lemma: In a complete nonarchimedean field `𝕜`, given any polynomial `f` with coefficients in
  `disc 𝕜` and a point `t₀ : disc 𝕜` such that `∥f(t₀)∥ < ∥f'(t₀)∥²`, there exists a unique point `t : disc 𝕜`
  such that `f(t) = 0` and `∥t - t₀∥ < ∥f'(t₀)∥`. This point `t` also satisfies `∥f'(t)∥ = ∥f'(t₀)∥` and
  `∥t - t₀∥ = ∥f(t₀)∥ / ∥f'(t₀)∥`. -/
theorem hensels_lemma [cau_seq.is_complete 𝕜 norm] : ∃ t, f.eval t = 0 ∧ ∥t - t₀∥ < ∥f.derivative.eval t₀∥ ∧
  ∥f.derivative.eval t∥ = ∥f.derivative.eval t₀∥ ∧ ∥t - t₀∥ = ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥ ∧
  ∀ s, f.eval s = 0 → ∥s - t₀∥ < ∥f.derivative.eval t₀∥ → s = t :=
begin
  have hf' : 0 < ∥f.derivative.eval t₀∥ := lt_of_le_of_lt (norm_nonneg (f.eval t₀))
    (lt_of_lt_of_le ht₀ (sq_le (norm_nonneg _) (disc.norm_le_one _))),
  have hcau : is_cau_seq norm (seq f t₀),
  { apply nonarchimedean.cau.mpr,
    { intros ε hε,
      cases exists_pow_lt_of_lt_one (mul_pos hε hf') (κ_lt_one f t₀ ht₀) with i hi,
      use i, intros j hj,
      apply lt_of_le_of_lt (seq_properties f t₀ ht₀ j).2.2.1,
      apply (div_lt_iff hf').mpr,
      apply lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg (zero_le_κ f t₀) j) (disc.norm_le_one _)),
      exact lt_of_le_of_lt (pow_le_pow_of_le_one (zero_le_κ f t₀) (le_of_lt (κ_lt_one f t₀ ht₀)) hj) hi },
    { exact disc.disc_nonarchimedean 𝕜 } },
  let t : disc 𝕜 := cau_seq.lim ⟨seq f t₀, hcau⟩,
  use t,
  have hzero : f.eval t = 0,
  { rw [polynomial_comp_lim],
    apply cau_seq.lim_eq_of_equiv_const,
    intros ε hε,
    by_cases h : f.eval t₀ = 0,
    { use 0, intros j hj,
      simp only [cau_seq.const_zero, sub_zero, polynomial_comp, cau_seq.mk_to_fun],
      have : 0 = ∥f.eval (seq f t₀ j)∥,
      { apply le_antisymm (norm_nonneg _),
        cases j,
        { rw [seq.def_zero, h, norm_zero] },
        { apply le_trans (seq_properties f t₀ ht₀ j).2.2.2,
          rw [h, norm_zero, mul_zero] } },
      exact this ▸ hε },
    { have : 0 < ∥f.eval t₀∥ := lt_of_le_of_ne (norm_nonneg _) (λ h', h (norm_eq_zero.mp h'.symm)),
      cases exists_pow_lt_of_lt_one (div_pos hε this) (κ_lt_one f t₀ ht₀) with n hn,
      use n, intros j hj,
      simp only [cau_seq.const_zero, sub_zero, polynomial_comp, cau_seq.mk_to_fun],
      cases j,
      { have := (lt_div_iff this).mp hn,
        rw [le_zero_iff.mp hj, pow_zero, one_mul] at this,
        exact this },
      { apply lt_of_le_of_lt (seq_properties f t₀ ht₀ j).2.2.2,
        exact (lt_div_iff (this)).mp (lt_of_le_of_lt (pow_le_pow_of_le_one
          (zero_le_κ f t₀) (le_of_lt (κ_lt_one f t₀ ht₀)) hj) hn) } } },
  have heq : ∥t - t₀∥ = ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥,
  { have heq : ∀ n : ℕ, ∥seq f t₀ (n+1) - t₀∥ = ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥,
    { intro n, induction n with n ih,
      { change ∥seq f t₀ 1 - seq f t₀ 0∥ = _,
        have h : ∥f.eval (seq f t₀ 0)∥ ≤ ∥f.derivative.eval (seq f t₀ 0)∥ :=
          le_of_lt (lt_of_lt_of_le ht₀ (sq_le (norm_nonneg _) (disc.norm_le_one _))),
        rw [seq.def_succ h, sub_right_comm, sub_self, zero_sub,
          norm_neg, disc.divide.norm h], refl },
      { by_cases h : f.eval t₀ = 0,
        { rw [h, norm_zero, zero_div],
          refine le_antisymm _ (norm_nonneg _),
          have := nonarchimedean.nonarch (seq f t₀ (n+1+1) - seq f t₀ (n+1)) (seq f t₀ (n+1) - seq f t₀ 0),
          rw [add_sub, sub_add_cancel] at this,
          apply le_trans this, apply max_le,
          { have := (seq_properties f t₀ ht₀ (n+1)).2.2.1,
            rw [h, norm_zero, mul_zero, zero_div] at this,
            exact this },
          { rw [seq.def_zero, ih, h, norm_zero, zero_div] } },
        { have h'' : ∥seq f t₀ (n+1+1) - seq f t₀ (n+1)∥ < ∥seq f t₀ (n+1) - t₀∥,
          { rw [ih],
            apply lt_of_le_of_lt (seq_properties f t₀ ht₀ (n+1)).2.2.1,
            apply div_lt_div_of_lt hf',
            exact (mul_lt_iff_lt_one_left (lt_of_le_of_ne (norm_nonneg _) (λ h',
              h (norm_eq_zero.mp h'.symm)))).mpr (pow_lt_one (zero_le_κ f t₀)
              (κ_lt_one f t₀ ht₀) (nat.succ_ne_zero n)) },
          have := nonarchimedean.eq_max_of_ne_norm (ne_of_lt h''),
          rw [max_eq_right_of_lt h'', ih, add_sub, sub_add_cancel] at this,
          exact this } } },
    have : t - t₀ = cau_seq.lim (⟨seq f t₀, hcau⟩ - cau_seq.const norm t₀),
    { have : ∀ s t : cau_seq (disc 𝕜) norm, s - t = s + -t,
      { intros s t, apply cau_seq.ext, intro n,
        rw [cau_seq.sub_apply, cau_seq.add_apply, cau_seq.neg_apply, sub_eq_add_neg] },
      rw [this ⟨seq f t₀, hcau⟩ (cau_seq.const norm t₀), ←cau_seq.lim_add, cau_seq.lim_neg,
        cau_seq.lim_const, sub_eq_add_neg] },
    rw [this, norm_comp_lim],
    apply cau_seq.lim_eq_of_equiv_const,
    intros ε hε, use 1, intros j hj,
    rw [cau_seq.sub_apply, cau_seq.const_apply],
    have : (norm_comp (⟨seq f t₀, hcau⟩ - cau_seq.const norm t₀)) j = ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥,
    { cases j,
      { exact absurd hj (not_le.mpr zero_lt_one) },
      { exact heq j ▸ rfl } },
    rw [this, sub_self, norm_zero], exact hε },
  have hlt : ∥t - t₀∥ < ∥f.derivative.eval t₀∥,
  { rw [heq], apply (div_lt_iff hf').mpr, rw [←sq], exact ht₀ },
  have hder : ∥f.derivative.eval t∥ = ∥f.derivative.eval t₀∥,
  { rw [polynomial_comp_lim, norm_comp_lim],
    apply cau_seq.lim_eq_of_equiv_const,
    intros ε hε,
    use 0, intros j hj,
    simp only [cau_seq.sub_apply, cau_seq.const_apply],
    have : (norm_comp (polynomial_comp f.derivative ⟨seq f t₀, hcau⟩)) j = ∥f.derivative.eval t₀∥,
    { cases j,
      { refl },
      { exact (seq_properties f t₀ ht₀ j).2.1 ▸ rfl } },
    rw [this, sub_self, norm_zero], exact hε },
  refine ⟨hzero, hlt, hder, heq, _⟩,
  -- Uniqueness
  intros s hs₁ hs₂,
  apply classical.by_contradiction, intro hst,
  have := nonarchimedean.nonarch_sub (s - t₀) (t - t₀),
  rw [sub_sub_sub_cancel_right] at this,
  apply absurd (lt_of_le_of_lt this (max_lt hs₂ hlt)),
  apply not_lt_of_le,
  cases taylor₂ f t with g hg,
  have h := hg s,
  rw [hzero, hs₁, zero_add] at h,
  have h := congr_arg norm (eq_neg_of_add_eq_zero h.symm),
  rw [norm_neg, disc.norm_mul, disc.norm_mul] at h,
  have : ∥(s - t) ^ 2∥ * ∥g.eval s∥ ≤ ∥(s - t) ^ 2∥ :=
    mul_le_of_le_one_right (norm_nonneg _) (disc.norm_le_one _),
  rw [←h, disc.norm_pow, sq, hder] at this,
  exact (mul_le_mul_left (lt_of_le_of_ne (norm_nonneg _)
    (λ h, sub_ne_zero.mpr hst (norm_eq_zero.mp h.symm)))).mp this
end

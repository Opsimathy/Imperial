
import analysis.normed.normed_field
import data.polynomial.taylor
import topology.metric_space.cau_seq_filter
import topology.algebra.polynomial

section nonarchimedean
  variables (𝕜 : Type) [normed_group 𝕜]

  /-- A type with a normed group structure is nonarchimedean if it satisfies `∥x + y∥ ≤ max ∥x∥ ∥y∥`. -/
  class nonarchimedean :=
  (nonarch : ∀ x y : 𝕜, ∥x + y∥ ≤ max (∥x∥) (∥y∥))

  variables {𝕜} [nonarchimedean 𝕜]

  /-- The nonarchimedean inequality with addition replaced with subtraction. -/
  theorem nonarchimedean.nonarch_sub (x y : 𝕜) : ∥x - y∥ ≤ max (∥x∥) (∥y∥) :=
    (sub_eq_add_neg x y).symm ▸ norm_neg y ▸ nonarchimedean.nonarch x (-y)

  /-- The nonarchimedean inequality is equal if the elements being added have different norms. -/
  theorem nonarchimedean.eq_max_of_ne_norm {x y : 𝕜} (h : ∥x∥ ≠ ∥y∥) :
    ∥x + y∥ = max (∥x∥) (∥y∥) :=
  begin
    have : ∀ {x y : 𝕜}, ∥x∥ > ∥y∥ → ∥x + y∥ = max (∥x∥) (∥y∥),
    { intros x y h,
      rw [max_eq_left_of_lt h],
      have := nonarchimedean.nonarch_sub (x + y) y,
      rw [←(eq_sub_of_add_eq rfl : x = x + y - y)] at this,
      apply le_antisymm (max_eq_left_of_lt h ▸ nonarchimedean.nonarch x y : ∥x + y∥ ≤ ∥x∥),
      cases le_max_iff.mp this with h' h',
      { exact h' },
      { exact absurd h' (not_le.mpr h) } },
    cases h.lt_or_lt with h h,
    { rw [add_comm, max_comm], exact this h },
    { exact this h }
  end

  /-- If the nonarchimedean inequality is not equal, the elements being added have the same norm. -/
  theorem nonarchimedean.eq_norm_of_ne_max {x y : 𝕜} (h : ∥x + y∥ ≠ max (∥x∥) (∥y∥)) :
    ∥x∥ = ∥y∥ := of_not_not (mt nonarchimedean.eq_max_of_ne_norm h)

  /-- A `ℕ`-indexed sequence in a nonarchimedean normed ring is Cauchy iff the difference
    of its consecutive terms tends to `0`. -/
  theorem nonarchimedean.cau {𝕜} [normed_ring 𝕜] [nonarchimedean 𝕜] {s : ℕ → 𝕜} :
    is_cau_seq norm s ↔ ∀ ε > 0, ∃ i, ∀ j ≥ i, ∥s (j + 1) - s j∥ < ε :=
  begin
    apply forall₂_congr, intros ε hε,
    split,
    { rintro ⟨i, hi⟩, use i, intros j hj,
      exact sub_add_sub_cancel (s (j + 1)) (s i) (s j) ▸ neg_sub (s j) (s i) ▸
        lt_of_le_of_lt (nonarchimedean.nonarch (s (j + 1) - s i) (-(s j - s i)))
        (max_lt (hi (j + 1) (le_add_right hj)) ((norm_neg (s j - s i)).symm ▸ hi j hj)) },
    { rintro ⟨i, hi⟩, use i, intros j hj,
      cases le_iff_exists_add.mp hj with k hk,
      induction k with k ih generalizing j,
      { rw [(add_zero i ▸ hk : j = i), sub_self, norm_zero], exact hε },
      { exact hk.symm ▸ (sub_add_sub_cancel (s (i + k + 1)) (s (i + k)) (s i)) ▸
          lt_of_le_of_lt (nonarchimedean.nonarch (s (i + k + 1) - s (i + k)) (s (i + k) - s i))
          (max_lt (hi (i + k) le_self_add) (ih (i + k) le_self_add rfl)) } }
  end
end nonarchimedean

section
  variables (𝕜 : Type) [normed_field 𝕜] [nonarchimedean 𝕜]

  /-- The closed unit ball in the nonarchimedean normed field `𝕜`. -/
  def disc : subring 𝕜 := {
    carrier   := {x | ∥x∥ ≤ 1},
    mul_mem'  := λ x y hx hy, (norm_mul_le x y).trans (one_mul (1 : ℝ) ▸
      mul_le_mul hx hy (norm_nonneg y) zero_le_one),
    one_mem'  := norm_one.le,
    add_mem'  := λ x y hx hy, (nonarchimedean.nonarch x y).trans (max_le hx hy),
    zero_mem' := norm_zero.le.trans zero_le_one,
    neg_mem'  := λ x hx, ((norm_neg x).symm ▸ hx : ∥-x∥ ≤ 1)
  }

  namespace disc
    /-- `disc 𝕜` inherits the norm of `𝕜`. -/
    instance disc_normed_ring : normed_ring (disc 𝕜) := {
      norm := norm ∘ subtype.val,
      dist_eq := λ x y, normed_field.dist_eq x.1 y.1 ▸ rfl,
      norm_mul := λ x y, le_of_eq (norm_mul x.1 y.1)
    }

    section
      variable {𝕜}

      /-- The norm of `disc 𝕜` equals the norm of the inclusion into `𝕜`. -/
      theorem norm_def (x : disc 𝕜) : ∥x∥ = ∥x.1∥ := rfl

      /-- All elements in `disc 𝕜` have norm less than or equal to `1`. -/
      theorem norm_le_one (x : disc 𝕜) : ∥x∥ ≤ 1 := x.2

      /-- The norm in `disc 𝕜` preserves multiplication. -/
      protected theorem norm_mul (x y : disc 𝕜) : ∥x * y∥ = ∥x∥ * ∥y∥ :=
        norm_mul x.1 y.1

      /-- The norm in `disc 𝕜` preserves exponentiation. -/
      protected theorem norm_pow (x : disc 𝕜) (n : ℕ) : ∥x ^ n∥ = ∥x∥ ^ n :=
        norm_pow x.1 n

      /-- Sequences with all elements having norm `≤ 1` are Cauchy in `𝕜` if and only if they are Cauchy in `disc 𝕜`. -/
      theorem disc_is_cau_seq_iff (s : ℕ → 𝕜) (hs : ∀ n, ∥s n∥ ≤ 1) :
        is_cau_seq norm s ↔ is_cau_seq norm (λ n, ⟨s n, hs n⟩ : ℕ → disc 𝕜) := iff.rfl

      /-- The injection of any Cauchy sequence in `disc 𝕜` into `𝕜` is also a Cauchy sequence. -/
      theorem disc_is_cau_seq {s : ℕ → disc 𝕜} (h : is_cau_seq norm s) : is_cau_seq norm (λ n, (s n).1) :=
        (disc_is_cau_seq_iff (λ n, (s n).1) (λ n, (s n).2)).mpr h

      variables {x y : disc 𝕜} (h : ∥x∥ ≤ ∥y∥)
      include h

      /-- `disc 𝕜` inherits division from `𝕜`, so long as the denominator has at least the numerator's norm. -/
      def divide : disc 𝕜 := ⟨x.1 / y.1,
      begin
        change ∥_∥ ≤ 1,
        rw [norm_div, ←norm_def x, ←norm_def y],
        by_cases hy : ∥y∥ = 0,
        { rw [hy, div_zero], exact zero_le_one },
        { exact (div_le_one (lt_of_le_of_ne (norm_nonneg y) (ne.symm hy))).mpr h }
      end⟩

      /-- The norm in `disc 𝕜` preserves division. -/
      theorem divide.norm : ∥divide h∥ = ∥x∥ / ∥y∥ :=
        norm_div x.1 y.1

      /-- If the denominator `y` is non-zero, multiplying `divide h` by `y` cancels the division, leaving the numerator `x`. -/
      theorem divide.mul_cancel (hy : y ≠ 0) : divide h * y = x :=
        subtype.val_inj.mp (div_mul_cancel x.1 (mt subtype.val_inj.mp hy : y.1 ≠ (0 : disc 𝕜).val))
    end

    /-- `disc 𝕜` inherits the nonarchimedean inequality from `𝕜`. -/
    instance disc_nonarchimedean : nonarchimedean (disc 𝕜) :=
      ⟨λ x y, (norm_def (x + y)).symm ▸ nonarchimedean.nonarch x.1 y.1⟩

    /-- The norm in `disc 𝕜` is an absolute value, thanks to properties inherited from the normed field `𝕜`. -/
    instance disc_norm_is_absolute_value : is_absolute_value (norm : disc 𝕜 → ℝ) := {
      abv_nonneg  := norm_nonneg,
      abv_eq_zero := λ _, norm_eq_zero,
      abv_add     := λ x y, (normed_field.is_absolute_value.abv_add : ∀ x y : 𝕜, ∥x + y∥ ≤ ∥x∥ + ∥y∥) x y,
      abv_mul     := disc.norm_mul,
    }

    /-- `disc 𝕜` inherits the completeness of `𝕜`, i.e. if all Cauchy sequences in `𝕜` are convergent,
      then so are all Cauchy sequences in `disc 𝕜`. -/
    instance disc_is_complete [cau_seq.is_complete 𝕜 norm] : cau_seq.is_complete (disc 𝕜) norm := ⟨λ s,
      begin
        let s' : cau_seq 𝕜 norm := ⟨λ n, (s n).1, s.2⟩,
        use s'.lim,
        { cases s'.equiv_lim 1 zero_lt_one with n hn,
          rw [←sub_add_cancel s'.lim (s' n)],
          apply le_trans (nonarchimedean.nonarch (s'.lim - s' n) (s' n)),
          have : ∥s' n - cau_seq.const norm s'.lim n∥ = ∥s'.lim - s' n∥,
          { rw [←norm_neg, neg_sub, cau_seq.const_apply] },
          exact max_le (this ▸ le_of_lt (hn n (le_refl n))) (s n).2 },
        { exact s'.equiv_lim }
      end⟩
  end disc
end

section taylor
  open polynomial
  variables {R : Type} [comm_ring R]

  /-- Any term of a polynomial sum can be removed and added separately so long as zero terms
    do not contribute to the sum. -/
  theorem polynomial.sum_term (n : ℕ) (f : polynomial R) (fn : ℕ → R → polynomial R) (h : ∀ k, fn k 0 = 0) :
    f.sum fn = fn n (f.coeff n) + (f.erase n).sum fn :=
  begin
    rw [sum_def, sum_def, support_erase],
    by_cases hn : n ∈ f.support,
    { rw [←finset.add_sum_erase f.support (λ n, fn n (f.coeff n)) hn],
      apply congr_arg, apply finset.sum_congr rfl, intros x hx,
      rw [erase_ne f n x (finset.ne_of_mem_erase hx)] },
    { rw [not_mem_support_iff.mp hn, h n, zero_add],
      exact eq.symm (finset.sum_congr (finset.erase_eq_of_not_mem hn)
        (λ x hx, congr_arg _ (erase_ne f n x (λ h, absurd (h ▸ hx : n ∈ f.support) hn)))) }
  end

  /-- Any polynomial `f` can be approximated as a quadratic polynomial centred on a chosen point `t₀`. -/
  theorem taylor₂ (f : polynomial R) (t₀ : R) : ∃ err : polynomial R, ∀ t,
    f.eval t = f.eval t₀ + (t - t₀) * f.derivative.eval t₀ + (t - t₀)^2 * err.eval t :=
  begin
    use (((taylor t₀ f).erase 0).erase 1).sum (λ i a, C a * (X - C t₀) ^ (i - 2)), intro t,
    have : ∀ n, C 0 * (X - C t₀) ^ n = 0, { intro n, rw [C_0, zero_mul] },
    conv_lhs { rw [←f.sum_taylor_eq t₀, (taylor t₀ f).sum_term 0 (λ i a, C a * (X - C t₀) ^ i) this,
      ((taylor t₀ f).erase 0).sum_term 1 (λ i a, C a * (X - C t₀) ^ i) this, taylor_coeff_zero,
      erase_ne (taylor t₀ f) 0 1 nat.one_ne_zero, taylor_coeff_one], simp only,
      rw [pow_zero, mul_one, pow_one, ←add_assoc, mul_comm, eval_add, eval_add,
        eval_C, eval_mul, eval_sub, eval_X, eval_C, eval_C] },
    apply congr_arg,
    have : (t - t₀)^2 = ((X - C t₀) ^ 2).eval t := by rw [eval_pow, eval_sub, eval_X, eval_C],
    rw [this, ←eval_mul], apply congr_arg,
    rw [sum_def, sum_def, finset.mul_sum, finset.sum_congr rfl],
    intros n hn,
    conv_rhs { rw [mul_comm, mul_assoc, ←pow_add], },
    have : 2 ≤ n,
    { cases n with n,
      { exfalso, rw [support_erase, support_erase, finset.erase_right_comm] at hn,
        exact absurd rfl (finset.ne_of_mem_erase hn) },
      { cases n with n, { rw [support_erase] at hn, exact absurd rfl (finset.ne_of_mem_erase hn) },
        { simp only [succ_order.succ_le_succ_iff, zero_le'] } } },
    rw [nat.sub_add_cancel this]
  end

  /-- Any polynomial `f` can be approximated as a linear polynomial centred on a chosen point `t₀`. -/
  theorem taylor₁ (f : polynomial R) (t₀ : R) : ∃ err : polynomial R, ∀ t,
    f.eval t = f.eval t₀ + (t - t₀) * err.eval t :=
  begin
    cases taylor₂ f t₀ with err h,
    use C (f.derivative.eval t₀) + (X - C t₀) * err, intro t,
    rw [h t, eval_add, eval_C, mul_add, ←add_assoc, eval_mul,
      eval_sub, eval_X, eval_C, ←mul_assoc, sq]
  end

end taylor

section
  variables {R : Type} [normed_ring R] [is_absolute_value (norm : R → ℝ)]

  /-- A filter-wise Cauchy sequence is an absolute-value-wise Cauchy sequence.
    (This already exists in `topology.metric_space.cau_seq_filter`, but only for normed fields,
    here it is restated for normed rings whose norm is an absolute value). -/
  theorem cauchy_seq.is_cau_seq' {f : ℕ → R} (hf : cauchy_seq f) :
    is_cau_seq norm f :=
  begin
    cases cauchy_iff.1 hf with hf1 hf2,
    intros ε hε,
    rcases hf2 {x | dist x.1 x.2 < ε} (metric.dist_mem_uniformity hε) with ⟨t, ⟨ht, htsub⟩⟩,
    simp at ht, cases ht with N hN,
    existsi N,
    intros j hj,
    rw ←dist_eq_norm,
    apply @htsub (f j, f N),
    apply set.mk_mem_prod; solve_by_elim [le_refl]
  end

  variable [cau_seq.is_complete R norm]

  /-- A Cauchy sequence formed by composing a Cauchy sequence with a polynomial. -/
  noncomputable def polynomial_comp (f : polynomial R) (s : cau_seq R norm) : cau_seq R norm :=
    ⟨λ n, f.eval (s n), ((f.continuous.tendsto s.lim).comp s.tendsto_limit).cauchy_seq.is_cau_seq'⟩

  /-- The composition of a polynomial with a Cauchy sequence's limit equals the limit of the
    composition of the polynomial with the Cauchy sequence. -/
  theorem polynomial_comp_lim (f : polynomial R) (s : cau_seq R norm) : f.eval s.lim = (polynomial_comp f s).lim :=
    tendsto_nhds_unique ((f.continuous.tendsto s.lim).comp s.tendsto_limit) (polynomial_comp f s).tendsto_limit

  /-- A Cauchy sequence formed by composing a Cauchy sequence with the norm. -/
  noncomputable def norm_comp (s : cau_seq R norm) : cau_seq ℝ norm :=
    ⟨λ n, ∥s n∥, ((continuous_norm.tendsto s.lim).comp s.tendsto_limit).cauchy_seq.is_cau_seq'⟩

  /-- The composition of the norm with a Cauchy sequence's limit equals the limit of the
    composition of the norm with the Cauchy sequence. -/
  theorem norm_comp_lim (s : cau_seq R norm) : ∥s.lim∥ = (norm_comp s).lim :=
    tendsto_nhds_unique ((continuous_norm.tendsto s.lim).comp s.tendsto_limit) (norm_comp s).tendsto_limit
end

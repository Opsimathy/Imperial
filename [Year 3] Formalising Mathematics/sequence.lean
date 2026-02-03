
import tactic          -- Imports all the Lean tactics.
import data.real.basic -- Imports the real numbers.

namespace my_analysis

  /-- Sequence of real numbers indexed by natural numbers. -/
  def seq := ℕ → ℝ

  /-- Sequence formed by taking the absolute value of each term. -/
  noncomputable def seq.abs (s : seq) : seq := λ k, |s k|
  @[simp] theorem seq_abs_eq (s : seq) (n : ℕ) : s.abs n = |s n| := rfl

  /-- Set containing all the values taken by terms of the sequence `s`. -/
  def seq.to_set (s : seq) : set ℝ := {x | ∃ n, s n = x}
  /-- Proof that the image set of sequence indexed by ℕ is nonempty. -/
  def seq.nonempty (s : seq) : s.to_set.nonempty :=
    by { use s 0, use 0 }

  /-- Proposition that a sequence converges to a specified limit. -/
  def tendsto (s : seq) (x : ℝ) : Prop := ∀ ⦃ε⦄, 0 < ε → ∃ B : ℕ, ∀ ⦃n⦄, B ≤ n → |s n - x| < ε
  notation s ` ⟶ ` limit := tendsto s limit

  /-- Proposition that there is a limit to which a sequence converges. -/
  def seq.convergent (s : seq) : Prop := ∃ x, s ⟶ x

  section neg

    /-- Sequence formed by taking the additive inverse of each real term of the original sequence `s`. -/
    def seq.neg (s : seq) : seq := λ n, - s n

    instance seq_neg : has_neg seq := ⟨seq.neg⟩
    @[simp] theorem seq.neg_eq (s : seq) (n : ℕ) : (-s) n = -(s n) := rfl

    /-- Sequence negation is an involution, i.e. it is its own inverse. -/
    @[simp] theorem seq.neg_neg (s : seq) : -(-s) = s :=
    begin
      apply funext, intro n,
      rw [seq.neg_eq, seq.neg_eq, neg_neg]
    end 

    /-- tendsto is preserved by negating both the sequence and its limit. -/
    theorem neg_tendsto_neg {s : seq} {x : ℝ} : (-s ⟶ -x) ↔ (s ⟶ x) :=
    begin
      split,
      { intros h ε hε, cases h hε with B hB, use B, intros n hn,
        rw [← abs_neg, neg_sub, ← neg_sub_neg, ← s.neg_eq],
        exact hB hn },
      { intros h ε hε, cases h hε with B hB, use B, intros n hn,
        rw [s.neg_eq, ← neg_sub, abs_neg, neg_sub_neg],
        exact hB hn }
    end

    /-- tendsto is preserved by swapping the negation between the sequence and limit. -/
    theorem neg_tendsto {s : seq} {x : ℝ} : (-s ⟶ x) ↔ (s ⟶ -x) :=
    begin
      have : x = - -x, from eq_neg_of_eq_neg rfl,
      conv_lhs { rw [this] },
      exact neg_tendsto_neg
    end

    /-- Negation preserves convergence. -/
    theorem neg_convergent {s : seq} : (-s).convergent ↔ s.convergent :=
    begin
      split,
      { intro h, cases h with x hx,
        exact ⟨-x, neg_tendsto.mp hx⟩ },
      { intro h, cases h with x hx,
        exact ⟨-x, neg_tendsto_neg.mpr hx⟩ }
    end

  end neg

  section bounded

    /-- Proposition that a sequence is bounded above, i.e. all terms lie within `(-∞, M]`. -/
    def seq.bounded_above (s : seq) : Prop := ∃ M, ∀ n, s n ≤ M

    /-- Proposition that a sequence is bounded above, i.e. all terms lie within `[m, ∞)`. -/
    def seq.bounded_below (s : seq) : Prop := ∃ m, ∀ n, m ≤ s n

    /-- Proposition that a sequence is bounded above and below, i.e. all terms lie within `[-M, M]`. -/
    def seq.bounded (s : seq) : Prop := s.abs.bounded_above

    /-- Proof that a sequence is bounded in absolute value if and only if it is bounded both above and below. -/
    theorem bounded_iff_above_below {s : seq} : s.bounded ↔ s.bounded_above ∧ s.bounded_below :=
    begin
      split,
      { intro hb,
        cases hb with M hM,
        split,
        { use M, intro n,
          exact le_of_abs_le (hM n) },
        { use -M, intro n,
          exact neg_le_of_abs_le (hM n) } },
      { rintro ⟨ha, hb⟩,
        cases ha with M hM,
        cases hb with m hm,
        use max M (-m), intro n,
        by_cases h : s n ≤ 0,
        { rw [seq_abs_eq, abs_of_nonpos h],
          exact le_max_of_le_right (neg_le_neg (hm n)) },
        { rw [seq_abs_eq, abs_of_nonneg (le_of_not_ge h)],
          exact le_max_of_le_left (hM n) }}
    end

    /-- Cast from myanalysis.bounded_above to mathlib's bdd_above Prop. -/
    theorem seq.bounded_above.to_bdd_above {s : seq} (hb : s.bounded_above) : bdd_above s.to_set :=
    begin
      cases hb with M hM,
      use M, intros x hx,
      cases hx with n hn,
      rw [← hn], exact hM n
    end

    /-- Negation turn an upper bound into a lower bound. -/
    theorem bounded_above_iff_neg_below {s : seq} : s.bounded_above ↔ (-s).bounded_below :=
    begin
      split,
      { intro h, cases h with M hM,
        use -M, intro n, rw [seq.neg_eq],
        exact neg_le_neg_iff.mpr (hM n) },
      { intro h, cases h with m hm,
        use -m, intro n, rw [←s.neg_neg, (-s).neg_eq],
        exact neg_le_neg_iff.mpr (hm n) }
    end

    /-- Negation turn an lower bound into a upper bound. -/
    theorem bounded_below_iff_neg_above {s : seq} : s.bounded_below ↔ (-s).bounded_above :=
    begin
      conv_lhs { rw [←seq.neg_neg s] },
      exact bounded_above_iff_neg_below.symm
    end

  end bounded

  section order

    /-- Proposition that every term in a sequence is greater than or equal to any term before it. -/
    def seq.increasing (s : seq) : Prop := ∀ ⦃m n⦄, m ≤ n → s m ≤ s n
    /-- Proposition that every term in a sequence is strictly greater than any term before it. -/
    def seq.strictly_increasing (s : seq) : Prop := ∀ ⦃m n⦄, m < n → s m < s n

    /-- Proposition that every term in a sequence is less than or equal to any term before it. -/
    def seq.decreasing (s : seq) : Prop := ∀ ⦃m n⦄, m ≤ n → s n ≤ s m
    /-- Proposition that every term in a sequence is strictly less than any term before it. -/
    def seq.strictly_decreasing (s : seq) : Prop := ∀ ⦃m n⦄, m < n → s n < s m

    /-- Proposition that in a sequence, either every term is greater than or equal to any term before it,
      or every term is less than or equal to any term before it. -/
    def seq.monotone (s : seq) : Prop := s.increasing ∨ s.decreasing
    /-- Proposition that in a sequence, either every term is strictly greater than any term before it,
      or every term is strictly less than any term before it. -/
    def seq.strictly_monotone (s : seq) : Prop := s.strictly_increasing ∨ s.strictly_decreasing

    /-- Weakening of strictly increasing to just increasing. -/
    theorem seq.strictly_increasing.to_increasing {s : seq} (si : s.strictly_increasing) : s.increasing :=
    begin
      intros m n h,
      by_cases h' : m = n,
      { rw [h'] },
      { exact le_of_lt (si (lt_of_le_of_ne h h')) }
    end
    /-- Weakening of strictly increasing to just increasing. -/
    theorem seq.strictly_decreasing.to_decreasing {s : seq} (si : s.strictly_decreasing) : s.decreasing :=
    begin
      intros m n h,
      by_cases h' : m = n,
      { rw [h'] },
      { exact le_of_lt (si (lt_of_le_of_ne h h')) }
    end
    /-- Weakening of strictly increasing to just increasing. -/
    theorem seq.strictly_monotone.to_monotone {s : seq} (si : s.strictly_monotone) : s.monotone :=
    begin
      cases si with h h,
      { exact or.inl h.to_increasing },
      { exact or.inr h.to_decreasing }
    end

    /-- Negation turns an increasing sequence into a decreasing sequence. -/
    theorem increasing_iff_neg_decreasing {s : seq} : s.increasing ↔ (-s).decreasing :=
    begin
      split,
      { intros h a b hab,
        rw [seq.neg_eq, seq.neg_eq],
        exact neg_le_neg (h hab) },
      { intros h a b hab,
        rw [←s.neg_neg, (-s).neg_eq],
        exact neg_le_neg_iff.mpr (h hab) }
    end

    /-- Negation turns an decreasing sequence into a increasing sequence. -/
    theorem decreasing_iff_neg_increasing {s : seq} : s.decreasing ↔ (-s).increasing :=
    begin
      conv_lhs { rw [←seq.neg_neg s] },
      exact increasing_iff_neg_decreasing.symm
    end

    /-- Any increasing bounded-above sequence is convergent. -/
    theorem convergent_of_bounded_above_increasing {s : seq} (hba : s.bounded_above) (hi : s.increasing) :
      s.convergent :=
    begin
      use Sup s.to_set,
      intros ε hε,
      have hlub := real.is_lub_Sup s.to_set s.nonempty hba.to_bdd_above,
      have : ∃ B, s B > Sup s.to_set - ε,
        by_contradiction h,
        simp only [not_exists, not_lt] at h,
        have : Sup s.to_set - ε ∈ upper_bounds s.to_set,
          rintros x ⟨n, rfl⟩,
          exact h n,
        exact absurd hε (not_lt.mpr ((le_sub_self_iff _).mp (hlub.right this))),
      cases this with B hB,
      use B, intros n hn,
      refine abs_lt.mpr ⟨_, _⟩,
      exact lt_tsub_iff_left.mpr (lt_of_lt_of_le hB (hi hn)),
      exact lt_of_le_of_lt (sub_nonpos.mpr (hlub.left (by use n))) hε
    end

    /-- Any decreasing bounded-below sequence is convergent. -/
    theorem convergent_of_bounded_below_decreasing {s : seq} (hbb : s.bounded_below) (hd : s.decreasing) :
      s.convergent :=
        neg_convergent.mp $ convergent_of_bounded_above_increasing
          (bounded_below_iff_neg_above.mp hbb)
          (decreasing_iff_neg_increasing.mp hd)

  end order

  section shift

    /-- Sequence formed by ignoring the first `n` elements, such that `s.shift 0 = s n`. -/
    def seq.shift (s : seq) (n : ℕ) : seq := λ m, s (m + n)

    /-- Shifting by `0` leaves the sequence unchanged. -/
    @[simp] theorem shift_zero (s : seq) : s.shift 0 = s :=
      by simp only [seq.shift, nat.add_zero]

    /-- For any `m` greater than the shift number `n`, `s m` has been moved to `s.shift n (m - n)`. -/
    theorem shift_ge (s : seq) {n m : ℕ} (h : n ≤ m) : s.shift n (m - n) = s m :=
      by simp only [seq.shift, nat.sub_add_cancel h]

    /-- tendsto is preserved by arbitrary finite shifts (including preserving the limit). -/
    theorem tendsto_shift (s : seq) (x : ℝ) : ∀ n, (s ⟶ x) ↔ (s.shift n ⟶ x) :=
    begin
      intro n, split,
      { intros h ε hε,
        cases h hε with B hB,
        use B, intros m hm,
        exact hB (le_add_right hm : B ≤ m + n) },
      { intros h ε hε,
        cases h hε with B hB,
        use B + n, intros m hm,
        rw [← shift_ge s (nat.le_of_add_le_right hm)],
        exact hB (le_tsub_of_add_le_right hm) }
    end

  end shift

  section finite_prefix

    /-- A finite set made up of the values of the first `n` terms of the sequence `s` (from `s 0` to `s (n-1)`). -/
    noncomputable def finite_prefix (s : seq) (n : ℕ) : finset ℝ :=
      (multiset.map s (multiset.range n)).to_finset

    /-- A real number belongs to the finite prefix set if and only if it is the value taken by
      the sequence `s` for some term before the `n`-th term. -/
    @[simp] theorem mem_finite_prefix {s : seq} {n : ℕ} {x : ℝ} : x ∈ finite_prefix s n ↔ ∃ k, k < n ∧ s k = x :=
      by simp only [finite_prefix, multiset.mem_to_finset, multiset.mem_map, multiset.mem_range]

    /-- If the natural number `n` isn't zero, then the finite prefix with `n` elements is nonempty. -/
    theorem finite_prefix_nonempty (s : seq) {n : ℕ} (hn : n ≠ 0) :
      (finite_prefix s n).nonempty :=
        ⟨s 0, mem_finite_prefix.mpr ⟨0, pos_iff_ne_zero.mpr hn, rfl⟩⟩

    /-- For any `n`, the real numbers `|s m|` for `m < n` have a maximal element. -/
    theorem finite_prefix_max (s : seq) {n : ℕ} (hn : n ≠ 0) :
      ∃ m, m < n ∧ ∀ k < n, s k ≤ s m :=
    begin
      let fs := (finite_prefix s n),
      have hM := mem_finite_prefix.mp (fs.max'_mem (finite_prefix_nonempty s hn)),
      cases hM with m hm,
      use m, split, exact hm.left,
      intros k hk, rw [hm.right],
      exact fs.le_max' (s k)(mem_finite_prefix.mpr ⟨k, hk, rfl⟩)
    end

    /-- For any `n`, the real numbers `|s m|` for `m < n` have a minimal element. -/
    theorem finite_prefix_min (s : seq) {n : ℕ} (hn : n ≠ 0) :
      ∃ m, m < n ∧ ∀ k < n, s m ≤ s k :=
    begin
      cases finite_prefix_max (-s) hn with M hM,
      use M, split, exact hM.left,
      intros k hk,
      exact neg_le_neg_iff.mp (hM.right k hk)
    end

    /-- For any `n`, the elements `|s m|` for `m < n` are bounded. -/
    theorem finite_prefix_bounded (s : seq) (n : ℕ) : ∃ M, ∀ m < n, |s m| ≤ M :=
    begin
      by_cases hn : n = 0,
      { use 0,
        intros m hm,
        rw [hn] at hm,
        exact absurd hm (nat.not_lt_zero m) },
      { cases finite_prefix_max s.abs hn with M hM,
        exact ⟨|s M|, hM.right⟩ }
    end

  end finite_prefix

  /-- bounded is preserved by arbitrary finite shifts (although the bound `M` itself might change). -/
  theorem bounded_shift (s : seq) : ∀ n, s.bounded ↔ (s.shift n).bounded :=
  begin
    intro n, split,
    { rintro ⟨M, h⟩,
      use M, intro k,
      exact h (k + n) },
    { rintro ⟨M₁, h₁⟩,
      cases finite_prefix_bounded s n with M₂ h₂,
      use max M₁ M₂,
      intro k,
      by_cases hk : k < n,
      { exact le_max_of_le_right (h₂ k hk) },
      { rw [seq_abs_eq, ← shift_ge s (not_lt.mp hk)],
        exact le_max_of_le_left (h₁ (k - n)) } }
  end

end my_analysis

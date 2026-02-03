
import sequence -- Imports sequences and their properties (convergent, bounded, monotone, etc.).

namespace my_analysis

  section subindex

    /-- A subindex is a strictly increasing map from ℕ to itself. -/
    structure subindex :=
      (φ : ℕ → ℕ)
      (mono : strict_mono φ)

    instance subindex_fun : has_coe_to_fun subindex (λ _, ℕ → ℕ) := ⟨subindex.φ⟩
    @[simp] theorem subindex_fun_eq (si : subindex) (n : ℕ) : si n = si.φ n := rfl

    /-- The strictly increasing property of subindex follows inductively from the
      function having strictly increasing consecutive terms. -/
    def subindex_mk (f : ℕ → ℕ) (h : ∀ n, f n < f n.succ) : subindex :=
      ⟨f, begin
        intros a b hab,
        have : ∀ n, n > 0 → f a < f (a + n),
          intro n,
          induction n with n ih,
          { intro h', exact absurd h' (irrefl 0) },
          { intro h', rw [nat.add_succ],
            by_cases hn : n > 0,
            { exact lt_trans (ih hn) (h (a + n)) },
            { have : n = 0, from nat.eq_zero_of_le_zero (not_lt.mp hn),
              rw [this, add_zero], exact h a } },
        rw [← nat.add_sub_of_le (le_of_lt hab)],
        exact this (b - a) (tsub_pos_of_lt hab)
      end⟩

    /-- A function used for defining subindex structures, such that each
      index is `f` applied to the previous index, beginning with `f 0`. -/
    def subindex_recursive (f : ℕ → ℕ) : ℕ → ℕ
    | 0     := f 0
    | (k+1) := f (subindex_recursive k)

    /-- A subindex formed by moving every index up by `n`. -/
    def subindex.add (si : subindex) (n : ℕ) : subindex :=
      ⟨λ k, si k + n, λ a b hab, (add_lt_add_iff_right n).mpr (si.mono hab)⟩

    /-- The `m`-th entry of a subindex is at least `m`, or in other words
      it will never fall behind the original sequence. -/
    theorem subindex.unbounded (si : subindex) : ∀ m, m ≤ si m
    | 0     := zero_le _
    | (k+1) := nat.succ_le_of_lt $ lt_of_le_of_lt (subindex.unbounded k) $ si.mono (lt_add_one k)

  end subindex

  section subseq

    /-- A sub-sequence, formed by composing a sequence and a subindex. -/
    def seq.subseq (s : seq) (si : subindex) : seq := s ∘ si

    /-- A sub-sequence inherits any upper bounds from the original sequence. -/
    theorem subseq_bounded_above {s : seq} (hb : s.bounded_above) (si : subindex) :
      (s.subseq si).bounded_above :=
    begin
      cases hb with M hM, use M,
      intro n, exact hM (si n)
    end

    /-- A sub-sequence inherits any lower bounds from the original sequence. -/
    theorem subseq_bounded_below {s : seq} (hb : s.bounded_below) (si : subindex) :
      (s.subseq si).bounded_below :=
    begin
      cases hb with m hm, use m,
      intro n, exact hm (si n)
    end

  end subseq

  /-- Every sequence has a monotone sub-sequence. -/
  theorem peak_point_lemma (s : seq) : ∃ si : subindex, (s.subseq si).monotone :=
  begin
    by_cases h : ∀ N, ∃ m, m > N ∧ ∀ n, n > N →  s m ≤ s n,
    -- Increasing case.
    { let sir := subindex_recursive (λ n, classical.some (h n)),
      let si := subindex_mk sir (λ n, (classical.some_spec (h (sir n))).left),
      use si, apply or.inl,
      intros a b hab,
      have : ∀ n, s.subseq si a ≤ s.subseq si (a + n),
        intro n,
        induction n with n ih,
        { rw [add_zero] },
        { apply ih.trans,
          rw [nat.add_succ],
          by_cases han : a + n = 0,
          { rw [han],
            cases classical.some_spec (h 0) with h₁ h₂,
            exact h₂ (classical.some (h (sir 0)))
              (lt_trans h₁ (classical.some_spec (h (sir 0))).left) },
          { cases nat.exists_eq_succ_of_ne_zero han with k hk,
            rw [hk],
            cases classical.some_spec (h (sir k)) with h₁ h₂,
            exact h₂ (classical.some (h (sir k.succ)))
              (lt_trans h₁ (classical.some_spec (h (sir k.succ))).left) } },
      rw [← nat.add_sub_of_le hab],
      exact this (b - a) },
    -- Decreasing case.
    { simp only [not_forall, not_exists, not_and, not_le, gt_iff_lt, exists_prop] at h,
      cases h with N hN,
      have h : ∀ x, ∃ y, x < y ∧ s.shift N.succ y < s.shift N.succ x,
        intro x,
        by_contradiction h,
        simp only [not_exists, not_and, not_lt] at h,
        cases finite_prefix_min (s.shift N.succ) (nat.succ_ne_zero x) with M hM,
        cases hN (M + N.succ) (nat.lt_add_left N N.succ M (lt_add_one N)) with y hy,
        by_cases hxy : x < y - N.succ,
        { have := lt_of_lt_of_le hy.right (hM.right x (lt_add_one x)),
          rw [← shift_ge s hy.left] at this,
          exact absurd (h (y - N.succ) hxy) (not_le_of_lt this) },
        { have := hM.right (y - N.succ) (nat.lt_succ_of_le (le_of_not_lt hxy)),
          rw [shift_ge s hy.left] at this,
          exact absurd this (not_le_of_lt hy.right) },
      let sir := subindex_recursive (λ n, classical.some (h n)),
      let si := (subindex_mk sir (λ n, (classical.some_spec (h (sir n))).left)).add N.succ,
      use si, apply or.inr,
      intros a b hab,
      have : ∀ n, s.subseq si (a + n) ≤ s.subseq si a,
        intro n,
        induction n with n ih,
        { rw [add_zero] },
        { refine le_trans _ ih,
          rw [nat.add_succ],
          exact le_of_lt (classical.some_spec (h (sir (a + n)))).right },
      rw [← nat.add_sub_of_le hab],
      exact this (b - a) }
  end

  /-- Every bounded sequence has a convergent subsequence. -/
  theorem bolzano_weierstrass {s : seq} (hb : s.bounded) :
    ∃ si : subindex, (s.subseq si).convergent :=
  begin
    cases peak_point_lemma s with si hm,
    cases hm with inc dec,
    { exact ⟨si, convergent_of_bounded_above_increasing (subseq_bounded_above
      (bounded_iff_above_below.mp hb).left si) inc⟩ },
    { exact ⟨si, convergent_of_bounded_below_decreasing (subseq_bounded_below
      (bounded_iff_above_below.mp hb).right si) dec⟩ }
  end

end my_analysis

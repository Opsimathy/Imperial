import Theorem1

variables {d : ℕ} {hd: nonsquare d}

/-
# Corollary 2 (Dirichlet)
The main goal of this file is to prove:
S = {(p,q) ∈ ℤ×ℤ ∣ |p-q√d|<1/q } is infinite.
-/

/--|p-qa| is positive. This uses irrational_ne_rational_abs from the previous file. Needed because we will extensively divide by |p-qa| in inequalities.--/
lemma irrational_abs_gt_0 (a:ℝ) (i: irrational a) (p q:ℤ) (h: q ≠ 0): 0 < abs (a-p/q):=
begin
  have j1: (q:ℝ) ≠ 0,
    { norm_cast, assumption },
  cases eq_or_lt_of_le (abs_nonneg (a-p/q)),
  { exfalso, apply irrational_ne_rational_abs a i p q h (0:ℤ) (1:ℤ) (show _,  by simp), 
    apply_fun (has_mul.mul (abs q) ) at h_1, rw mul_zero at h_1, push_cast, rw abs_eq_neg, rw h_1, rw ← abs_mul,
    rw div_one, apply congr_arg, rw mul_sub, simp, field_simp, norm_cast, exact mul_comm p q,
  },
  { assumption }
end

lemma div_of_div (a b c:ℝ) (h: 0 ≠ a) (h1: 0 ≠ b): 1/(a*b) = 1/a/b:= by field_simp

/--To change between |a-p/q| and |p-qa| in equalities--/
lemma div_q_eq (p q :ℤ) (a:ℝ) (h: 1 ≤ q):  abs(a-p/q) = abs((p:ℝ)-(q:ℝ)*a)/q:=
begin
  have h1: (q:ℝ) ≠ 0,
    { norm_cast, linarith, },
  rw eq_div_iff h1,  
  have h2: 0 < (q:ℝ),
    { norm_cast, linarith, },
  nth_rewrite 1 ← abs_of_pos h2,
  rw ← abs_mul,
  rw ← abs_neg,
  rw sub_mul,
  nth_rewrite 0 mul_comm,
  repeat {rw mul_div_assoc},
  field_simp [show (q:ℝ) ≠ 0, begin norm_cast, linarith end],
end

/--The descent lemma: given any (p,q) that satisfies the inequality in Corollary 2 there exists (p',q') such that |p'-q'a|<|p-qa| that also satisfies the inequality of Corollary 2.--/
lemma inf_irrational_approx (a :ℝ) (p q :ℤ ) (h: 1≤ q)(i: irrational a): ∃ (p' q' :ℤ), 1 ≤ q' ∧ abs((p':ℝ)-(q':ℝ)*a)< abs(p-q*a) ∧ abs(a - (p':ℝ)/q') < 1/(q'*q'):=
begin
  cases archimedean_iff_nat_lt.1 (by apply_instance) (1/abs(a - p/q)) with Q' hQ',
  let Q:= max Q' 2,
  have hQ: 1 < Q ∧ (1/abs(a - p/q)) < Q,
    { split, 
    { simp },
    { apply lt_of_lt_of_le hQ', norm_cast, apply le_max_left, }},
  have gQ: 0 < (Q:ℝ),
    { norm_cast, simp },

  cases irrational_approx a i Q hQ.1 with p' q', rcases q' with ⟨q', H1, H2, H3⟩, use p', use q', 
  have h3: 0 < (q':ℝ),
    { norm_cast,  linarith },
  rw ← div_lt_div_right (abs_pos_of_pos h3) at H1, rw ← abs_div at H1, rw ← div_sub' _ _ _ (show (q':ℝ) ≠ 0, begin norm_cast, linarith end) at H1, rw abs_sub_comm at H1,
  rw abs_eq_self.mpr (le_of_lt h3) at H1,
  split,
  { exact H2, },
  { split, 
    { cases hQ with hQ1 hQ2, rw div_lt_iff (irrational_abs_gt_0 a i p q (show q ≠ 0, by linarith)) at hQ2,
      rw ← div_lt_iff' gQ at hQ2, rw div_q_eq _ _ _ h at hQ2, rw lt_div_iff' (show (0:ℝ) < (q:ℝ), begin norm_cast, linarith end) at hQ2,
      apply lt_trans _ hQ2, rw div_q_eq _ _ _ H2 at H1, rw div_lt_iff h3 at H1, apply lt_of_lt_of_le H1,
      have H3: 1 / ↑Q / (q':ℝ) * ↑q' = 1 / ↑Q ,
        { simp [show (q':ℝ) ≠ 0, begin norm_cast, linarith end], },
      rw H3, nth_rewrite 0 ← one_mul (1/(Q:ℝ)), apply mul_le_mul _ (eq.le (show 1/(Q:ℝ) = 1/(Q:ℝ), from rfl )) (one_div_nonneg.mpr(show 0 ≤ (Q:ℝ), by linarith)), 
      all_goals { norm_cast, linarith, }},
    
    { apply lt_trans H1, rw div_lt_iff h3, rw div_lt_iff gQ, 
      have H4: 1<(Q:ℝ)/q',
        { rw lt_div_iff' h3, rw mul_one, norm_cast, assumption, },
      suffices goal: ↑Q / (q':ℝ) = 1 / (↑q' * ↑q') * ↑q' * ↑Q,
        { rw ← goal, exact H4, },
        { field_simp, }
    }}
end 

/--Convert between |p-qa| and |a-p/q| in inequalities.--/
lemma div_q_lt (p q :ℤ) (a b:ℝ) (h: 1 ≤ q): abs((p:ℝ)-(q:ℝ)*a)<b*q ↔ abs(a-p/q) <b:=
begin
  rw div_q_eq _ _ a h,
  have h1: 0 < (q:ℝ),
    { norm_cast, linarith, },
  exact (div_lt_iff h1).symm,
end

/--Define the set S we want to prove is infinite--/
def S (u:ℕ):= {x : ℤ×ℤ | 1≤ x.2 ∧ abs((x.1:ℝ)-(x.2:ℝ)*real.sqrt u)< 1/(x.2:ℝ)}

/--If d is nonsquare natural, then √d is irrational. Needed since our previous results assumes a was irrational.--/
lemma sqrtd_irrational {d : ℕ} (hd: nonsquare (d:ℤ)) : irrational (real.sqrt d):=
begin
  have h1: 0 ≤ (d:ℝ),
    { exact nat.cast_nonneg d, },
  apply irrational_nrt_of_notint_nrt 2 d (show real.sqrt ↑d ^ 2 = ↑↑d, begin simp end) _ (show _, by simp),
  by_contra, cases h with u hu, 
  have h2:= hd u,
  have h3: (d:ℤ) = u*u,
    { apply_fun (λ(x:ℝ), x*x) at hu, rw real.mul_self_sqrt h1 at hu,
    norm_cast at hu, },
  cc,
end

/--Base case: S is nonempty.--/
lemma S_nonempty (hd: nonsquare (d:ℤ)): nonempty ↥ (S d):=
begin
  cases irrational_approx (real.sqrt d) (sqrtd_irrational hd) (2) (show 1<2, by dec_trivial) with p q,
  rcases q with ⟨q, h1, h2, h3⟩,
  have g1: 0 < (q:ℝ),
    { norm_cast, linarith },
  have h4: |↑p - ↑q * real.sqrt ↑d| < 1 / (q:ℝ),
    { apply lt_trans h1, rw one_div_lt_one_div (show 0<((2:ℕ):ℝ), begin norm_cast, dec_trivial end) g1, norm_cast, simp at h3, exact h3 },
  use (p,q), split, 
  { assumption },
  { assumption }
end

/--Corollary 2: S is infinite because of the base case S_nonempty and the descent lemma inf_irrational_approx.--/
theorem S_infinite (hd: nonsquare (d:ℤ)): set.infinite (S d):=
begin
  by_contra,
  rw set.not_infinite at h,
  have h2: ∀ (x:S d), ∃ (u:ℝ), u = abs((x.val.1:ℝ)-(x.val.2:ℝ)*real.sqrt d),
    { intro x, use abs((x.val.1:ℝ)-(x.val.2:ℝ)*real.sqrt d), },
  choose f h3 using h2,
  haveI H:=S_nonempty hd,
  haveI h4: fintype (S d),
    { exact set.finite.fintype h },
  have h5:= fintype.exists_min f,
  cases h5 with x h5,
  rcases inf_irrational_approx (real.sqrt d) x.val.1 x.val.2 (show 1 ≤ x.val.2, begin cases x, cases x_property, assumption end) (sqrtd_irrational hd) with ⟨p, q, g1, g2, g3⟩, 
  have j1: 0 ≠ (q:ℝ), 
    { norm_cast, linarith },
  have h6: (p,q) ∈ S d,
    { split, 
      { assumption, },
      { rw div_of_div _ _ (q:ℝ) j1 j1 at g3, rw ← div_q_lt p q (real.sqrt d) _ g1 at g3, field_simp at g3, apply g3, }},
  have h7:= h5 ⟨ (p,q),h6⟩,
    repeat { rw h3 at h7 },
  have h8:= lt_of_lt_of_le g2 h7,
  simp at h8, assumption,
end


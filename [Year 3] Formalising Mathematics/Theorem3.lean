import Corollary2


/-
# Theorem 3: Existence of Pell solutions
The main goal of this final file is to prove that the equation x^2-dy^2=1 always has a nontrivial integer solution if d is a nonsquare natural number.
-/

variables {d : ℕ} {hd: nonsquare d}

lemma abs_eq_self1 (a:ℝ) (h: 0≤ a): abs a =a :=
begin
  exact abs_eq_self.mpr h,
end

/--Every pair in S has norm bounded by 2√d+1 and -(2√d+1). But S is infinite so there are infinitely many pairs with bounded norm.--/
lemma inf_bounded_pairs (a: (S d)) (hd: nonsquare (d:ℤ)): abs(((⟨a.val.1, a.val.2⟩ : ℤ√d).norm):ℝ)≤ (2:ℝ) *(real.sqrt d)+1:=
begin
  rcases a with ⟨a, a1, a2⟩,
  rw ← eval_eval_conj_norm,
  rw abs_mul, dsimp, 
  have h1: abs ((a.fst:ℝ) + (a.snd:ℝ) * (real.sqrt d))≤ 1/(a.snd:ℝ) +2*(real.sqrt d)* (a.snd),
  { have i1: ↑(a.fst) + ↑(a.snd) * real.sqrt ↑d = ↑(a.fst) - ↑(a.snd) * real.sqrt ↑d + 2*↑(a.snd) * real.sqrt ↑d:=by ring,
    rw i1,
    apply le_trans (abs_add _ _), apply add_le_add (le_of_lt a2), apply le_of_eq, repeat {rw abs_mul}, 
    rw abs_eq_self1 _ (show 0 ≤ (2:ℝ), by linarith), 
    rw abs_eq_self1 _ (show 0 ≤ (a.snd:ℝ), begin norm_cast, linarith end),
    rw abs_eq_self1 _ (real.sqrt_nonneg d),
    ring, },
    apply le_trans (mul_le_mul h1 (le_of_lt a2) (abs_nonneg _) (le_trans (abs_nonneg _) h1)),
    rw add_mul, simp [show (a.snd:ℝ ) ≠ 0, begin norm_cast, linarith end],rw add_comm, 
    apply add_le_add (show 2 * real.sqrt ↑d ≤ 2 * real.sqrt ↑d, by simp), 
    have h2: (0:ℝ) ≤  (↑(a.snd))⁻¹,
      { simp, linarith, },
    have h3: (↑(a.snd))⁻¹ ≤  (1:ℝ),
      { apply inv_le_one, norm_cast, linarith, },
    rw ← mul_one (1:ℝ),
    apply mul_le_mul h3 h3 h2 (show (0:ℝ) ≤ 1, by simp),
end

/--Define A the set of integers between 2√d+1 and -(2√d+1)--/
def A (d:ℕ):= {x: ℤ | abs(x:ℝ) ≤ 2*(real.sqrt d)+1}

/--A is finite. Needed for infinite Pigeonhole (which we formalize below): S infinite, A finite → infinitely many pairs with fixed norm.--/
lemma A_finite (d:ℕ) : set.finite (A d):=
begin
  refine bdd_below.finite_of_bdd_above _ _,
  { use ⌊-(2*(real.sqrt d)+1) ⌋,
    intros x hx,
    have h1:= int.floor_le (-(2*(real.sqrt d)+1)),
    have h2: -(2*(real.sqrt d)+1) ≤ x,
      { exact neg_le_of_abs_le hx, },
    have h3:= le_trans h1 h2,
    simp * at *, },

  { use ⌈(2*(real.sqrt d)+1)⌉,
    intros x hx,
    have h1:= int.le_ceil ((2*(real.sqrt d)+1)),
    have h2:  (x:ℝ) ≤ (2:ℝ)*(real.sqrt d)+(1:ℝ),
      { exact le_of_abs_le hx, },
    have h3:= ge_trans h1 h2,
    norm_cast at h3, exact h3,
  }
end

/--Norm can never be 0 if the 2nd coordinate is ≥ 1.--/
lemma pell_ne_zero (x y:ℤ) (hd: nonsquare d) (H: 1 ≤ y): x^2 -d*y^2 ≠ 0:=
begin
  by_contra,
  have h0:= nat.zero_le d, 
  have h1: y≠ 0,
    { linarith, },
  have h2: (d:ℝ) = (x/y)^2,
    { rw sub_eq_zero at h, field_simp * at *, norm_cast, rw h, },
  have h3: real.sqrt d = abs(x/y),
    { rw ← sq_abs at h2, rw real.sqrt_eq_iff_sq_eq (show 0 ≤ (d:ℝ), begin norm_cast, assumption end) (abs_nonneg _), rw h2, },
  have h4:= sqrtd_irrational hd, 
  rw abs_div at h3, 
  rw irrational_iff_ne_rational at h4,
  have h5:= h4 (abs x) (abs y),
  push_cast at h5,
  rw h3 at h5,
  exact h1 (false.rec (y = 0) (h5 rfl)),
end

/--Theorem 3: If d is nonsquare then Pell's equation always has a nontrivial solution. Nearly done, just some small exercies in rewrites left.--/
theorem exist_pell_solution {d:ℕ} (hd: nonsquare d): ∃ (x y:ℤ), x^2-d*y^2=1 ∧ 1 ≤ y:=
begin
  suffices goal:∃ (x y:ℤ),  (⟨x, y⟩ : ℤ√d).norm = 1 ∧ 1 ≤ y,
    { rcases goal with ⟨x, y, hy, hz⟩ , use x, use y, rw zsqrtd.norm_def at hy,split,
      { rw ← hy, ring_nf, },
      { assumption }},

  { have H1: ∀ (x: S d), ∃ (a:A d), (⟨x.val.1, x.val.2⟩ : ℤ√d).norm = (a:ℤ),
      { intros, use (⟨x.val.1, x.val.2⟩ : ℤ√d).norm, swap, 
      { simp, },
      { have h1:= inf_bounded_pairs x hd,
        assumption, }
      },
    haveI h2: fintype ↥(A d), 
      { exact set.finite.fintype (A_finite d) },
    choose f H2 using H1,
    haveI h3: infinite ↥(S d):= set.infinite_coe_iff.mpr (S_infinite hd),
    have H3:= fintype.exists_infinite_fiber f,
    rcases H3 with ⟨N,hN ⟩,
    have H4: (N:ℤ) ≠ 0,
      { rw set.infinite_coe_iff at hN, 
        have g1:=set.infinite.nonempty hN, 
        cases g1 with u gu, 
        replace gu:  f(u)=N:= gu,
        have g2:=H2 u,
        rw ← gu, 
        rw ← pell_to_norm at g2,
        rw ← g2, exact pell_ne_zero _ _ hd (show 1≤ u.val.snd, begin rcases u with ⟨u1, u2, u3⟩, assumption, end), },
    let B:= {x:ℤ | ∃ (v:ℤ), x=v%N},
    have h5: set.finite B,
      { refine bdd_below.finite_of_bdd_above _ _, 
      { use 0, intros w hw, cases hw, rw hw_h, exact int.mod_nonneg hw_w H4, },
      { use abs N, intros w hw, cases hw, rw hw_h, apply le_of_lt, exact int.mod_lt hw_w H4, }},
    let C:= B ×ˢ B,
    have h6: set.finite C,
      { exact set.finite.prod h5 h5, },

    have h7: ∀ ( t: ↥(f ⁻¹' {N})), ∃ (c: ↥C), (((t.1.val.1)%N :ℤ) ,((t.1.val.2)%N :ℤ)) =((c.1.1:ℤ), (c.1.2:ℤ)),
      { intro t, use (((t.1.val.1)%N :ℤ) ,((t.1.val.2)%N :ℤ)), split,
        { use (t.val.val.fst % ↑N), simp, },
        { use (t.val.val.snd % ↑N), simp, },
      },

    choose g h8 using h7,
    haveI hC: fintype ↥C,
      { exact set.finite.fintype h6 },
    have h9:= fintype.exists_ne_map_eq_of_infinite g,
    rcases h9 with ⟨ x, y, hx, hy ⟩,
    rcases x with ⟨x1, x2⟩, rcases y with ⟨y1, y2⟩,
    have k1: x1.val.1*y1.val.1 - d*x1.val.2*y1.val.2 ≡ 0 [ZMOD (N:ℤ)],
      { sorry },
    have k2:  x1.val.1*x1.val.2 - y1.val.1*y1.val.2 ≡ 0 [ZMOD (N:ℤ)],
      { sorry },
    rw int.modeq_zero_iff_dvd at k1 k2,
    cases k1 with X hX, 
    cases k2 with Y hY, 
    use X, use (abs Y),
    rw ← pell_to_norm,
    sorry, 
  },
end


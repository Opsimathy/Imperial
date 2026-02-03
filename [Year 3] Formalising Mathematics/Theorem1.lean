import tactic
import data.int.basic
import data.nat.basic
import data.nat.modeq
import number_theory.zsqrtd.basic
import data.real.basic
import data.real.sqrt
import data.set.finite
import algebra.big_operators.order
import data.real.irrational

/-
# Pell's Equation
We start formalizing the fact that the equation x^2-dy^2 =1 always has a nontrivial solution. We do this in 3 files. This is the first one.
-/

/-
# Theorem 1: Irrational Approximation
The main goal of this file is to prove:
Theorem 1: Given an irrational a and a natural number Q>1, there exist integers p,q with 1 ≤ q < Q such that |p-qa|<1/Q.
-/

/--Define d to be a nonsquare natural number.--/
def nonsquare (m: ℤ) :=∀(a: ℤ), m  ≠ a*a 

variables {d : ℕ} {hd: nonsquare (d:ℤ)}


/--
Solving x^2-dy^2=1 is equivalent to finding a number in ℤ√d with norm 1. This will help us generate more solutions since 1^k =1.
--/
lemma pell_to_norm (x y: ℤ): x^2 - d*y^2= (⟨x, y⟩ : ℤ√d).norm :=
begin
  rw zsqrtd.norm_def, ring_nf,
end

/--Evaluate the pair ∈ ℤ√d on the reals. We will need this later on for pigeonhole principle. --/

noncomputable def zsqrt_eval (n : ℤ√d): ℝ :=  n.re + n.im* real.sqrt d

noncomputable def zsqrt_eval_conj (n : ℤ√d): ℝ :=  n.re - n.im* real.sqrt d


/--Multipying out two eval functions gives us the norm.--/
lemma eval_eval_conj_norm (n : ℤ√d) : zsqrt_eval n * zsqrt_eval_conj n = n.norm :=
begin
  unfold zsqrt_eval zsqrt_eval_conj, rw zsqrtd.norm_def, 
  ring_nf, rw real.sq_sqrt, norm_num,
  { ring },
  { norm_cast, exact zero_le d, },
end


/--There are infinitely many natural numbers.--/
lemma nat_infinite : set.infinite (set.univ : set ℕ) :=
begin
  exact set.infinite_univ,
end

/--If the floor of two numbers is the same then they are within 1 of each other.--/
lemma equal_floors (a b : ℝ) (g0: 0 ≤ a) (g1: 0≤ b) (g2: nat.floor a = nat.floor b):  abs(a-b) < 1:=
begin
  have h1:= nat.floor_le g0, 
  have h2:= nat.lt_floor_add_one a, 
  have h3:= nat.floor_le g1,
  have h4:= nat.lt_floor_add_one b, 
  rw abs_lt, split, 
  { simp * at *, linarith },
  { simp * at *, linarith },
end

/--Dividing both sides of an inequality. Useful for the main proof.--/
lemma dividing_ineq ( a b :ℝ ) (h: 0 < a) : a*b<1 ↔b < 1/a :=
begin
  exact (lt_div_iff' h).symm,
end 

/--Plugs in max and min instead of 2 real numbers in an equation. Equivalent to wlog a>=b arguments.--/
lemma plug_max_min (a b: ℕ) (f: ℕ → ℤ): f a = f b ↔ f (max a b) = f (min a b):=
begin
  cases le_total a b, 
  { rw max_eq_right h, rw min_eq_left h, exact comm },
  { rw max_eq_left h, rw min_eq_right h }
end

/--Can swap signs inside absolute value--/
lemma abs_eq_neg(p :ℝ) : abs p  = abs (-p) := by simp

/--Lift integers to naturals--/
lemma lift_to_nat ( Q: ℤ) (h: 0≤ Q): ∃ (n:ℕ), (n:ℤ) = Q:=
begin
  exact can_lift.prf Q h,
end

/--Q*{x} is non-negative--/
lemma nonneg_prod (Q:ℕ) (x:ℝ): 0≤ (Q:ℝ)*(int.fract (x:ℝ)):=
begin
  apply mul_nonneg (show 0 ≤ (Q:ℝ), begin norm_cast, linarith end), apply int.fract_nonneg,
end

/--Equality → Less Than → Less Than--/
lemma eq_lt_trans (a b c:ℝ )(h: a=b) ( h1: a<c): b< c:=
begin
  rw ← h, assumption,
end

/--Converts fractional part to floor--/
lemma fract_to_floor (a:ℝ) : int.fract a =a - ⌊a ⌋:=
begin
  exact rfl
end

/--max = min ↔ inputs are equal--/
lemma max_eq_min (x y:ℕ) :  max x y = min x y ↔ x=y:=
begin
  split, 
  { intro h, have h1:= le_max_left x y,
    have h2:= le_max_right x y,
    have h3:= min_le_left x y,
    have h4:= min_le_right x y,
    linarith },

  { intro h, rw h, simp },

end

/--Subtracting two numbers smaller than c is smaller than c. Needed in proving the last part of Theorem 1 where subtracting after PHP generates a number < Q.--/
lemma sub_lt_lt (a b c : ℕ) (h0: a <c) (h1: b<c) : (a-b:ℤ)< c:=
begin
  linarith,
end

/--|p-qa| is not rational--/
lemma irrational_ne_rational_abs (a :ℝ) (i:irrational a) (p q:ℤ) (h2: q ≠ 0) (x y:ℤ) (h: y ≠ 0)  (h1: abs((p:ℝ)-(q:ℝ)*a) = x/y ):   false:=
begin
  rw abs_eq at h1, swap,
    { rw ← h1, apply abs_nonneg, },
    { cases h1 with i1 i2,
  have h3: (y:ℝ) ≠ 0,
    { norm_cast, assumption },
  have h4: (q:ℝ) ≠ 0,
    { norm_cast, assumption },
      { have i3: a = (p*(y:ℝ)-x)/(y*q), 
          { rw eq_div_iff h3 at i1, rw ← i1, field_simp, ring, },  
        rw irrational_iff_ne_rational at i, contrapose! i, use (p*y-x), use y*q, rw i3, norm_cast, },
      { have i3: a = (p*(y:ℝ)+x)/(y*q), 
          { field_simp * at *, rw (show (x:ℝ) = (-1)*(-(x:ℝ)), by ring), rw ← i2, ring, },
        rw irrational_iff_ne_rational at i, contrapose! i, use (p*y+x), use y*q, rw i3, norm_cast, }}, 
end

/--Theorem 1 ↔ Theorem 1' where strict inequalty < 1/Q is replaced by ≤ 1/Q. This uses the previous result.--/
lemma imp_irrational_approx (a : ℝ) (i: irrational a) (Q: ℕ ) (h0: 1<Q) (H: ∃ (p q : ℤ) , abs ((p:ℝ)-q*a) ≤  1/Q ∧ 1 ≤ q ∧ q < Q ): ∃ (p q : ℤ) , abs ((p:ℝ)-q*a) < 1/Q ∧ 1 ≤ q ∧ q < Q:=
begin
  rcases H with ⟨p, q, h1, h2⟩,
      use p, use q, split, swap,
      { exact h2, },
      { rw le_iff_eq_or_lt at h1, cases h1, swap,
        { assumption },
        { exfalso, 
          apply irrational_ne_rational_abs a i p q (show q ≠ 0, by linarith) 1 (Q:ℤ) (show _, begin norm_cast, linarith end) (show _, begin rw h1, simp end), }}
end

/--The main theorem of this file. For any irrational we can find a rational number that very closely approximates it. 
The proof is by pigeonhole principal.--/
theorem irrational_approx (a : ℝ) (i: irrational a) (Q: ℕ ) (h0: 1<Q) : ∃ (p q : ℤ) , abs ((p:ℝ)-q*a) < 1/Q ∧ 1 ≤ q ∧ q < Q :=
begin
  have hQ: (Q:ℝ) ≠ 0,
    { norm_cast, linarith, },
  apply imp_irrational_approx a i Q h0,

  let A:= fin Q,
  let B:= fin (Q-1),
  have h1:= em( ∃(u:A),  ((Q:ℝ)-1)/Q ≤ int.fract((u:ℝ)*a)),
  cases h1 with h1 h2,
  { cases h1 with u h1, use (1+int.floor((u:ℝ)*a)), use u, split, 
    { have h2: 1-int.fract((u:ℝ) * a) ≤ 1/(Q:ℝ),
        { rw sub_le, convert h1, 
        field_simp [hQ], },
      have h3: 0 ≤ 1 - int.fract (↑u * a),
        { apply le_of_lt, rw lt_sub, rw sub_zero, exact int.fract_lt_one (↑u * a), },
      unfold int.fract at h2 h3, rw abs_eq_neg, rw ← abs_eq_self at h3, rw ← h3 at h2, rw abs_eq_neg, convert h2, simp *, unfold int.fract, ring, },

      split, 
      { by_contra, push_neg at h, cases u with u hu, dsimp at *,
        have i1: (u:ℝ)=0,
          { norm_cast, linarith },
        rw i1 at h1, 
        have i2:= div_pos (show 0<(Q:ℝ)-1, begin simp, assumption end) (show 0<(Q:ℝ), begin norm_cast, linarith end),
        simp * at *, linarith, },
      { cases u, dsimp, norm_cast, assumption,  }},

      { push_neg at h2, 
        have hQ1: 0 < (Q: ℝ),
          { norm_cast, linarith, },
        simp only [lt_div_iff' hQ1] at h2, 
        have h4:∀ (r:A), ∃(b : B), ↑b= nat.floor((Q:ℝ)*int.fract(r*a)), 
        { intro r, use nat.floor((Q:ℝ)*int.fract(r*a)), swap,
          { ring, },
          { rw nat.floor_lt, convert h2 r, simp * at *, exact nonneg_prod Q _, }}, 
        
        choose f h5 using h4, 
        obtain ⟨x, y, h9, h10⟩:= fintype.exists_ne_map_eq_of_card_lt f (show _, begin simp, omega  end),
        cases x with x hx, cases y with y hy,
        have h7: ((f ⟨x, hx⟩ :ℕ ):ℤ) = (f ⟨y, hy⟩:ℕ),
          { norm_cast, exact congr_arg coe h10 },
        rw h5 ⟨x, hx⟩ at h7, 
        rw h5 ⟨y, hy⟩ at h7, dsimp at h7, 
        rw plug_max_min x y (λx, nat.floor(↑Q * int.fract (↑x * a))) at h7,
        dsimp at h7, norm_cast at h7,
        have h8:= equal_floors (↑Q * int.fract (↑(max x y) * a)) (↑Q * int.fract (↑(min x y) * a)) (nonneg_prod _ _) (nonneg_prod _ _) h7,
        set m := max x y, 
        set n := min x y, 
        use (int.floor((m:ℝ)*a)-int.floor((n:ℝ)*a)), use (m-n :ℤ), 
        split,

        { rw ← mul_sub at h8, rw abs_mul at h8,
        have j1: abs (Q:ℝ) = Q,
          { rw abs_eq_self, apply le_of_lt hQ1 },
        rw j1 at h8, rw ← lt_div_iff' hQ1 at h8, apply le_of_lt, rw abs_eq_neg, apply eq_lt_trans _ _ _ _ h8, 
        apply congr_arg (λ(x:ℝ), abs(x) ), rw fract_to_floor, rw fract_to_floor, ring_nf, ring_nf,
        congr, 
          { simp },
          { simp, ring } },

      split, 
      { have i1: 0 ≤ (m-n:ℤ),
        { rw sub_nonneg, simp[min_le_max], },
        by_contra, push_neg at h, interval_cases (m-n:ℤ),
        rw sub_eq_zero at h_1, norm_cast at h_1, rw max_eq_min x y at h_1, rw h_1 at hx, cc },
      
      { apply sub_lt_lt _ _ _ (show m < Q,by exact max_lt hx hy ) _, apply lt_of_le_of_lt (min_le_right x y) hy, }
      } 
end

/--p equals its absolute value ↔ p is non-negative--/
lemma abs_equal (p q: ℝ): 0 ≤  p ↔ p = abs p :=
begin
  split, 
  { intro h, unfold abs, simp, exact h, },
  { intro h, exact abs_eq_self.mp (eq.symm h), }
end



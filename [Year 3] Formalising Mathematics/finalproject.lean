/-
Formalising Mathematics - Project 3
Based on Number Theory module taken in term 1 of MSc in Pure Mathematics 2021-22
Submitted by: Additi Pandey 
CID: 02119403
-/

--We will first import the necessary mathlib libraries needed to proceed with the definitions and proofs. 
import tactic 
import data.int.modeq 
import data.zmod.basic 
import data.int.gcd 
import init.data.int.basic
import data.nat.prime 
import algebra.big_operators.finprod 
import number_theory.divisors 

/-!
## Number Theory Problem - Reflexive and Corpulent Integers
This file is based on a problem in the Number Theory past paper for Year 3/4. The question
deals with a integer `n` which is said to be:
* Reflexive - If two conditions are equivalent, that is, if `∀ a,b ∈ ℤ` with `(a,b) = 1` then,
 `a ≡ b (mod n)` and `a*b ≡ 1 (mod n)`.
* Corpulent - If `∀ a ∈ ℤ` with `(a,n)=1`, `a^2 ≡ 1 (mod n)`. 
The aim is to first show that `n` is reflexive ↔ `n` is corpulent and then show that if `n` is 
corpulent then all prime divisors of `n` are also corpulent. -/

/-- Definition of Reflexive Number: An integer `1 ≤ n` is reflexive if for all integers `a b` with 
`a.gcd b = 1`, the following two conditions are equivalent:
(i) `a ≡ b (mod n)`. 
(ii) `a * b ≡ 1 (mod n)`.-/
def reflexiv {n : ℕ} (hn : 1 ≤ n) :=
(∀ {a b : ℤ} (h : a.gcd b = 1),  a ≡ b [ZMOD n] ↔ a * b ≡ 1 [ZMOD n])

/-
Hence, `reflexiv` defines a integer `n` which is `1 ≤ n` as reflexive. To define a natural 
number `n` as corpulent, a `def` called `corpulent` is defined as :
-/

/--Definition of Corpulent Number: An integer `1 ≤ n` is corpulent if for all integers `a` with 
`a.gcd n = 1`, we have `a^2 ≡ 1 (mod n)`.-/
def corpulent {n : ℕ} (hn : 1 ≤ n) :=
( ∀ {a : ℤ} (han : a.gcd n = 1), a^2  ≡ 1 [ZMOD n])

/-
We now declare the global variables `n` and `m` so that if they are used anywhere in the file,
Lean knows that they are in `ℕ` and `1 ≤ n`.
-/
variables  {n : ℕ} (hn : 1 ≤ n) {m : ℕ}

/- 
To proceed with the proof of "`n` is reflexive ↔ `n` is corpulent", there was a requirement of a
lemma called  `int.gcd_add_self_left (m n : ℤ) : m.gcd (m + n) = m.gcd n` which says that:
if `m` and `n` are two integers then `gcd(m,m+n)` is same as the `gcd(m,n)`. So to show this,
Professor Kevin Buzzard defined `int.nat_abs_def` which says that if an integer `a ≥ 0` then it 
is defined as `a` or else it is less than `0` and is defined as `-a`. He proceeded to further 
define `int.add_nat_abs` which defines `(a+b).nat_abs`, `a.nat_abs` and `b.nat_abs` and defined 
`int.gcd_add_self_right` which helped in defining `int.nat_add_self_left` by applying `add_comm`
and `gcd_comm` on the already proven `int.gcd_add_self_left` theorem. 
-/

/-- This theorem applies cases on `a` to show that if `a ≥ 0` then it is either `a` or `-a`. -/
theorem int.nat_abs_def (a : ℤ) : (a.nat_abs : ℤ) = if 0 ≤ a then a else -a :=
begin
  cases a,
  { simp,},
  { ring,},
end

/-- Defining integers and their sum in `nat_abs`, i.e. coercing from `ℤ` to `ℕ`. -/
theorem int.add_nat_abs (a b : ℤ) : 
  (a + b).nat_abs = a.nat_abs + b.nat_abs ∨ 
  a.nat_abs = (a + b).nat_abs + b.nat_abs ∨
  b.nat_abs = (a + b).nat_abs + a.nat_abs :=
begin
  zify,
  simp [int.nat_abs_def],
  split_ifs,
  { left, ring, },
  { right, left, ring, },
  { right, right, ring, },
  { linarith, },
  { linarith, },
  { right, right, ring, },
  { right, left, ring, },
  { left, ring },
end

/-- Given two integers `m` and `n`, show that `gcd(m,n+m) = gcd(m,n)`. -/
theorem int.gcd_add_self_right  (m n : ℤ) :
m.gcd (n + m) = m.gcd n :=
begin
  change (m.nat_abs).gcd (n + m).nat_abs = (m.nat_abs).gcd n.nat_abs,
  rcases int.add_nat_abs n m with (h | h | h);
  rw h,
  { exact (int.nat_abs m).gcd_add_self_right (int.nat_abs n) },
  { exact ((int.nat_abs m).gcd_add_self_right (n + m).nat_abs).symm },
  { rw nat.gcd_add_self_left,
    rw add_comm,
    rw nat.gcd_add_self_left,
    rw nat.gcd_comm },
end

/-- Using the above three theorems, I created a lemma that given integers `m` and `n`,
the  `gcd(m,m_n) = gcd(m,n)`. -/
@[simp]lemma int.gcd_add_self_left (m n : ℤ) : m.gcd (m + n) = m.gcd n := 
begin
  change (m.nat_abs).gcd (m + n).nat_abs = (m.nat_abs).gcd n.nat_abs,
  rcases int.add_nat_abs m n with (h | h | h);
  rw h,
  { exact (int.nat_abs m).gcd_self_add_right (int.nat_abs n),},
  { rw nat.gcd_add_self_left,
    rw add_comm,
    rw nat.gcd_add_self_left,
    rw nat.gcd_comm,},
  { rw add_comm,
    exact ((int.nat_abs m).gcd_add_self_right (n + m).nat_abs).symm,},
end

/-
Having defined `int.gcd_add_self_left`, there are two other lemmas needed that will help in 
proving that an integer  `1 ≤ n` is reflexive ↔ `1 ≤ n` is corpulent. The first lemma is called
`gcd_sn_given_t_s` which gives the gcd of two numbers `s` and `n` (where `s` is an integer and since,
`n` is such that `1 ≤ n`, the number `n` is defined as `n : ℕ`), when `t ≡ s [ZMOD n]` and `gcd(s,t) = 1`.
This lemma has been proven by contradiction as it did not involve dealing with integer divisions, which 
is a harder and lesser efficient approach.
After this, there is a lemma  `gcd_sn_given_st` defined, which by its name tells that given `gcd(s,t) = 1`
and `s*t ≡ 1 [ZMOD n]`, the `gcd(s,n) = 1`. Again, I proved this by contradiction, as it was easier
to avoid integer division in this method, which tends to be more pathological. 
-/

/-- Given `gcd(s,t) = 1` and `t ≡ s [ZMOD n]`, show that `gcd(s,n) = 1`. -/
lemma gcd_sn_given_t_s {s t : ℤ} {n : ℕ} (hp : t ≡ s [ZMOD n]): (s.gcd t) = 1 → (s.gcd n) = 1 := 
begin
  intro hst,
  --We will now proceed by contradiction. 
  apply of_not_not, 
  intro hk,
  set d :=  (s.gcd n) with hd, -- Letting `d` to be the `gcd (s, n)`.
  -- Since `d` is the `gcd (s,n) → d ∣ s ∧ d ∣ n`.
  have h1: (d : ℤ) ∣ s, 
  { apply int.gcd_dvd_left s n,},
  have h2: (d : ℤ) ∣ n,
  { apply int.gcd_dvd_right s n,},
  -- Since `d ∣ s → s = d * p`, for some `(p : ℤ)` and similarly, `↑n = ↑d * q`, for some `(q : ℤ)`.
  have h12: ∃ (p : ℤ), s = d * p,
  { assumption,},
  have h22 :  ∃ (q : ℤ), ↑n = ↑d * q,
  { assumption, },
  -- We have `t ≡ s [ZMOD n]`, so `↑n ∣ (t - s)` and since, `d ∣ n`, we have `d ∣ (t - s)`.
  have h4 : ↑ n ∣ (t - s),
  { apply int.modeq.dvd,
    exact hp.symm,},
  have h5' : (d : ℤ) ∣ (t - s),
  { cases h22 with c hc,
    exact dvd_trans h2 h4,},
  -- The previous hypothesis imply that `d ∣ s` and `d ∣ t` but we already have `h1` for former. 
  have h5: (d : ℤ) ∣ t,
  { exact (dvd_iff_dvd_of_dvd_sub h5').mpr h1,},
  have h6: ↑ d ∣ ↑ (s.gcd t), -- Since `d` divides both `s` and `t`, it should divide their gcd.
  { apply int.dvd_gcd h1 h5,},
  rw hst at h6, -- The `gcd (s,t) = 1` 
  norm_cast at *, 
  -- `d ∣ 1` so `d = 1` but we assumed it is `≠ 1`, hence, a contradiction!
  finish,
end

/-- Given `gcd(s,t) = 1` and `s * t ≡ 1 [ZMOD n]`, show that `gcd(s,n) = 1`. -/
@[simp]lemma gcd_sn_given_st {s t : ℤ}{n : ℕ} (hp : s * t ≡ 1 [ZMOD n]) : s.gcd n = 1 := 
begin
  -- As there was no use of `gcd(s,t) = 1` in the proof, I omitted it from the definition of lemma. 
  -- We will proceed by contradiction. 
  apply of_not_not, -- Assume that the `gcd(s,n) ≠ 1`.
  intro hk,
  set d :=  (s.gcd n) with hd, -- Let `d` be the `gcd (s,n)`.
  -- Clearly `d ∣ s` and `d ∣ n`.
  have h1: (d : ℤ) ∣ s, 
  { apply int.gcd_dvd_left s n,},
  have h2: (d : ℤ) ∣ n,
  { apply int.gcd_dvd_right s n,},
  -- Given `s * t ≡ 1 [ZMOD n] → ↑n ∣ (s*t -1)`.
  have h3: ↑ n ∣ (s * t - 1) ,
  { apply int.modeq.dvd,
    apply hp.symm,},
  rw dvd_iff_exists_eq_mul_left at h3,
  -- With `h3` now, we can express `s * t - 1` in terms of `n`.
  have h3' : ∃ (c : ℤ), s * t - n * c = 1,
  { cases h3 with k hk,
    use k,
    rw mul_comm ↑ n k,
    linarith,},
  -- Since `d ∣ s` and `d ∣ n`, `d` should divide their linear combination. 
  have h4: ∃ (c : ℤ), ↑ d ∣ (s * t - n * c),
  { cases h1 with x hx,
    cases h2 with y hy,
    cases h3 with k hk,
    rw hx,
    rw hy,
    use k,
    rw [mul_assoc, mul_assoc],
    rw ← mul_sub (↑d) (x*t) (y * k),
    simp,},
  have hs : ∀ (c : ℤ), ↑ d ∣ s * c,
  { apply dvd_mul_of_dvd_left h1,},
  have hn : ∀ (c : ℤ), ↑ d ∣ ↑ n * c,
  { apply dvd_mul_of_dvd_left h2,},
  -- Since `∀ c` in ℤ,  `d ∣ s * c` , `d` will divide `s * t` where `t` is an integer. 
  have hs_ : ↑ d ∣ s * t,
  { apply hs,},
  have hn_ : ∃ (c : ℤ), ↑d ∣ ↑n * c,
  { tauto,},
  -- Since `d` divides `s * t - ↑n * c` so it will divide `1` as well by `h3`.
  have h5: ↑ d ∣ (1 : ℤ),
  { cases h3' with k hk,
    rw ← hk,
    specialize hn k,
    apply dvd_sub hs_ hn, },
  norm_cast at *,
  finish, -- `d ∣ 1` → `d = 1` and this imply that our claim that `d ≠ 1` is false.  
end

/-- Show that `n` is reflexive if and only if `n` is corpulent.-/
theorem reflexive_iff_corpulent : reflexiv hn ↔ corpulent hn := 
begin
  split,
  -- We will first prove the forward direction, i.e., `n` is reflexive → `n` is corpulent. 
    { unfold reflexiv, 
      unfold corpulent, 
      intros hp q hqn, 
      -- The goal now is to show that `q ^ 2 ≡ 1 [ZMOD ↑n]`, given `n`, `hn`, `hp`, `q`, `hqn`.
      have hp1 : q.gcd (q+n) = 1 → (q ≡ (q+n) [ZMOD ↑n] ↔ q * (q+n) ≡ 1 [ZMOD ↑n]),
        { exact hp},
      have hp2 : (q ≡ q + ↑n [ZMOD ↑n] ↔ q * (q + ↑n) ≡ 1 [ZMOD ↑n]),
        { rw hp1, 
          simp,
          rw hqn },
      have hp3 : q * (q + ↑n) ≡ 1 [ZMOD ↑n],
        { rw ← hp2,
          apply int.modeq.symm,
          have h1 : q ≡ q [ZMOD ↑n] := int.modeq.rfl, 
          have h2 : ↑n ≡ 0 [ZMOD ↑n],
          { rw int.modeq_zero_iff_dvd,},
          conv
            begin
              to_rhs,
              congr,
              skip,
              skip,
              rw ← add_zero q,
            end,
          apply int.modeq.add,
          exact h1,
          exact h2, },
      have hp4: (q * ↑n) ≡ 0 [ZMOD ↑n],
      { rw int.modeq,
        simp only [int.mul_mod_left, euclidean_domain.zero_mod],},
      have hp5 : q ^ 2 + (q * ↑n) ≡ 1 [ZMOD ↑n],
      { have h: q * q = q ^ 2,
        { ring,},
        rw ← h,
        rw ← mul_add,
        exact hp3,},
      set x := q + ↑n with hx,
      set y := q * ↑n with hy,
      have hp6: q ^ 2 + y - y ≡ 1 - 0 [ZMOD ↑n],
      { apply int.modeq.sub hp5 hp4,},
      simp at hp6,
      exact hp6,},
  -- We will now prove the converse, i.e. `n` is corpulent → `n` is reflexive. 
    { unfold corpulent,
      unfold reflexiv,
      intros hp s t hst,
      -- After unfolding the definitions of reflexive and corpulent, we observe that given
      -- `n`, `hn`, `hp`, integers `s` and `t`, and a hypothesis `hst`, we need to show two 
      -- things to prove that `n` is reflexive. So, the goal now is `s ≡ t [ZMOD ↑n] ↔ s * t ≡ 1 [ZMOD ↑n]`.
      split,
      -- We will first show that given `s ≡ t [ZMOD ↑n] →  s * t ≡ 1 [ZMOD ↑n]`.
      { intro hst_mod,
        have h : t * t = t ^ 2,
        { ring,},
        have hts : t ≡ s [ZMOD ↑n],
        { apply int.modeq.symm,
          exact hst_mod,},
        have htn : t.gcd n = 1,
        { rwa gcd_sn_given_t_s hst_mod,
          rwa int.gcd_comm,},
        have ht: t * t ≡ 1 [ZMOD ↑n],
        { rw h,
          apply hp,
          exact htn,},
        have hst : s * t ≡ t * t [ZMOD ↑n],
        { apply int.modeq.mul_right t hst_mod,},
        apply int.modeq.trans hst ht,},
      -- We will now show that `s * t ≡ 1 [ZMOD ↑n] → s ≡ t [ZMOD ↑n]`.
      { intro h_st,
        have hsn : s.gcd n = 1,
        { rwa gcd_sn_given_st h_st,},
        have hss : s^2 ≡ 1 [ZMOD ↑n],
        { apply hp,
          exact hsn,},
        have hs2 : s^2 = s * s,
        { ring,},
        have hs_modn : s * s ≡ 1 [ZMOD ↑n],
        { rw ← hs2,
          exact hss,},
        have hst2 : s * s - s * t ≡ 1 - 1 [ZMOD ↑n],
        { apply int.modeq.sub hs_modn h_st,},
        simp at hst2,
        have hst_sub : s * (s - t) = s * s - s * t ,
        { rw mul_sub,},
        have hp_st_sub: s * (s-t) ≡ 0 [ZMOD ↑n],
        { rw hst_sub,
          exact hst2,},
        have hn_dvd_st: ↑n ∣ s * (s - t),
        { set x := s * (s - t) with hx,
          rwa ← int.modeq_zero_iff_dvd,},
        have hns_gcd : (n : ℤ).gcd s = 1,
        { rw hsn.symm,
          exact int.gcd_comm n s,},
        have hn_dvd_st : ↑n ∣ (s - t),
        { apply int.dvd_of_dvd_mul_right_of_gcd_one hn_dvd_st hns_gcd,},
        have hts_modn: t ≡ s [ZMOD ↑n],
        { apply int.modeq_of_dvd,
          exact hn_dvd_st,},
        apply int.modeq.symm ,
        exact hts_modn,},},
  -- Hence, we proved that `n` is reflexive ↔ `n` is corpulent. 
end

/-
To proceed with the next part of the project which is to prove that `n` is corpulent ↔
`m` is corpulent for every prime power `m` dividing `n`, I constructed a helper lemma called
`na.coprime_lift`, which shows that units in `[ZMOD n]` are the units in `[ZMOD m]`. To do so,
I constructed a `findprod f` called `x` to denote the product of all primes dividing `n` which 
do not divide `b`, and `f` is a map from `nat.coprime_alpha` (which gives a condition on primes)
to the set of integers, such that `b` is some integer such that ∃ an `a₀ : ℤ` is coprime to `n` 
and `a₀ ≡ b [ZMOD d]` where `d ∣ n` and `gcd(b,d) = 1`.
-/

/-- Defining a subtype `nat.coprime_alpha` such that `∀ n,d ∈ ℕ` and `b ∈ ℤ`, there is a set of 
primes `p` which divide `n` but do not divide `b`. -/
@[nolint has_inhabited_instance] def nat.coprime_alpha (n : ℕ) (b : ℤ):
  Type := { p : ℕ // p∣n ∧ ¬ ↑p∣b ∧ p.prime}

/-
To proceed with the proof, there are lemmas that need to be defined as below:
The lemmas `dvd_mem_gcd` and `dvd_mem_gcd` state that if there are integers `a` and `b` such that 
for all primes that divide `a`, do not divide `b` or primes that do not divide `b` and divide `a`, 
the `gcd(a,b) = 1`. The lemma `dvd_mem_dvd_sum` is a basic lemma stating that if a number does not 
divide one or all of the members, then it does not divide their sum. The proof of the same is by 
contradiction. 
-/

/-- For some integers `a` and `b`, and `∀ (p : ℕ)` where `p` is prime and divides `a`, then `p` do 
not divide `b ↔ gcd (a,b) = 1`. -/
lemma dvd_mem_gcd (a b : ℤ) : (∀ p : ℕ, p.prime → ↑p ∣ a → ¬ ↑p ∣ b) ↔ a.gcd b = 1 := 
begin
  split,
  -- To show that: `a.gcd b = 1`
  { intro hp,
    -- We proceed by contradiction. 
    apply of_not_not,
    set d:= a.gcd b with hd,
    intro hpd,
    have d_ne1 : d ≠ 1,
    { exact hpd, },
    -- If `a.gcd b` is not equal to `1` then there is a prime such that it divides the gcd. 
    have hprime_d : ∃ (p : ℕ) , p.prime ∧ p ∣ d,
    { rwa nat.ne_one_iff_exists_prime_dvd at d_ne1,},
    -- Since the prime divides the `a.gcd b` → it divides `a` and `b`.
    have hprime_a_b :∃ (p : ℕ) , p.prime ∧ ↑p ∣ a ∧ ↑p ∣ b,
    {
      cases hprime_d with p hprime,
      use p,
      have hd_a : (d : ℤ) ∣ a,
      {
        exact int.gcd_dvd_left a b,
      },
      have hd_b : (d : ℤ) ∣ b,
      {
        exact int.gcd_dvd_right a b,
      },
      split,
      {exact hprime.1,},
      { split,
        { exact dvd_trans (int.coe_nat_dvd.mpr hprime.2) hd_a,},
        {exact dvd_trans (int.coe_nat_dvd.mpr hprime.2) hd_b,},},},
    finish,},
    -- To show : `a.gcd b = 1 → ∀ (p : ℕ), nat.prime p → ↑p ∣ a → ¬↑p ∣ b`
    { intros hp p hprime hp_a hp_b,
      have hp_gcd : ↑p ∣ ↑ (a.gcd b),
      { apply int.dvd_gcd hp_a hp_b,},
      rw hp at hp_gcd,
      -- Since `p` divides `a` and `b` and also their gcd → `p ∣ 1` but a prime does 
      -- not divide `1`, hence, proved `a.gcd b = 1 → ∀ (p : ℕ), nat.prime p → ↑p ∣ a → ¬↑p ∣ b`
      apply nat.prime.not_dvd_one hprime (int.coe_nat_dvd.mp hp_gcd),
    },
end

/-- If `c` divides `a` and `c` does not divide `b`, then it does not divide their sum. -/
lemma dvd_mem_dvd_sum (a b c: ℤ) : (c ∣ a ∧ ¬ c ∣ b) →  ¬ c ∣ (a + b) := 
begin
  intros h_ab hp,
  set d:= a.gcd b with hd,
  have hc_a : c ∣ a ,
  { finish,},
  have hc_b : c ∣ ((a+b)-a),
  { apply dvd_sub hp hc_a,},
  simp at hc_b,
  finish,
end

/-- Define a map from `nat.coprime_alpha` to the set of natural numbers. -/
def nat.coprime_alpha_id (n : ℕ) (b : ℤ) : nat.coprime_alpha n b → ℕ := λ p, p.1

/-- To show that the mul_support of the map `nat.coprime_alpha_id n b` is finite.-/
lemma nat.coprime_alpha_finite (n : ℕ) (b : ℤ) (hn : 0 < n) : 
(function.mul_support (nat.coprime_alpha_id n b)).finite :=
begin
show set.finite {x : nat.coprime_alpha n b | nat.coprime_alpha_id n b x ≠ 1},
unfold nat.coprime_alpha_id,
have t : {a : ℕ | a ∣ n} ⊆ {a : ℕ | a ≤ n},
{ intro a, 
  apply nat.le_of_dvd hn,},
have k : fintype (n.coprime_alpha b),
{ unfold nat.coprime_alpha,
  show fintype ↥{p | p ∣ n ∧ ¬↑p ∣ b ∧ nat.prime p}, 
  apply set.finite.fintype,
  rw [set.set_of_and, set.set_of_and],
  apply set.finite.inter_of_left,
  apply set.finite.subset (set.finite_le_nat _) t,},
apply @set.finite.of_fintype _ k _,
end

/-- Helper lemma to show that if `p ∣ finprod f` then there is a `t` in `α` such that 
`p` divides that `t` in the product of `f t`-/
lemma prime_dvd_finprod {α : Type} (f : α → ℕ) (hf : (function.mul_support f).finite) 
{p : ℕ} (hp : p.prime) : p ∣ finprod f ↔ ∃ t : α, p ∣ f t := sorry

/-- This is a pre-existing mathlib lemma that says that if a prime number is divisible by a 
natural number which is not `1`, then the number is the prime number itself. -/
lemma nat.prime.dvd_iff_eq {p a : ℕ} (hp : p.prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := sorry

/- Please note: The above stated lemma is already there in mathlib but since the addition was
recent (in the month of March itself), I am unable to use it in my file. Hence, I mentioned it
here. -/

/-- Defining `nat.coprime_lift` which says that units in `[ZMOD n]` are units in `[ZMOD d]` where
`d∣n` and here, the goal is to show that this map is surjective. Reference for the proof can be found
on the link : https://math.stackexchange.com/q/487022 -/
lemma nat.coprime_lift {n d : ℕ} {b : ℤ}
  (hn : 1 ≤ n)
  (hs : d ∣ n)
  (hyp : b.gcd ↑d = 1) :
  ∃ a₀ : ℤ, a₀.gcd n = 1 ∧ a₀ ≡ b [ZMOD d] :=
begin
  set f:= nat.coprime_alpha_id n b,
  set x:= finprod f,
  use (b + d * x),
  have hyp' : (d : ℤ).gcd b = 1,
  { rwa int.gcd_comm ↑d b,},
  split,
  -- To first show that : `(b + ↑d * ↑x).gcd ↑n = 1`
  { set g:= (b + ↑d * x).gcd ↑n with hg,
    have h1: ↑g ∣ ↑n,
    { apply int.gcd_dvd_right (b + ↑d * x) ↑n,},
    have h2: ↑g ∣ (b + ↑d * x),
    { apply int.gcd_dvd_left (b + ↑d * x) ↑n,},
    -- To show that: All primes that divide `n`, do not divide `(b + ↑d * x)`:
    have h3: ∀ (p : ℕ), p.prime ∧ p ∣ n → ¬ ↑p ∣ (b + ↑d * x),
      { intros p hp1 hp2,
      by_cases (↑p ∣ b),
      -- To show if `p` divides `b` then it does not divide `(↑d * x)` hence, 
      -- does not divide `(b + ↑d * x)`
      { have h3_pd : ¬ ↑p ∣ ↑d,
        { apply (dvd_mem_gcd b ↑d).mpr hyp p hp1.1 h,}, 
        have h3_pd_nat : ¬ p ∣ d,
        { intro ht, 
        have hkt: ↑p ∣ ↑d,
        {exact int.coe_nat_dvd.mpr ht,}, finish, },
        have h3_px : ¬ p ∣ x,
        { intro hpx,
          change p ∣ finprod f at hpx,
          rw prime_dvd_finprod f (nat.coprime_alpha_finite n b hn) hp1.1 at hpx,
          cases hpx with t ht,
          change p ∣ t.1 at ht,
          set t_val2 := t.2,
          have h3_t_ne1 : t.val ≠ 1,
          { apply nat.prime.ne_one t_val2.2.2,},
          have h_p_ne1 : p ≠ 1,
          {apply nat.prime.ne_one hp1.1,},
          have h3_tp : p = t.val,
          { rw (nat.prime.dvd_iff_eq hp1.1 h3_t_ne1).mp,
            rwa (nat.prime.dvd_iff_eq t_val2.2.2 h_p_ne1).mp,},
          finish,},
        have h3'_p : ¬ p ∣ (d * x),
        { apply nat.prime.not_dvd_mul hp1.1 h3_pd_nat h3_px,},
        have h3''_p :  ¬ ↑p ∣ (d : ℤ) * x,
        { norm_cast,
          exact h3'_p,},
        have h3_p : ¬ ↑p ∣ (b + ↑d * x) ,
        { apply dvd_mem_dvd_sum b (↑d * x) ↑p,
          change ¬ (p : ℤ) ∣ ↑d * ↑x at h3''_p,
          refine ⟨h, h3''_p⟩,},
        finish,},
      -- To show if `p` does not divide `b` then it does not divide `(b + ↑d * x)`.
      { have h3' : p ∣ x,
        { show p ∣ finprod f, 
         rw prime_dvd_finprod f (nat.coprime_alpha_finite n b hn) hp1.1,
         use p,
         finish,
         finish,}, 
         have h3'' : ↑ p ∣ ↑x,
         {  exact int.coe_nat_dvd.mpr h3'},
        have h3_p : ¬ ↑p ∣ (↑d * ↑x + b) ,
        { apply dvd_mem_dvd_sum (↑d * x) b ↑p, 
        split,
        -- To show that `p` divides `(↑d * x)`.
        { apply dvd_mul_of_dvd_right h3'' ↑d,},
        -- To show that `p` does not divide `b`.
        {exact h,},},
        have h3_p : ¬ ↑p ∣ (b + ↑d * x ),
        { rwa add_comm at h3_p,},
        -- Hence, we have a contradiction at `hp2` and `h3_p`. 
        finish,},},
        -- We have shown that all primes `p` that divide `n`, do not divide `(b + ↑d * x)`.
        -- To show: (b + ↑d * x).gcd n = 1
        show (b + d * x).gcd n = 1,
        have h3': ∀ (p : ℕ), p.prime → (p : ℤ) ∣ (n : ℤ) → ¬ ↑p ∣ (b + ↑d * x), 
        {intros p hp hs ht, rw int.coe_nat_dvd at hs, finish, },
        rw ← (dvd_mem_gcd n (b + d*x)).mp h3',
        rw int.gcd_comm,},
  -- To show that: `b + ↑d * ↑x ≡ b [ZMOD ↑d]`.
  { rw int.modeq_iff_dvd,
    simp only [dvd_neg, sub_add_cancel', dvd_mul_right],},
end

/- 
We now have all the lemmas needed to prove the second theorem of the project, so we define the theorem
as below and prove it by first unfolding our definitions and then using `nat.coprime_lift` and 
`int.modeq.modeq_of_dvd`, we get `a₀ ^ 2 ≡ 1 [ZMOD ↑(p ^ e)]`. We will use this and `a₀ ≡ b [ZMOD ↑t]`
to show that `b ^ 2 ≡ 1 [ZMOD ↑(p ^ e)]` as follows:
-/

/--Show that `n` is corpulent if `m` is corpulent for every prime power `m|n` 
(i.e. for every divisor of `n` of the form `p^e` with `1 ≤ e`).-/
theorem corpulent_two_int: corpulent hn →  ∀ {p e : ℕ} {hp : nat.prime p} {hm : (pow p e) ∣ n} ,
 corpulent (pow_pos (nat.pos_of_ne_zero (nat.prime.ne_zero hp)) e) :=
begin
  { unfold corpulent, 
    intros hp p e s hs,
    unfold corpulent,
    intros b hyp,
    -- To show: `b ^ 2 ≡ 1 [ZMOD ↑(p ^ e)]`, we can use `nat.coprime_lift` and draw a
    -- connection between the units in `[ZMOD ↑n]` and `[ZMOD ↑(p ^ e)]`. 
    obtain ⟨a₀, ha₀n, ha₀b⟩ := nat.coprime_lift hn hs hyp,
    specialize @hp a₀ ha₀n,
    set t:= (p ^ e) with ht,
    -- Since we have that `t ∣ n`, we can say that if `a₀ ^ 2 ≡ 1 [ZMOD ↑n]` then 
    --`a₀ ^ 2 ≡ 1 [ZMOD ↑(p ^ e)]`.
    have ht: ↑t ∣ ↑n,
    { exact int.coe_nat_dvd.mpr hs, },
    have hp' : a₀ ^ 2 ≡ 1 [ZMOD ↑(p^e)],
    { apply int.modeq.modeq_of_dvd ht hp, },
    have hab : ↑t ∣ (a₀ - b),
    { apply int.modeq.dvd ,
      exact ha₀b.symm,},
    rw dvd_iff_exists_eq_mul_left at hab,
    -- Expressing `a₀` in terms of `↑t` and `b`, so that we can get an expression for `b` and `↑t`: 
    have h_ab: ∃ (c : ℤ), a₀ = c * ↑t + b,
    { cases hab with k hk,
      use k,
      rw ← mul_comm ↑t k,
      linarith, },
    have h_ap : ↑t ∣ (a₀ ^ 2 - 1),
    { apply int.modeq.dvd ,
    exact hp'.symm, },
    rw dvd_iff_exists_eq_mul_left at h_ap,
    have h_bp : ∃ (c k : ℤ), (c * ↑t + b)^2 - 1 = k * ↑t,
    { cases h_ap with l hl,
      cases h_ab with s hs,
      use s,
      use l,
      rwa ← hs, },
      -- To show that in the expansion of `(c * ↑t + b)^2` , all terms with `↑t` can be grouped together
      -- and be expressed just as `g * ↑t` for some integer `g`. 
    have helper : ∃ (c k : ℤ), b ^ 2 - 1 = k * ↑t - c ^ 2 * ↑t ^ 2 - 2 * c * ↑t * b,
    { cases h_bp with x hx,
      cases hx with y hy,
      rw add_pow_two (x * ↑t) (b) at hy,
      use x, 
      use y,
      apply eq_sub_of_add_eq',
      apply eq_sub_of_add_eq',
      rw (mul_pow x ↑t 2).symm,
      rw ← add_assoc,
      rw add_sub,
      nth_rewrite 1 (mul_assoc),
      exact hy,},
    have h_bp' : ∃ (g : ℤ), b^2 - 1 = g * ↑t,
    { cases helper with c hc,
      cases hc with k hk,
      use (k - c ^ 2 * ↑t - 2 * c  * b),
      rw mul_sub_right_distrib,
      rw mul_sub_right_distrib,
      rw hk,
      ring, },
    -- Since `↑t` divides `b^2 - 1`, we can say that `b^2 ≡ 1 [ZMOD ↑t]`.
    rw ← dvd_iff_exists_eq_mul_left at h_bp',
    have h_bp_mod : 1 ≡ b^2 [ZMOD ↑t],
    { apply int.modeq_of_dvd, 
      exact h_bp',},
    exact h_bp_mod.symm,},
end


#lint
/-While there are the `unused_arguments` linter reports but I feel that they are really
important to be a part of definition to maintain coherency, hence I did not remove them. -/


import data.zmod.basic
import tactic
import data.nat.gcd
import number_theory.zsqrtd.gaussian_int
import number_theory.arithmetic_function
import number_theory.lucas_lehmer
import algebra.big_operators.order
import data.nat.prime


/- Progress Report
1) I've shown a^(p^2+p+1)=a^3 mod p is p is prime NO SORRYS

2) a < b → 2*a < 2*b  NO SORRYS

3) 2^n < 2^(n+1) n ∈ ℕ NO SORRYS

4)  r ∈ ℕ r < 2^r NO SORRYS

5) 1< n *1 → 0 < n NO SORRYS

6) a < b → 2^a < 2^b 1 SORRY ORDERED SUB??

7) c m: ℕ, m>1, c > m , m ∣ c → c not prime

8) m r c n:ℕ, r > 1,c= 2^r + 1 then c.prime → r=2^n :=

-/


lemma a_square (x a b :ℕ):
x^(a+b) = x^(a) * x^(b) :=
begin
  exact pow_add x a b,
end

-- This is our first main goal of three 
-- That a^(p^2+p+1) ≅ a^3 mod p where p is prime

lemma a_cong_mod_p (p c b: ℕ) (a: zmod p) [ fact p.prime] :
a^(p^2 + p + 1) = a^3  :=
begin
  have h1: a=0 ∨  a≠0,
    {exact em (a = 0)},
  -- this allows us to split the cases into a being = 0 modp or ≠ 0 modp
  cases h1 with b hb,
    {rw b,
    simp},
  -- we split the first case so a=0 modp and solve this pretty easily
  rw [add_assoc,pow_add a (p^2) (p+1),pow_add a p 1],
  -- this allows us to split a^(p^2+p+1)
  have h10: (p-1+1)=p,
    {apply nat.sub_add_cancel,
    apply nat.prime.pos,
    apply fact.out},
  -- This allows us to convert p to p-1+1
  rw [pow_two,pow_mul'],
  -- this converts a^p^2 to (a^p)^p
  have h5: a^p =a^(p-1+1),
    {rw h10},
  -- here we get a formula for a^p
  have h6: a^(p-1+1) =a,
    {rw [pow_add a (p-1) 1,zmod.pow_card_sub_one_eq_one],
    simp,
    apply hb},
  --here we using fermat's little theorem to show a^p=a
  rw [h5,h6,h5,h6],
  --we constantly apply a^p =a
  by ring,
  --we simplify
end

-- Now we move onto our second main problem which is
--to show if 2^r +1 is prime then r=2^n

-- this lemma uses omega so I took it out of the code for clarity and so
-- it didn't slow down the larger lemma as much
lemma two_mul_less (a b :ℕ) (h:a<b) : 2*a < 2*b :=
begin
  omega,
end
--Here we use induction to show 2^n < 2^n+1
lemma n_great_nplusone (n:ℕ) : 2^n < 2^(n+1):=
begin
  induction n with d hd,
  {simp},
  -- we apply induction and solve n=0
  rw [← nat.add_one,pow_add 2 d 1, pow_add 2 (d+1) 1,(by ring:  2^d*2^1 = 2*2^d),(by ring:  2^(d+1)*2^1 = 2 * 2^(d+1))],
  -- we change succ to +1 (I find this personally easier to deal with)
  -- we also separate the indices into multiplication
  -- we use ring to rearrange 
  exact two_mul_less (2^d) (2^(d+1)) (hd),
  -- here we apply our above lemma if a < b 2*a < 2*b
end

--here our lemma is r < 2^r
lemma two_to_r_greater_r (r : ℕ) :
r < 2^r :=
begin
  induction r with d hd,
  simp,
  -- again we do induction and 
  have h0: 1 ≤ d ∨ d<1,
    {exact le_or_lt 1 d},
  --here we split by the cases that 1≤d or 1>d
  rw ← nat.add_one,
  -- I change succ to +1 once again
  cases h0 with b hb,
  rw pow_add 2 (d) 1,
  -- here we separate the indices again
  have h2: 2*d < 2^d *2,
    {linarith},
  rw two_mul at h2,
  rw pow_one,
  linarith,
  -- we rewrite 2^1=2 and 2*d=d+d and simplify
  have h4: d=0,
    linarith,
  rw h4,
  simp,
  -- we change d<1 to d=0 and simp solves this
end

-- here we show if 1 < n*1 then 0 < n
--this seems trivial but was a necessary lemma for later on
lemma adjhf (n :ℕ) (h:1 < n * 1 ): 0 < n :=
begin
  refine lt_trans zero_lt_one _, 
  -- here we rewrite our goal to be 1 < n
  rwa mul_one at h, 
  -- here we use n*1=n and apply the hypothesis
end

--here we use the general a < b → 0 < b -a with 2^a and 2^b
lemma a_great_b1 (a b : ℕ) : 2^a<2^b ↔ 0< 2^b-2^a :=
begin
  exact tsub_pos_iff_lt.symm,
end

-- this is what we've been slowly building too and is our first large lemma
--of part two
-- in this lemma I used a lot of hypothesises as they were mostly solved by linarith,
lemma a_great_b (a b : ℕ) : a<b → 2^a < 2^b :=
begin
  intro h,
  have h2: a +1 ≤ b,
    {linarith},
  have h2: a ≤ b,
    {linarith},
  rw [a_great_b1,← pow_mul_pow_sub 2 h2],
  --here we use the above lemma and this gives us 0 < 2^a * 2^(b-a) -2^a
  have h3: 1 ≤ b-a,
    {linarith},
  have h0: b-a < 2^(b-a),
    {apply two_to_r_greater_r (b-a)},
  -- these are a couple of hypothesises to help us later
  have h4: 2^(0) < 2^(b-a)*2^0,
    {rw (by ring: 2^(b-a)*2^0=2^(b-a)),
    simp,
    linarith},
  -- this gives us 2^0 < 2^(b-a)*2^(0)
  have h5: 0 < 2^(b-a),
    {apply adjhf,
    apply h4},
    -- we apply the lemma 1<1*n → 0< n and our above hypothesises
  have h6: 2^(b-a) = 2^(b-a)*2^0,
    {apply pow_add 2 (b-a) 0},
  have h1: 1 < 2^(b-a),
    {linarith},
  have h7:  (2^a)*(2^(b-a)-1)= 2^a * 2^(b-a) - 2^a,
    {have h8: 2^a = 2^a*1,
      {simp},
    nth_rewrite 2 h8,
    exact mul_tsub (2^a) (2^(b-a)) 1},
  --this gives us a few more hypothesises to use now
  rw ← h7,
  have h9: 0<2^a,
    {simp},
  have h10: 0< (2^(b-a)-1),
    {linarith},
  nlinarith,
  -- here we use that each component is > 0 and hence so is their product
end

-- this is again a useful lemma for later 
lemma hhhhh (a b n : ℕ) : n*(b-a) = n*b-n*a :=
begin
  exact mul_tsub n b a,
end

--this is the same as a_great_b1 but more general
lemma a_great_b4 (a b : ℕ) : a<b ↔ 0< b-a :=
begin
  exact tsub_pos_iff_lt.symm,
end

-- this lemma is used later to show numbers aren't prime in order to get a contradiction
lemma c_not_prime (c m: ℕ)(h0: m>1)(h1: c > m) (h2: m ∣ c) :
¬ c.prime :=
begin
  rw nat.prime_def_lt',
  -- I rewrote the defintion of prime
  intro h,
  have hn: 2≤m,
    {linarith},
  cases h with d hd,
  -- separate our definition of prime into different hypothesises 
  specialize hd m hn h1,
  -- here we use that m∣ c and ¬ m∣c to get a contradiction
  exact hd h2,
end

--In the end I didn't need this lemma, however I spent a lot of time on it,
-- so please enjoy
-- This shows is we have n is odd 3∣ 2^n +1 
lemma three_dvd_eq (r b :ℕ) : 3∣ (2^(2*r+1) + 1) :=
begin
  induction r with h he,
  {simp},
  -- here I use induction and simp the case n=0
  rw [← nat.add_one,(by ring :(2*(h + 1)+1) = 2*h + 1 + 2 ),pow_add 2 (2*h +1) 2],
  -- here we rearrange our goal into a desired form
  have h3: 3 ∣ (2 ^ (2 * h + 1) + 1)* (2^2),
    {exact dvd_mul_of_dvd_left he (2^2)},
  have h4:  (2 ^ (2 * h + 1) + 1)* 2^2 -3 = 
  2 ^ (2 * h + 1) * 2 ^ 2 + 1,
    {by ring_nf},
  have h5: 3∣3,
    {simp},
  set b:= (2 ^ (2 * h + 1) + 1)* 2^2 with r,
  --here we set b to be the above for simplicity
  have h8: 1 < 2 ^ (2 * h + 1) +1,
    {simp},
  have h9: 4 < (2 ^ (2 * h + 1) +1)* (2^2),
    {linarith},
  have h7: 3 ≤ b,
    {linarith},
  have h6 : 3 ∣ b -3,
    {apply nat.dvd_sub h7 h3 h5},
    -- here we use that if 3∣b and 3∣3 then 3∣ b-3 as 3≤b
  rw ← h4,
  apply h6,
  -- we apply all the hypothesesis that we've created together and get our end result
end

open_locale big_operators
open finset 

-- this lemma is the key to our proof that if r isn't written as 2^n then 2^r +1 cannot be prime
-- What i want to do here is show i can use x^(r-1)-x^(r-2)+...+1
--def poly_sum (r x:ℕ) : ℤ  :=
--((range r).map (λ m, ((-1)^m)*x^m)).sum


lemma divide_d (x r:ℕ) (h: odd r): x +1 ∣ x^r +1 :=
begin
  sorry,
end

-- Now need to show if n = a* r where r is odd and ≥ 3 then 2^n +1 isn't prime
lemma n_not_2_to_r_not_prime2 (r c n a : ℕ ) (h0: 1 < r)(h1: n=a*r) (h2: c=2^n +1) (h3: odd r) (h4: 0<a) :
¬ c.prime :=
begin
  rw nat.prime_def_lt',
  intro h,
  -- we rewrite our definition of prime again
  have h5: 2≤ 2^a +1,
    {have h6: a < 2^a,
      {apply two_to_r_greater_r},
    have h7: 1 < 2^a,
      {linarith},
    linarith},
  -- here are some hypothesises we need later on
  have h6: 2^a +1 < c,
    {rw h2,
    simp,
    apply a_great_b,
    nlinarith},
  -- we use this later as if 2^a +1 =c this doesn't necessarily mean c isn't prime
  cases h with d hd,
  specialize hd (2^a +1) h5 h6,
  --here we split our one large hypothesis into more manageable ones
  have h17: 2^a +1 ∣ c,
    {set x:= 2^a with e,
    rw [h2,h1,pow_mul,←e],
    apply divide_d,
    -- here we apply our previous lemma that x+1 ∣ x^r +1 for x =2^a
    apply h3},
  exact hd h17,
  -- here we apply our contradiction that 2^a +1 ∣ c and ¬ 2^a +1 ∣ c 
end

lemma a1 (r : ℕ) (h0: 0 < r) : ∃ n m : ℕ, odd m ∧ r = (2 ^ n) * m := 
begin
  have h1: even r ∨ odd r,
    {apply nat.even_or_odd},
  cases h1 with d hd,
  {induction r with f hf,
  {use 1,
  use 0,
  split,
  {simp,
  linarith},
  simp},
  --rw he,
  --simp,
  rw ← nat.add_one at h0,
  rw ← nat.add_one at d,
  use 1,
  --use (2^(n-1)*m +1),
  sorry},
  use 0,
  use r,
  split,
  {apply hd},
  simp,
end 

lemma assahs (a:ℕ)(h: a +1 ≠ 1): a ≠ 0 :=
begin
  exact ne_of_apply_ne (λ (a : ℕ), a + 1) h,
end 

lemma afg (d:ℕ) (h:d ≠ 0): 0<d :=
begin
  exact zero_lt_iff.mpr h,
end
lemma g_great_1 (g: ℕ)(h: g≠1)(h1: odd g) : 1 < g :=
begin
  cases h1 with d hd,
  rw hd,
  rw hd at h,
  have h2: 2*d≠ 0,
    {apply assahs,
    apply h},
  have h3: d≠ 0,
    {exact right_ne_zero_of_mul h2},
  simp,
  exact zero_lt_iff.mpr h3,
end


-- here we apply our previous lemmas to show that if c is prime r =2^n
lemma two_to_the_r_prime (m r c :ℕ) (h: 1 < r) (h0:c= 2^r + 1)(h1: c.prime) (h2: odd m): ∃n : ℕ, 
r=2^n :=
begin
  have h19: ∃ j k : ℕ, odd k ∧ r = (2 ^ j) * k,
    {apply a1,
    linarith},
  cases h19 with f hf,
  cases hf with g hg,
  cases hg with i hi,
  use f,
  have h5: g =1 ∨ g≠ 1,
    {exact em (g=1)},
  cases h5 with e he,
  {rw e at hi,
  rw hi,
  simp},
  exfalso,
  have h2: ¬ c.prime,
    {apply n_not_2_to_r_not_prime2 g c r (2^f),
    {apply g_great_1,
    apply he,
    apply i},
    {apply hi},
    {apply h0},
    {apply i},
    simp},
    -- here we show if r=(2^n)*m then c isn't prime
  exact h2 h1,
  -- we apply our contradiction 
end

--Here we've completed our 2nd part of the project
variable (n: ℕ ) 


-- Perfect Numbers
-- Even number is perfect if it has the form
-- 2^(p-1)*(2^p -1) where 2^p -1 is prime

definition perfect (n : ℕ ): Prop :=
(∑ d in nat.proper_divisors n, d=n) ∧ n ≠ 0
-- this is our definition of perfect

lemma perfect_eq_prop_divisors (n: ℕ) (h1: n ≠ 0) :
(∑ d in nat.proper_divisors n, d=n) ↔ perfect n 
:= 
begin
  rw perfect,
  split,
  {intro g,
  split,
  {exact g},
  exact h1},
  intro f,
  cases f with b hb,
  apply b,
end
--Here we see that n is perfect iff the sum of proper divisors is n


lemma divisors_sum_and_proper :
∑ d in nat.divisors n, d = ∑d in nat.proper_divisors n, d+n :=
begin
  rw nat.sum_divisors_eq_sum_proper_divisors_add_self,
end
-- this shows the sum of divisors of n = sum of proper divisors of n +n

lemma perfect_eq_divisors (h1: n≠0) :
(∑ d in nat.divisors n, d=2*n) ↔ perfect n 
:= 
begin
  split,
  {intro h,
  rw [divisors_sum_and_proper, two_mul n ,(add_left_inj n)] at h,
  -- here we rewrite our definition of divisors into proper divisors
  rw ← perfect_eq_prop_divisors,
  -- here we use that if perfect sum of proper divisors = n
  {apply h},
  apply h1},
  -- we apply the necessary hypothesises to this
  intro h,
  rw [divisors_sum_and_proper,two_mul n,(add_left_inj n),perfect_eq_prop_divisors],
  -- here we do the same in the other direction
  {apply h},
  apply h1,
  -- this gives the necessary solution
end
-- this show us another definition of perfect n ↔ sum of divisors = 2n 

-- Two doesn't divide any mersenne primes
-- We use this late to show that 2^(n-1) and 2^n -1 are coprime
lemma two_non_divisor (n : ℕ) (h: 0<n): ¬ 2 ∣  2^n -1 :=
begin
  rw [← even_iff_two_dvd,← nat.even_succ,← nat.add_one,nat.sub_add_cancel, even],
  -- this chances our goal to ∃ k s.t. 2^n = 2*k
  -- and that 1 ≤ 2^n 
  {use 2^(n-1),
  have h1: 2=2^1 ; simp,
  nth_rewrite 1 h1,
  rw [← pow_add 2 1 (n-1),← (by ring_nf: n-1+1=1+(n-1)), nat.sub_add_cancel],
  linarith},
  -- here we have to do a little work to show 2^n = 2*2(n-1) 
  -- this is because n-1+1 poses some problems in ℕ 
  have h3: 1≤n,
    {linarith},
  have h4: n < 2^n,
    {apply two_to_r_greater_r},
  linarith,
  -- this shows that 1≤ 2^n
end 

notation `σ ` n := ∑ d in nat.divisors n, d

lemma my_sigma_eq_sigma : (σ n) = nat.arithmetic_function.sigma 1 n :=
begin
  simp,
end 
-- this is our notation for sigma
-- and our proof that our sigma is the same as the lean sigma

namespace nat

lemma multiplicative_sigma (n m c : ℕ ) (h0: n.coprime m) : 
(σ n*m) = (σ n) * (σ m):=
begin
  rw my_sigma_eq_sigma,
  have h1: (σ n) = nat.arithmetic_function.sigma 1 n,
    {simp},
  rw h1,
  have h2: (σ m) = nat.arithmetic_function.sigma 1 m,
    {simp},
  rw h2,
  have h3: arithmetic_function.is_multiplicative (arithmetic_function.sigma 1),
    {apply arithmetic_function.is_multiplicative_sigma},
  apply arithmetic_function.is_multiplicative.map_mul_of_coprime,
  {apply h3},
  apply h0,
end
--here we use that our sigma = lean sigma and that lean sigma is multiplicative
-- this shows that sigma is multiplicative
end nat
-- As I'm thinking of adding this to the API I spent a lot of time
-- making this as concise as possible hence why it looks much more professional
-- than my other proofs.
lemma mem_pair_iff  (p a: ℕ) : a ∈ ({1, p}: finset ℕ) ↔  (a =1 ∨ a =p):=
begin
  split,
  {intro g,
  rw [insert_eq 1 {p}, mem_union] at g,
  -- here we use that a∈{1,p} means a∈ {1} or a∈{p}
  cases g with e he,
  {rwa mem_singleton at e,
  left; assumption},
  rw mem_singleton at he,
  right; assumption},
  -- we take these two cases and solve them by our assumption
  intro f,
  cases f with d hd,
  {simp [d]},
  simp [hd],
  -- we take both cases and show that they're in the set {1,p}
end

--Here we use the above to show the nat divisors of p are {1,p}
lemma prime.divisors (p : ℕ) (h: p.prime) : nat.divisors p = {1, p} := 
begin
  ext,
  split,
  {intro f,
  rw nat.prime_def_lt'' at h,
  -- we rewrite our definition of prime
  cases h with b hb,
  have h1: a∣p,
    {rw nat.mem_divisors at f,
    cases f with e he,
    apply e},
  specialize hb a h1,
  -- we specialize our defintion of prime into smaller hypothesises
  cases hb with d hd,
  {simp [d]},
  simp [hd]},
  -- here we show 1 and p are members of {1,p}
  intro g,
  have h3: 0 <p,
    {apply nat.prime.pos,
    apply h},
  rw nat.mem_divisors,
  -- here we rewrite the divisors of p
  split,
  {have h4: a=1 ∨ a=p,
    {rw ← mem_pair_iff,
    apply g},
  cases h4 with e he,
  -- here we split into a=1 or a=p
  {rw e,
  simp},
  rw he},
  linarith,
end

-- here we prove that sigma(p) =p+1
-- this is key in our final proof as we need σ(2^n -1) =2^n
lemma prime_sigma (p: ℕ ) (h0: p.prime) : (σ p) = p+1:=
begin
  rw prime.divisors,
  {rw [insert_eq 1 {p},finset.sum_union],
  -- here we rewrite our divisors into sums
  {simp,
  linarith},
  simp,
  have h1: 2≤p,
    {apply nat.prime.two_le,
    apply h0},
  linarith},
  -- here we use that as 2≤ p p≠ 1
  apply h0,
end

-- this lemma is that any odd number c is coprime to 2
lemma odd_coprime_two (c: ℕ) (h0: odd c) :  c.coprime 2 :=
begin
  cases h0 with d hd,
  have h2: (2*d +1).coprime 2, 
    {apply nat.coprime.symm,
    rw nat.coprime_mul_left_add_right,
    apply nat.coprime_one_right},
    -- here we apply a few of the coprime identites from lean
  rwa hd,
end

-- here we show that d is odd
lemma d_odd (h: 1≤n): odd (2^n -1) :=
begin
  have h1: 2^n -1 = 2^1*2^(n-1) -1,
    {rw ← pow_add 2 1 (n-1),
    have h2: 1+(n-1) =n-1+1,
      {by ring_nf},
    rw h2,
    rw nat.sub_add_cancel,
    apply h},
  rw h1,
  rw pow_one at h1,
  have h3: ¬ 2 ∣ 2^1*2^(n-1) -1,
    {rw pow_one,
    apply nat.two_not_dvd_two_mul_sub_one,
    simp},
  rw nat.two_dvd_ne_zero at h3,
  rwa nat.odd_iff,
end 

-- we apply the above two lemmas to show d is coprime to 2
lemma two_coprime_d (m n c d : ℕ)(h: 1≤n)(h0: d=2^n-1) : d.coprime 2 :=
begin
  have h1: odd d,
    {rw h0,
    apply d_odd,
    apply h},
  apply odd_coprime_two,
  apply h1,
end

-- we show that d is coprime to 2^(n-1) as d is coprime to 2
lemma gcd_perfect (m n c d:ℕ)(h2: 1≤ n)(h0: c= 2^(n-1)) (h1: d =2^n -1) (h: d.prime): c.coprime d :=
begin
  apply nat.coprime.symm,
  rw h0,
  apply nat.coprime.pow_right,
  apply two_coprime_d n,
  {use n},
  {apply h2},
  {apply h1},
end

--divisor of prime power is a prime pwer
--dvd_prime_power


namespace nat
open arithmetic_function finset
open_locale arithmetic_function

-- here is the lean lemma for showing σ(2^k)=2^(k+1)-1
lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = 2^(k+1)-1 :=
by simpa [prime_two, ← geom_sum_mul_add 1 (k+1)]

end nat
-- here we show that our sigma 2^n = 2^(n+1)-1
lemma my_sigma_two_pow_eq_mersenne (n:ℕ) : (σ 2^n) = 2^(n+1)-1 :=
begin
  rw ← nat.sigma_two_pow_eq_mersenne_succ,
  simp,
end
-- here we specialize for 2^(n-1)
lemma sigma_two_power (h: 1≤ n): (σ (2^(n-1))) = 2^n -1 :=
begin
  rw my_sigma_two_pow_eq_mersenne,
  rw nat.sub_add_cancel,
  apply h,
end

-- here we use multiplicativity to show that σ(2^(n-1)*(2^n-1)) = 2^n * (2^n-1)
lemma prime_implies_perfect (h0: 1 <n)(h: nat.prime (2^n -1)): (σ (2^(n-1)*(2^n -1))) = (2^n)*(2^n-1) :=
begin
  rw [nat.multiplicative_sigma, sigma_two_power,prime_sigma,nat.sub_add_cancel],
  {linarith},
  have h3: 2^1 < 2^n,
    {apply a_great_b,
    apply h0},
  {linarith},
  {apply h},
  {linarith},
  {use n},
  {apply gcd_perfect n n,
  {linarith},
  {refl},
  {refl},
  {apply h}},
end

-- this is our end result and shows us that if 2^n -1 is prime
-- then 2^(n-1)*(2^n -1) is perfect
lemma mersenne_primes (h0: 1<n) (g: nat.prime (2^n -1)): perfect (2^(n-1)*(2^n -1)) :=
begin
  rw ← perfect_eq_divisors,
  {rw prime_implies_perfect,
  {rw ←  mul_assoc,
  have h5: 2=2^1,
    {simp},
  nth_rewrite 2 h5,
  rw ← pow_add 2 1 (n-1),
  have h2: n -1 +1 = 1+ (n-1),
    {by ring_nf},
  rw [← h2, nat.sub_add_cancel],
  linarith},
  {apply h0},
  {apply g}},
  {simp,
  intro h,
  cases h with d hd,
  have h1: 0 < 2^(n-1),
    {simp},
  have h2: 2^(n-1) ≠ 0,
    {linarith},
  exact h2 d,
  have h3: 2^1 < 2^n,
    {apply a_great_b,
    apply h0},
  linarith},
end


--Here is my Appendix
--This is code I couldn't quite bring myself to delete but isn't actually
-- relevant to the prject I've created. For more details please see my project Word document.

-- The code is commented out as it contains a sorry in the first lemma

/-
--here we want to show that if m∣ 2^n and 1 < m→ 2∣m 
lemma two_dvd_2_power (m n: ℕ)(h: ∀ m : ℕ, m∣2^n )(h0: m>1): 2∣m :=
begin
  sorry,
end

-- this proof ended up being unnecessary but alas i spent hours doing it
 -- here we show that if m∣c then ¬ m∣d for c=2^(n-1) d=2^n-1
lemma m_dvd_c_not_d (m n c d:ℕ)(h0: c= 2^(n-1)) (h1: d =2^n -1) (h: d.prime) (h2: ∀ m : ℕ, m∣c) (h3: 1< m) (h4: 1< n):
 ¬ m∣d :=
begin
  have h5: 2∣m,
    {apply two_dvd_2_power m (n-1),
    rw ← h0,
    intro m,
    apply h2,
    apply h3},
  -- here we show 2∣m 
  have h6: ¬ 2 ∣ d,
    {rw h1,
    apply two_non_divisor,
    linarith},
  -- we show here ¬ 2∣d
  cases h5 with e he,
  rw he,
  have h7: 2*e ∣ d ∨ ¬ 2*e ∣d,
    {exact em (2*e ∣ d)},
  -- here we show that either 2*e∣d or ¬ 2*e∣d
  cases h7 with f hf,
  {exfalso,
  have h8: 2∣d,
    exact dvd_of_mul_right_dvd f,
  exact h6 h8},
  -- here we show if 2*e ∣ d we get a contradiction
  apply hf,
  -- this shows that ¬ m∣d
end

-- this is outside the proof again so as to not slow things down
lemma add_sub_comm2  : n+n-2-n = n-2 :=
begin
  omega,
end

--here we show that if 2 < n → n < 2*(n-1)
-- we use this in the proof of m_dvd)d_not_c
lemma asghjda (h: 2< n): n < 2*(n-1) :=
begin
  rw [nat.mul_sub_left_distrib 2 n 1, mul_one,(by ring : 2*n =n+n),a_great_b4,add_sub_comm2],
  rwa ← a_great_b4,
end

lemma d_dvd_c_d_lesseq_c (c d : ℕ ) (h0: 0< c) (h: d∣c ): d≤ c :=
begin
  apply nat.le_of_dvd (h0)(h),
end

-- this proof ended up being unnecessary but alas i spent hourse doing it
--here we show that if m∣d then ¬ m∣c
lemma m_dvd_d_not_c (m n c d:ℕ)(h0: c= 2^(n-1)) (h1: d =2^n -1) (h: d.prime) (h2: m∣d) (h3: 1< m) (h4: 1< n): ¬ m∣c :=
begin
  have h4: m=1 ∨ m=d,
    apply nat.prime.eq_one_or_self_of_dvd,
    apply h,
    apply h2,
  --here we have that m=1 ∨ m=d
  have h5: m=d,
    cases h4 with e he,
    exfalso,
    linarith,
    apply he,
    rw h5,
  -- we then show m=d
  have h9: 2=2^1,
    {simp},
  have h6: c< d,
    {rw [h0,h1],
    have h7: 2* 2^(n-1)< 2*(2^n -1),
      {have h8: 2*2^(n-1) = 2^n,
        {nth_rewrite 0 h9,
        rw ←  pow_add 2 1 (n-1),
        have h10: n -1 +1 = 1+ (n-1),
          by ring_nf,
        rw[← h10,nat.sub_add_cancel],
        linarith},
      rw h8,
      apply asghjda,
      nth_rewrite 0 h9,
      apply a_great_b,
      linarith},
    linarith},
  -- here we show that c< d
  intro g,
  have h12: 0< c,
    rw h0,
    simp,
  have h11: d≤ c,
    {apply nat.le_of_dvd (h12)(g)},
  -- here we get a contradiction that c< d but also d≤ c 
  linarith,
end
-/
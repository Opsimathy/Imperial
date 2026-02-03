/-
Project 1 - Formalising Mathematics 
-/

import tactic
import data.nat.pow
import data.int.basic

open nat

open int

/-!
# Year 1 Past Examination Paper - 1174449
Based on Group Theory.

## Aim: For a group G
Define:
1. G is abelian 
2. G is cyclic 
Justify: Every cyclic group is abelian

We will start by first defining a group:

## Definition of a Group
-/

/-- A `group` structure on a type `G` under `*` is multiplication, identity and inverse,
so we define them: -/
class mygroup (G : Type)
extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(mul_one : ∀ a : G, a * 1 = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)
(mul_inv_self : ∀ a : G, a * a⁻¹ = 1)

/-
To drop the `mygroup` prefix, we move to a namespace called `mygroup`.
-/

namespace mygroup

variables {G : Type} [mygroup G] -- defining a group `G` in the namespace 

/-!
## Definition of an Abelian Group

We will now introduce a structure called `mul_com` which will contain the
definition of commutativity.
-/

/-- An `abelian group` structure on a type `G` is commutative along with
the definition of a group having regular axioms,
so we define them: -/
class abel_grp (G : Type)
extends mygroup G : Type:=
(mul_com : ∀ a b : G, a * b = b * a)

/-
We will move to a namespace called 'abel_grp'
-/

namespace abel_grp

/-- Introducing an abelian group -/
variables {H : Type} [abel_grp H]

/-
We will now try explicitly stating  and proving `mul_com` as a lemma.
-/

/-- Let `a,b` be elements of `H`, which is an abelian group. -/
variables (a b : H)

/-- Proving commutativity in H to show it is abelian: -/
lemma mul_comu (a b : H) : a * b = b * a :=
begin
exact abel_grp.mul_com a b, --by the field stated above
end

end abel_grp

-- Hence, we have defined abelian groups.

/-
We will now define non negative powers and integer powers for cyclic groups.
We start off by defining `npow` function for non negative powers as it is easier to work around
them and they will later help us prove many things about integer powers.
-/

/-- We define the function of group `G` raised to the power (which is a non negative) as : -/
def npow (g : G) : ℕ → G
| 0 := 1
| (n+1) := npow n * g

/-- We now extend to defining integer powers for element `g ∈ G` : -/
def zpow (g : G) : ℤ → G
| (int.of_nat n) := npow g n
| (int.neg_succ_of_nat n) := (npow g (n + 1))⁻¹

/-
To avoid confusion between `npow` and `zpow`, we will not declare any instance and avoid 
notation `^`. For any `g ∈ G` and `a ∈ ℤ` or `a ∈ ℕ`, we will refer to `g^a` as 
`zpow g a` or `npow g a` respectively, depending on the context.
-/

/-!
Once we have the integer power defined, we can now move to defining cyclic groups.
## Definition of cyclic groups
-/
/-- A group `G` is called cyclic if there exists an element `g : G` such that for some 
`n : ℤ` every element of `G` can be written as `zpow g n`. -/
class cyclic_grp (G : Type)
extends mygroup G : Type :=
(grp_generator [] : ∃ g : G, ∀ a : G, ∃ n : ℤ , a = zpow g n)

/-
A new perspective : Earlier I was dealing with integer powers needed to define cyclic groups by creating
all lemmas regarding exponential properties from the scratch. However, thanks to the Xena Project discord 
channel for providing me a new perspective into dealing with integers by breaking them down into natural 
numbers and starting with the main theorem first and then proving the building lemmas so that the proof of
the third part of the project that 'all cyclic groups are abelian' gets easier. 
-/

-- To avoid using the prefix `mycyclic_grp` we move to the namespace :
namespace cyclic_grp

/- 
We will now state some important properties of groups needed to define commutatativity in cyclic groups. 

The most important property that will help us in dealing with integer powers, when 
proving commutativity for cyclic groups, is Socks-Shoes Property in Group Theory. To define that, we 
will need:
-/
--We will tag some lemmas with @[simp] attribute so they can simplify some bits of proofs for us.
attribute [simp] one_mul mul_assoc inv_mul_self 

/-- To prove: Left cancellation law -/
lemma left_cancel (a b c : G) (cancellation : a * b = a * c) : b = c := 
begin
  rw ← one_mul b,
  rw ← inv_mul_self a,
  rw mul_assoc,
  rw cancellation,
  rw ← mul_assoc,
  rw inv_mul_self,
  rw one_mul,
end

/-- To prove right cancellation law-/
lemma right_cancel (a b c : G) (cancellation : a * b = c * b) : a = c := 
begin
  rw ← mul_one a,
  rw ← mul_inv_self b,
  rw ← mul_assoc,
  rw cancellation,
  rw mul_assoc,
  rw mul_inv_self,
  rw mul_one,
end

/-- To show: `a * (a⁻¹ * b) = b` -/
lemma inv_left_cancel ( a b : G): a * (a⁻¹ * b) = b :=
begin
  rw [←mul_assoc, mul_inv_self, one_mul],
end

/-- Socks Shoes Property which states that for group elements `a` and `b`, 
`(a * b)⁻¹ = b⁻¹ * a⁻¹` -/
@[simp] lemma socks_shoes ( a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply left_cancel (a * b),
  rw mul_assoc,
  rw mul_assoc,
  rw inv_left_cancel,
  rw mul_inv_self,
  rw ← mul_assoc,
  rw mul_inv_self (a*b),
end

/- 
While, we do not require the above lemmas for proving 
g^m * g^n = g ^ n * g^m, defining them right after defining cyclic groups and before 
further defining lemmas seemed like an ideal place.
-/

-- introducing variables needed to prove lemmas regarding powers of non negative numbers.
variables (g : G) (n : ℕ) (m : ℕ) (o : ℕ)

#check npow g ----- is an element of `G`

-- To show: any element of `G` raise to the power 0 = 1
@[simp]lemma pow_zero : npow g 0 = 1 := rfl

-- To show: `npow g (n+1) = npow g n * npow g 1 = npow g n * g`
@[simp]lemma pow_succ: npow g (n.succ)= npow g n  * g:= rfl

lemma g_one : npow g 1 = g := 
begin
  simp,
end 

/--
Though these lemmas are not required to prove cyclic groups, yet they helped in building 
the foundation needed to prove lemmas for integer powers as well as helped in defining 
the outline of the code needed to prove that all cyclic groups are abelian.

lemma add_succ: npow g (m + n.succ) = npow g (m+n).succ := rfl

-- To show: `npow g (m+n) = npow g m * npow g n`
@[simp]lemma pow_add: npow g (m+n) = npow g m * npow g n :=
begin
induction n with d hd,
simp,
rw mul_one,
simp,
rw add_succ,
rw pow_succ,
rw [hd, mul_assoc],
end

-- To show: `npow g m * npow g n = npow g n * npow g m`
@[simp]lemma pow_comm: npow g m * npow g n = npow g n * npow g m :=
begin
induction n with d hd,
simp,
rw mul_one,
rw [← pow_add, add_comm, pow_add],
end
-/

-- introducing variables needed to prove lemmas regarding integer powers.
variables (h : G) (a : ℤ) (b : ℤ) (p : ℕ)

#check zpow h n ----- is an element of `G`

-- Introducing `pow_neg` and `pow_pos` to help make terms simpler.
@[simp]lemma pow_neg : zpow g (int.neg_succ_of_nat p) = (zpow g (p + 1))⁻¹ := rfl

@[simp]lemma pow_pos : zpow g (int.of_nat p) = zpow g (p) := rfl

-- To show that any element raise to the power `0` , i.e., `zpow g 0 = 1`
@[simp]lemma pow'_zero : zpow g (0 : ℤ) = 1 := rfl

-- To show: `npow g p * g = g * npow g p` for `p ∈ ℕ`
@[simp] lemma comm_gwn: npow g p * g = g * npow g p :=
begin
  induction p with d hd,
  rw pow_zero,
  rw mul_one,
  rw one_mul,
  simp,
  rw ← mul_assoc,
  rw hd,
  rw ← mul_assoc,
  rw mul_assoc,
  rw hd,
  rw ← mul_assoc,
end

-- To show that power of a non negative number in `ℕ` is same as that in `ℤ` 
@[simp]lemma npow_zpow : npow g p = zpow g p := rfl 

/-- To show commutativity of `g` with some element of cyclic group in `G` 
represented in the form of `g` raised to an integer power `a` -/
@[simp]lemma comm_gwi: zpow g a * g = g * zpow g a :=
begin
  induction a with d hd,
  simp,
  rw ← npow_zpow,
  rw comm_gwn,
  simp,
  rw ← int.coe_nat_succ,
  rw ← npow_zpow,
  rw pow_succ,
  rw socks_shoes,
  rw ← mul_assoc,
  rw mul_inv_self,
  rw one_mul,
  rw ← socks_shoes,
  rw comm_gwn,
  rw socks_shoes,
  rw mul_assoc,
  rw inv_mul_self,
  rw mul_one,
end 

/- 
This lemma by far, seems the most obvious and easiest one, however, the tricky part here
is showing something too obvious which is g = npow g 1
-/
/-- To show: `zpow g (-1) = g⁻¹` -/
lemma inv_pow: zpow g (-1) = g⁻¹ := 
begin
  apply left_cancel (g),
  rw mul_inv_self,
  rw ← comm_gwi,
  change (npow g (1))⁻¹ * g= 1,
  apply left_cancel (npow g (1)),
  rw ← mul_assoc,
  rw mul_inv_self,
  rw mul_one,
  rw one_mul, 
  rw g_one,
end 

/-- To show: `zpow g a * g = zpow g (a+1)` -/
lemma zpow_one : zpow g a * g = zpow g (a+1) := 
begin
  cases a,
  simp,
  rw ← npow_zpow,
  rw ← comm_gwn,
  change npow g (a+1) = zpow g (↑a + 1),
  rw npow_zpow,
  simp,
  induction a with d hd,
  rw neg_succ_of_nat_eq,
  simp,
  rw inv_pow,
  rw mul_inv_self,
  rw neg_succ_of_nat_eq,
  rw neg_succ_of_nat_eq at hd,
  sorry,
end

/-- To show: `zpow g (a - 1) = zpow g a * g⁻¹`-/
lemma zpow_one_minus: zpow g (a - 1) = zpow g a * g⁻¹ := 
begin
  sorry,
end 

/-- To show: `g ^ a * g ^ b = g ^ (a+b)` -/
lemma zpow_add : zpow g a * zpow g b = zpow g (a+b) :=
begin 
  induction b using int.induction_on,
  rw pow'_zero,
  rw mul_one,
  rw add_zero,
  rw ← add_assoc,
  rw ←  int.coe_nat_succ,
  rw ← npow_zpow,
  rw pow_succ,
  rw ← mul_assoc,
  rw npow_zpow,
  rw b_ᾰ,
  rw zpow_one,
  rw zpow_one_minus,
  rw ← mul_assoc,
  rw b_ᾰ,
  rw ← zpow_one_minus,
  rw add_sub_assoc,
end 

/- 
Since we have proved that  `g ^ a * g ^ b = g ^ (a+b)`, the following lemma
follows directly.
-/
/-- To show: `g^m * g^n = g^n * g^m` -/
lemma pow'_comm: zpow g a * zpow g b = zpow g b * zpow g a :=
begin
  rw zpow_add,
  rw add_comm,
  rw ← zpow_add,
end

-- ending the namespace `mygroup`

/-!
## Theorem: Every cyclic group is abelian.
-/

/-- To show: Every element in a cyclic group commutes. -/
theorem cycl_abel {K : Type} [cyclic_grp K] (x y : K):
x * y = y * x:=
begin
obtain ⟨g, hg⟩ := grp_generator K, -- introducing the generator `g` of `K`
obtain ⟨m, hm⟩ := hg x,
obtain ⟨n, hn⟩ := hg y,
rw hm,
rw hn,
rw pow'_comm,
end

/-
We have expressed `x,y ∈ K` as some power of `g` which is a generator of `K`.
We have shown that `x * y = y * x`
Since `x,y ∈ K` are arbitrary, therefore, every element commutes in `K`.

Let `P` be a cyclic group belonging to the class of cyclic groups called 
`cyclic_grp`, since we know that it satisfies all axioms of a group defined in class
`mygroup`, and every element in `P` commutes, so we will now prove that all cyclic groups
are abelian.

-/

/-- To define `cyclic_groups` which proves that all cyclic groups are abelian: -/
def cyclic_groups (P : Type) [cyclic_grp P] : abel_grp P :=
{ mul_assoc := mul_assoc,
one_mul := one_mul,
mul_one := mul_one,
inv_mul_self := inv_mul_self,
mul_inv_self := mul_inv_self,
mul_com := cycl_abel
}

/-
Since the group `P` in `cyclic_grps` is arbitrary, therefore, every group is abelian.
`cyclic_grp` and `abel_grp` both `extends` `mygroups`, but `abel_grps`
has `mul_com` while `cyclic_grp` has `grp_generator`. We shown that every
element in a `cyclic_grp` can be expressed by `grp_generator` and satifies
`mul_com` in `cycl_abel`.
Hence, we proved that all cyclic groups are abelian.
-/

end cyclic_grp

end mygroup

/-Attempting to fix the bugs-/
#lint 
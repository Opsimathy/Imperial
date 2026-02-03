/-
First of three courseworks in the "Formalising Mathematics 2022" course.
I try to show that disjoint cycles in the symmetric group commute.
-/

import tactic
import group_theory.subgroup.basic


/-
First, I will try to construct the symmetric group
-/

-- These lines of code say X is a finite set (Type).
variables (X : Type) [fintype X]

-- The set of permutations of X are the set of bijections from X to X.
def my_perm (X : Type) := equiv X X

#check my_perm X

-- "Let f and g be permutations of X"
variables (f g : my_perm X) (m n : ℤ)

def my_perm_id : my_perm X := {
  to_fun    := λ x, x,
  inv_fun   := λ x, x,
  left_inv  := begin
    intro x,
    simp,
  end,
  right_inv := begin
    intro x,
    simp,
  end,
}

#check my_perm_id X

/-
Giving my_perm X group structure. 
Inverse and identity "equiv" elements already exist, and we use them to get the group structure.
-/
instance my_symm_grp : group (my_perm X):= {
  mul := λ f g, equiv.trans g f, -- Multiplication in the group is given by composing the two bijections
  one := equiv.refl X, 
  mul_assoc := λ f g h, equiv.trans_assoc h g f,
  -- Associativity of the group follows from associativity of bijections
  one_mul := by {intro a, simp},
  mul_one := by {intro a, simp},
  inv := equiv.symm,
  mul_left_inv := by {intro a, ext x, simp}, -- "simp" failed to simplify before I introduced x
}
-- Do not fully understand why I had to use "by" here and not "begin-end" stuff

@[simp] lemma my_perm_comp : (f * g).to_fun = f.to_fun ∘ g.to_fun  := begin ext x, simp, end


-- Just making sure taking powers made sense
#check f ^ n
#check f ^ (-n)

--Every element in a finite group has to have some power taking it to 1
--This is unused, but justifies my definition of orbit (using ℤ and not ℕ).
lemma my_perm_has_fin_ord : ∀ (f : my_perm X), ∃ (n : ℕ), n ≠ 0 ∧ f ^ n = 1 := by sorry

/-
Plan: 
Define orbit of element in X
Use orbit to define (disjoint) cycle
Prove disjoint cycles commute using orbits of elements
-/

def orbit {X : Type} [fintype X] (f : my_perm X) (x : X) : set X := {y : X | ∃ n : ℤ, (f ^ n).to_fun x = y}

#check orbit

@[simp] lemma in_own_orbit (f : my_perm X) (x : X) : x ∈ (orbit f) x :=
begin
  split, swap, use 0, refl,
end

lemma has_same_orbit (x y : X) (f : my_perm X) : orbit f x = orbit f y ↔ ∃ n : ℤ, (f^n).to_fun x = y :=
begin
  split,
  {
    intro h,
    change y ∈ orbit f x,
    rw h, simp},
  {
    intro h,
    cases h with n h1,
    ext g, split,
    {
      intro h2',
      cases h2' with n2 h2, 
      split, swap,
      exact n2 - n,
      rw [← h1],
      change ((f ^ (n2 - n)).to_fun ∘ (f ^ n).to_fun) x = g,
      rw [← my_perm_comp, ← zpow_add f (n2-n) (n)],
      simpa,
    },
  {
    intro h',
    cases h' with m h,
    rw [← h1] at h,
    split, swap,
    exact m + n,
    rw [zpow_add, my_perm_comp],
    exact h,
  }}
end

namespace orbit

/-
We define an equivalence relation using our definition of orbit
-/
inductive rel {X : Type} [fintype X] (f : my_perm X) : X → X → Prop
| a : ∀ (x y : X) (h : orbit f x = orbit f y), rel x y

lemma rel.refl (f : my_perm X) (x : X): rel f x x := 
begin
apply rel.a, refl
end

lemma rel.symm (f : my_perm X) (x y : X): rel f x y → rel f y x :=
begin
intro h',
cases h' with _ _ h, --Not sure why this statement has 3 arguments
apply rel.a,
apply eq.symm,
exact h
end

lemma rel.trans (f : my_perm X) (x y z : X): rel f x y → rel f y z → rel f x z :=
begin
  intro hxy,
  intro hyz,
  cases hxy with _ _ hxy1,
  cases hyz with _ _ hyz1,
  apply rel.a, rw [hxy1, hyz1]
end

lemma rel.is_equivalence : equivalence (rel f) := 
begin
split, apply rel.refl,
split, apply rel.symm, apply rel.trans
end

end orbit

def size_of_class {X : Type} [fintype X] (f : my_perm X) : X → ℕ := 
λ x, (finset.univ.filter $ λ y, orbit.rel f x = orbit.rel f y).card
-- I get an error here: definition 'size_of_class' is noncomputable, it depends on 'Prop.linear_order'
-- I do not understand noncomputability, so will press on anyway.

variable x : X
#check size_of_class f x

--Unused lemma, although I feel like I might have needed this to prove the next lemma if it wasn't "sorryed"
lemma class_non_empty {X : Type} [fintype X] (f : my_perm X) :
∀ x : X, 1 ≤ size_of_class f x :=
begin
  intro x,
  change 1 ≤ (finset.univ.filter $ λ y, orbit.rel f x = orbit.rel f y).card,
  -- I've got a statement here that says "The equivalence class of any x has cardinality at least 1", 
  -- and I've got the obvious element x in that equivalence class, but I do not know how to proceed.
  sorry,
end

/-
A cycle is a permutation f with only one non-trivial orbit. 
In this definition, I define `is_cycle` as a function taking the permutation f to the statement that there is only one non-trivial orbit.
-/
def is_cyc : (my_perm X) → Prop :=
λ f, ((∃ (x : X), (size_of_class f x) > 1) →  ∀ y : X, (size_of_class f y) > 1 → orbit.rel f x = orbit.rel f y )= true

#check is_cyc
#check is_cyc X x (my_perm_id X)

lemma has_triv_orbit (f : my_perm X) (x : X) : size_of_class f x = 1 ↔ (f.to_fun x = x) :=
begin
  split,
  {
    intro h,
    by_contra h1,
    sorry},
  {
    intro h,
    sorry}
end

-- Defining what it means for cycles to be disjoint
def are_dj_cyc (f g : my_perm X) := ∀ (x : X), (size_of_class f x = 1) ∨ (size_of_class g x = 1)

#check are_dj_cyc X f g

-- Disjoint cycles commute
theorem dj_cyc_comm (h : are_dj_cyc X f g) : f * g = g * f :=
begin
  ext x,
  rw [are_dj_cyc] at h,
  have h' : (∀ (x : X), size_of_class f x = 1 ∨ size_of_class g x = 1), by {exact h},
  specialize h x,
  cases h with h1 h2,
  specialize h' (g.to_fun x),
  {rw [has_triv_orbit] at h1,
  change f.to_fun (g.to_fun x)= g.to_fun (f.to_fun x),
  rw [h1],
  cases h' with h'1 h'2,
    {
      rw [has_triv_orbit] at h'1,
      exact h'1
    },
    {
      rw [has_triv_orbit] at h'2,
      have h3 : g.inv_fun (g.to_fun (g.to_fun x)) = g.inv_fun (g.to_fun x),
      {rw h'2},
      have h4 : g.to_fun x = x,
      {
        simp at h3, exact h3
      },
      rw [h4],
      exact h1,
    },
  },
  {
    rw [has_triv_orbit] at h2,
    change f.to_fun (g.to_fun x)= g.to_fun (f.to_fun x),
    specialize h' (f.to_fun x),
    rw [h2],
    cases h' with h'1 h'2,
    {
      rw [has_triv_orbit] at h'1,
      have h3 : f.inv_fun (f.to_fun (f.to_fun x)) = f.inv_fun (f.to_fun x),
      {rw h'1},
      have h4 : f.to_fun x = x,
      {
        simp at h3, exact h3
      },
      rw [h4],
      exact h2.symm,
    },
    {
      rw [has_triv_orbit] at h'2,
      exact h'2.symm
    }
  }
end
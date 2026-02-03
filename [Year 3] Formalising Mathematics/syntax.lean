import data.set
import tactic.induction
import data.equiv.denumerable
import data.list
import data.list.sigma

namespace type

@[derive(decidable_eq)]
inductive type (gnd : Type) : Type
| Gnd  : gnd → type
| Unit : type
| Prod : type → type → type
| Fun  : type → type → type

notation `|` G `|` := type.Gnd G
notation `unit`   := type.Unit
infixl ` ∏ `:65 := type.Prod
infixr ` ⊃ `:66 := type.Fun

end type

namespace term

open type

/- λ-calculus terms with a locally nameless representation. 

The bound variables are represented by how many abstractions away the 
abstraction that bound the variable is. For example,

λx. x (λy. x y) becomes λ (bvar 0) (λ (bvar 1) (bvar 0))

so we do not need the notion of α-equivalence.

The free variables are represented by names, so we can use any type that
  1) is infinite
  2) has decidable equality (decidable_eq)
  3) has a function where given a finite set of names, generates a fresh name 
     that does not appear in the set.
ℕ is a good candidate but we just assume an arbitrary `fvar` for this 
formalisation.
-/

class fvar (α : Type) :=
[hdec : decidable_eq α]
(fresh : finset α → α)
(hfresh : ∀ S, fresh S ∉ S)

-- Notice that non-finiteness is implied by having the `fresh` function:
instance fvar_is_infinite (α : Type) [fvar α] : infinite α := { 
  not_fintype := begin
    intro hfin,
    haveI := hfin,
    have hfresh := fvar.hfresh (@finset.univ α _),
    have hnfresh := @finset.mem_univ α _ (fvar.fresh finset.univ),
    contradiction
  end
}

-- a constant has some given fixed type
class const (α : Type) (gnd : Type) :=
(type_of : α → type gnd)

@[derive(decidable_eq)]
inductive term (gnd con fv : Type) : Type
| Const : con → term
| Bvar  : ℕ → term
| Fvar  : fv → term
| Unit  : term
| Pair  : term → term → term
| Fst   : term → term
| Snd   : term → term
| Abs   : type gnd → term → term -- The bound variable is typed to ensure each 
                                 -- term has a unique type.
| App   : term → term → term

notation `|` c `|`                := term.Const c
notation `⌈` i `⌉`                := term.Bvar i
notation `⌊` x `⌋`                := term.Fvar x
notation `⟪⟫`                     := term.Unit
notation `⟪` t1 `, ` t2 `⟫`       := term.Pair t1 t2
notation `fst ` t                  := term.Fst t 
notation `snd ` t                  := term.Snd t 
notation `Λ ` A `. ` t             := term.Abs A t
infixl    ` ⬝ `:65                 := term.App

variables {gnd con fv : Type} [fvar fv] [const con gnd]
instance : decidable_eq fv := fvar.hdec

def open_term (u : term gnd con fv) 
: ℕ → term gnd con fv → term gnd con fv
| k |c| := |c|
| k ⌈i⌉ := if k = i then u else ⌈i⌉
| k ⌊x⌋ := ⌊x⌋
| k ⟪⟫  := ⟪⟫
| k ⟪t1, t2⟫ := ⟪open_term k t1, open_term k t2⟫
| k (fst t) := fst (open_term k t)
| k (snd t) := snd (open_term k t)
| k (Λ A. t) := Λ A. (open_term (k+1) t)
| k (t1 ⬝ t2) := (open_term k t1) ⬝ (open_term k t2)

def open_var (x : fv) (n : ℕ) (t : term gnd con fv) := open_term ⌊x⌋ n t

def close_var (x : fv) : ℕ → term gnd con fv → term gnd con fv 
| k |c| := |c|
| k ⌈i⌉ := ⌈i⌉
| k ⌊y⌋ := if x = y then ⌈k⌉ else ⌊y⌋
| k ⟪⟫  := ⟪⟫
| k ⟪t1, t2⟫ := ⟪close_var k t1, close_var k t2⟫
| k (fst t) := fst (close_var k t)
| k (snd t) := snd (close_var k t)
| k (Λ A. t) := Λ A. (close_var (k+1) t)
| k (t1 ⬝ t2) := (close_var k t1) ⬝ (close_var k t2)

def free_vars : term gnd con fv → finset fv
| |c| := ∅
| ⌈i⌉ := ∅
| ⌊y⌋ := {y}
| ⟪⟫  := ∅
| ⟪t1, t2⟫ := free_vars t1 ∪ free_vars t2
| (fst t) := free_vars t
| (snd t) := free_vars t
| (Λ A. t) := free_vars t
| (t1 ⬝ t2) := free_vars t1 ∪ free_vars t2

lemma free_vars_open_term (t1 t2 : term gnd con fv) (n : ℕ)
: free_vars (open_term t2 n t1) = free_vars t1 ∪ free_vars t2 ∨
  free_vars (open_term t2 n t1) = free_vars t1 := 
begin
  induction t1 generalizing n,
  case term.term.Const : t1 n
  { right, simp [free_vars, open_term] },
  case term.term.Bvar : t1 n
  { simp only [free_vars, open_term, finset.empty_union], split_ifs,
    { left, refl },
    { right, unfold free_vars }
  },
  case term.term.Fvar : t1 n
  { right, simp [free_vars, open_term] },
  case term.term.Unit : n
  { right, simp [free_vars, open_term] },
  case term.term.Pair : t1l t1r ihl ihr n
  { simp only [free_vars, open_term, finset.union_assoc],
    specialize ihl n, specialize ihr n,
    with_cases { cases ihl; cases ihr; rw [ihl, ihr] },
    case or.inl or.inl
    { left,
      rw [←finset.union_assoc _ (free_vars t1r) (free_vars t2)],
      rw [finset.union_assoc _ (free_vars t2) (free_vars t1r)],
      rw [finset.union_comm (free_vars t2) (free_vars t1r)],
      simp only [finset.union_assoc, finset.union_right_idem],
    },
    case or.inl or.inr
    { left, ac_refl },
    case or.inr or.inl
    { left, ac_refl },
    case or.inr or.inr
    { right, ac_refl }     
  },
  case term.term.Fst : t1 ih n
  { simp only [free_vars, open_term], exact ih n },
  case term.term.Snd : t1 ih n
  { simp only [free_vars, open_term], exact ih n },
  case term.term.Abs : A t1 ih n
  { simp only [free_vars, open_term], exact ih (n + 1) },
  case term.term.App : t1l t1r ihl ihr n
  { simp only [free_vars, open_term, finset.union_assoc],
    specialize ihl n, specialize ihr n,
    with_cases { cases ihl; cases ihr; rw [ihl, ihr] },
    case or.inl or.inl
    { left,
      rw [←finset.union_assoc _ (free_vars t1r) (free_vars t2)],
      rw [finset.union_assoc _ (free_vars t2) (free_vars t1r)],
      rw [finset.union_comm (free_vars t2) (free_vars t1r)],
      simp only [finset.union_assoc, finset.union_right_idem],
    },
    case or.inl or.inr
    { left, ac_refl },
    case or.inr or.inl
    { left, ac_refl },
    case or.inr or.inr
    { right, ac_refl }     
  }
end

lemma free_vars_open_term' (t1 t2 : term gnd con fv) (n : ℕ)
: free_vars (open_term t2 n t1) ⊆ free_vars t1 ∪ free_vars t2 :=
begin
  cases free_vars_open_term t1 t2 n,
  { rw h, simp },
  { rw h, exact (free_vars t1).subset_union_left (free_vars t2) }
end

lemma free_vars_open_var (t1 : term gnd con fv) (x : fv) (n : ℕ)
: free_vars (open_var x n t1) = free_vars t1 ∪ {x} ∨
  free_vars (open_var x n t1) = free_vars t1 :=
free_vars_open_term t1 ⌊x⌋ n

notation x ` # ` t := x ∉ free_vars t
abbreviation closed (t : term gnd con fv) := free_vars t = ∅

inductive locally_closed : finset fv → term gnd con fv → Type
| Const : ∀ {Γ c},
----------------------
locally_closed Γ (|c|)

| Fvar : ∀ {Γ x},
x ∈ Γ
----------------------
→ locally_closed Γ ⌊x⌋

| Unit : ∀ {Γ},
-------------------
locally_closed Γ ⟪⟫

| Pair : ∀ {Γ t1 t2}, 
locally_closed Γ t1 → locally_closed Γ t2
-----------------------------------------
→ locally_closed Γ ⟪t1, t2⟫

| Fst : ∀ {Γ t},
locally_closed Γ t
--------------------------
→ locally_closed Γ (fst t)

| Snd : ∀ {Γ t},
locally_closed Γ t
------------------------
→ locally_closed Γ (snd t)

-- The locally nameless paper says this should be 
-- ∃ L : finset fv, ∀ x ∉ L, locally_closed (open_var x 0 t)
-- but in Lean3 constructor arguments can't be inside another inductive type
-- so I have to use a Γ to explicitly track the abstracted variables, which
-- makes the
-- representation even more complicated... 
| Abs : ∀ {Γ A t},
(∀ x ∉ free_vars t ∪ Γ, locally_closed (insert x Γ) (open_var x 0 t))
-------------------------------------------------------------------------
→ locally_closed Γ (Λ A. t)

| App : ∀ {Γ t1 t2},
locally_closed Γ t1 → locally_closed Γ t2
-------------------------------------
→ locally_closed Γ (t1 ⬝ t2)

def subst (u : term gnd con fv) (x : fv)
: term gnd con fv → term gnd con fv
| ⌈i⌉ := ⌈i⌉
| |c| := |c|
| ⌊y⌋ := if x = y then u else ⌊y⌋
| ⟪⟫  := ⟪⟫
| ⟪t1, t2⟫ := ⟪subst t1, subst t2⟫
| (fst t) := fst (subst t)
| (snd t) := snd (subst t)
| (Λ A. t) := Λ A. (subst t)
| (t1 ⬝ t2) := (subst t1) ⬝ (subst t2)

theorem open_term_eq_subst_of_open_var (t u : term gnd con fv) (x : fv) (n : ℕ)
(hx : x # t) : open_term u n t = subst u x (open_var x n t) :=
begin
  induction' t generalizing n,
  case term.term.Const : c
  { simp only [open_term, open_var, subst] },
  case term.term.Bvar : n
  { simp only [open_term, open_var], 
    split_ifs,
    { simp [subst], },
    { simp [subst], }
  },
  case term.term.Fvar : x_1
  { simp only [open_term, open_var, subst],
    split_ifs,
    { simp only [free_vars, finset.mem_singleton] at hx, contradiction },
    { refl } },
  case term.term.Unit
  { simp only [open_term, open_var, subst] },
  case term.term.Pair : t1 t2 ih1 ih2
  { simp only [free_vars, not_or_distrib, finset.mem_union] at hx,
    specialize ih1 n hx.left,
    specialize ih2 n hx.right,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih1 ih2,
    exact ⟨ih1, ih2⟩ 
  },
  case term.term.Fst : t ih
  { simp only [free_vars] at hx,
    specialize ih n hx,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih,
    exact ih
  },
  case term.term.Snd : t ih
  { simp only [free_vars] at hx,
    specialize ih n hx,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih,
    exact ih
  },
  case term.term.Abs : A t ih
  { simp only [free_vars] at hx,
    specialize ih (n + 1) hx,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih,
    exact ⟨rfl, ih⟩ 
  },
  case term.term.App : t1 t2 ih1 ih2
  { simp only [free_vars, not_or_distrib, finset.mem_union] at hx,
    specialize ih1 n hx.left,
    specialize ih2 n hx.right,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih1 ih2,
    exact ⟨ih1, ih2⟩
  }
end

end term